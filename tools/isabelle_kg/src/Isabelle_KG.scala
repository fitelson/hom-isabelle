package isabelle

import java.nio.file.{Files, Path as JPath, Paths}
import java.time.Instant
import scala.collection.mutable
import scala.jdk.CollectionConverters.*


object Isabelle_KG {
  private val source_line_starts = mutable.HashMap.empty[String, Vector[Int]]

  final case class Node(
    id: String,
    kind: String,
    name: String,
    short_name: String,
    theory: String = "",
    session: String = "",
    file: String = "",
    line: Int = 0,
    statement: String = "",
    typ: String = "",
    external: Boolean = false
  ) {
    def json: JSON.Object.T =
      JSON.Object(
        "id" -> id,
        "kind" -> kind,
        "name" -> name,
        "short_name" -> short_name,
        "theory" -> theory,
        "session" -> session,
        "file" -> file,
        "line" -> line,
        "statement" -> statement,
        "type" -> typ,
        "external" -> external)
  }

  final case class Edge(
    source: String,
    target: String,
    kind: String,
    theory: String = ""
  ) {
    def json: JSON.Object.T =
      JSON.Object(
        "source" -> source,
        "target" -> target,
        "kind" -> kind,
        "theory" -> theory)
  }

  private def short_name(name: String): String =
    name.split('.').lastOption.getOrElse(name)

  private def trim_statement(s: String, limit: Int = 4000): String =
    if (s.length <= limit) s else s.take(limit) + "..."

  private def node_id(kind: String, name: String): String =
    kind + ":" + name

  private def theorem_id(name: String): String = node_id("theorem", name)
  private def constant_id(name: String): String = node_id("constant", name)
  private def type_id(name: String): String = node_id("type", name)
  private def class_id(name: String): String = node_id("class", name)
  private def locale_id(name: String): String = node_id("locale", name)
  private def theory_id(name: String): String = node_id("theory", name)
  private def session_id(name: String): String = node_id("session", name)

  private def typ_names(typ: Term.Typ): Set[String] =
    typ match {
      case Term.Type(name, args) => args.foldLeft(Set(name))(_ ++ typ_names(_))
      case Term.TFree(_, sort) => sort.toSet
      case Term.TVar(_, sort) => sort.toSet
    }

  private def term_names(term: Term.Term): (Set[String], Set[String], Set[String]) = {
    def add_typ(typ: Term.Typ, acc: (Set[String], Set[String], Set[String])) =
      (acc._1, acc._2 ++ typ_names(typ), acc._3)

    term match {
      case Term.Const(name, typargs) =>
        (Set(name), typargs.flatMap(typ_names).toSet, Set.empty)
      case Term.Free(_, typ) => add_typ(typ, (Set.empty, Set.empty, Set.empty))
      case Term.Var(_, typ) => add_typ(typ, (Set.empty, Set.empty, Set.empty))
      case Term.Bound(_) => (Set.empty, Set.empty, Set.empty)
      case Term.Abs(_, typ, body) =>
        val body_names = term_names(body)
        add_typ(typ, body_names)
      case Term.App(fun, arg) =>
        val a = term_names(fun)
        val b = term_names(arg)
        (a._1 ++ b._1, a._2 ++ b._2, a._3 ++ b._3)
      case Term.OFCLASS(typ, cls) =>
        (Set.empty, typ_names(typ), Set(cls))
    }
  }

  private def project_theory_files(root: JPath): Map[String, String] = {
    val stream = Files.walk(root)
    try {
      stream.iterator.asScala
        .filter(path => Files.isRegularFile(path))
        .filter(path => path.getFileName.toString.endsWith(".thy"))
        .filterNot(path => path.toString.contains("/quarantine/"))
        .filterNot(path => path.toString.contains("/.git/"))
        .map { path =>
          val base = path.getFileName.toString.stripSuffix(".thy")
          base -> path.toAbsolutePath.normalize.toString
        }
        .toList
        .groupBy(_._1)
        .collect { case (base, List((_, file))) => base -> file }
    }
    finally stream.close()
  }

  private def entity_file(
    entity_file: String,
    theory_file: String,
    root: JPath
  ): String = {
    def normalize(file: String): Option[String] =
      if (file.isEmpty) None
      else {
        val path0 = Paths.get(file)
        val path = if (path0.isAbsolute) path0 else root.resolve(path0)
        Some(path.toAbsolutePath.normalize.toString)
      }

    normalize(entity_file)
      .filter(file => Files.exists(Paths.get(file)))
      .orElse(normalize(theory_file))
      .getOrElse(entity_file)
  }

  private def line_from_offset(file: String, offset: Int): Int = {
    if (file.isEmpty || offset < 0) 0
    else {
      val starts =
        source_line_starts.getOrElseUpdate(
          file, {
            val path = Paths.get(file)
            if (!Files.exists(path)) Vector.empty
            else {
              val result = mutable.ArrayBuffer(0)
              var symbol_offset = 0
              Symbol.explode(Files.readString(path)).foreach { symbol =>
                symbol_offset += 1
                if (symbol == "\n") result += symbol_offset
              }
              result.toVector
            }
          })

      if (starts.isEmpty) 0
      else {
        var low = 0
        var high = starts.length
        while (low < high) {
          val middle = low + (high - low) / 2
          if (starts(middle) <= offset) low = middle + 1
          else high = middle
        }
        low
      }
    }
  }

  private def entity_line(pos: Position.T, file: String): Int =
    Position.Line.unapply(pos)
      .orElse(Position.Offset.unapply(pos).map(offset => line_from_offset(file, offset)))
      .getOrElse(0)

  private def add_term_edges(
    source: String,
    term: Term.Term,
    theory: String,
    edges: mutable.LinkedHashSet[Edge]
  ): Unit = {
    val (consts, types, classes) = term_names(term)
    consts.foreach(name => edges += Edge(source, constant_id(name), "USES_CONSTANT", theory))
    types.foreach(name => edges += Edge(source, type_id(name), "USES_TYPE", theory))
    classes.foreach(name => edges += Edge(source, class_id(name), "USES_CLASS", theory))
  }

  private def add_entity[A <: Export_Theory.Content[A]](
    entity: Export_Theory.Entity[A],
    kind: String,
    theory: String,
    session: String,
    theory_file: String,
    root: JPath,
    statement: String = "",
    typ: String = ""
  ): Node = {
    val name = entity.name
    val file = entity_file(entity.file, theory_file, root)
    Node(
      id = node_id(kind, name),
      kind = kind,
      name = name,
      short_name = short_name(name),
      theory = theory,
      session = session,
      file = file,
      line = entity_line(entity.pos, file),
      statement = trim_statement(statement),
      typ = trim_statement(typ))
  }

  private def placeholder(id: String): Node = {
    val split = id.indexOf(':')
    val kind = if (split < 0) "unknown" else id.substring(0, split)
    val name = if (split < 0) id else id.substring(split + 1)
    Node(
      id = id,
      kind = kind,
      name = name,
      short_name = short_name(name),
      external = true)
  }

  def build(
    root: JPath,
    output: JPath,
    sessions: List[String],
    options: Options
  ): Unit = {
    val project_files = project_theory_files(root)
    val nodes = mutable.LinkedHashMap.empty[String, Node]
    val edges = mutable.LinkedHashSet.empty[Edge]
    val theory_session = mutable.LinkedHashMap.empty[String, String]
    val store = Store(options)

    sessions.foreach { session =>
      nodes.getOrElseUpdate(
        session_id(session),
        Node(session_id(session), "session", session, short_name(session)))

      using(Export.open_session_context0(store, session)) { session_context =>
        val names = session_context.theory_names(session = session)
        names.foreach { theory_name =>
          val base = short_name(theory_name)
          project_files.get(base).foreach { source_file =>
            val theory_context = session_context.theory(theory_name)
            val theory = Export_Theory.read_theory(theory_context)
            theory_session.getOrElseUpdate(theory_name, session)

            nodes.getOrElseUpdate(
              theory_id(theory_name),
              Node(
                theory_id(theory_name),
                "theory",
                theory_name,
                base,
                theory = theory_name,
                session = session,
                file = source_file,
                line = 1))

            edges += Edge(session_id(session), theory_id(theory_name), "CONTAINS_THEORY", theory_name)
            theory.parents.foreach { parent =>
              edges += Edge(theory_id(theory_name), theory_id(parent), "IMPORTS", theory_name)
            }

            theory.types.foreach { entity =>
              val content = entity.content
              val node = add_entity(
                entity, "type", theory_name, session, source_file, root,
                statement = content.map(_.args.mkString("[", ",", "]")).getOrElse(""))
              nodes.update(node.id, node)
              edges += Edge(theory_id(theory_name), node.id, "DECLARES", theory_name)
              content.flatMap(_.abbrev).foreach { abbrev =>
                typ_names(abbrev).foreach { name =>
                  edges += Edge(node.id, type_id(name), "USES_TYPE", theory_name)
                }
              }
            }

            theory.consts.foreach { entity =>
              val content = entity.content
              val node = add_entity(
                entity, "constant", theory_name, session, source_file, root,
                statement = content.flatMap(_.abbrev).map(_.toString).getOrElse(""),
                typ = content.map(_.typ.toString).getOrElse(""))
              nodes.update(node.id, node)
              edges += Edge(theory_id(theory_name), node.id, "DECLARES", theory_name)
              content.foreach { const =>
                typ_names(const.typ).foreach { name =>
                  edges += Edge(node.id, type_id(name), "USES_TYPE", theory_name)
                }
                const.abbrev.foreach(add_term_edges(node.id, _, theory_name, edges))
              }
            }

            theory.axioms.foreach { entity =>
              val term = entity.content.map(_.prop.term)
              val node = add_entity(
                entity, "axiom", theory_name, session, source_file, root,
                statement = term.map(_.toString).getOrElse(""))
              nodes.update(node.id, node)
              edges += Edge(theory_id(theory_name), node.id, "DECLARES", theory_name)
              term.foreach(add_term_edges(node.id, _, theory_name, edges))
            }

            theory.thms.foreach { entity =>
              val content = entity.content
              val term = content.map(_.prop.term)
              val node = add_entity(
                entity, "theorem", theory_name, session, source_file, root,
                statement = term.map(_.toString).getOrElse(""))
              nodes.update(node.id, node)
              edges += Edge(theory_id(theory_name), node.id, "DECLARES", theory_name)
              term.foreach(add_term_edges(node.id, _, theory_name, edges))
              content.foreach { thm =>
                thm.deps.foreach { dep =>
                  if (!dep.is_empty)
                    edges += Edge(node.id, theorem_id(dep.print), "DEPENDS_ON", theory_name)
                }
              }
            }

            theory.classes.foreach { entity =>
              val node = add_entity(
                entity, "class", theory_name, session, source_file, root,
                statement = entity.content.map(_.axioms.map(_.term).mkString("; ")).getOrElse(""))
              nodes.update(node.id, node)
              edges += Edge(theory_id(theory_name), node.id, "DECLARES", theory_name)
              entity.content.foreach { cls =>
                cls.axioms.foreach(prop => add_term_edges(node.id, prop.term, theory_name, edges))
              }
            }

            theory.locales.foreach { entity =>
              val node = add_entity(
                entity, "locale", theory_name, session, source_file, root,
                statement = entity.content.map(_.axioms.map(_.term).mkString("; ")).getOrElse(""))
              nodes.update(node.id, node)
              edges += Edge(theory_id(theory_name), node.id, "DECLARES", theory_name)
              entity.content.foreach { locale =>
                locale.axioms.foreach(prop => add_term_edges(node.id, prop.term, theory_name, edges))
              }
            }

            theory.locale_dependencies.foreach { entity =>
              entity.content.foreach { dep =>
                edges += Edge(locale_id(dep.target), locale_id(dep.source),
                  "LOCALE_DEPENDS_ON", theory_name)
              }
            }

            theory.constdefs.foreach { constdef =>
              edges += Edge(constant_id(constdef.name), node_id("axiom", constdef.axiom_name),
                "DEFINED_BY", theory_name)
            }

            theory.typedefs.foreach { typedef =>
              edges += Edge(type_id(typedef.name), node_id("axiom", typedef.axiom_name),
                "DEFINED_BY", theory_name)
              edges += Edge(type_id(typedef.name), constant_id(typedef.rep_name),
                "HAS_REPRESENTATION", theory_name)
              edges += Edge(type_id(typedef.name), constant_id(typedef.abs_name),
                "HAS_ABSTRACTION", theory_name)
            }

            theory.datatypes.foreach { datatype =>
              datatype.constructors.foreach { case (constructor, _) =>
                constructor match {
                  case Term.Const(name, _) =>
                    edges += Edge(type_id(datatype.name), constant_id(name),
                      "HAS_CONSTRUCTOR", theory_name)
                  case _ =>
                }
              }
            }

            theory.spec_rules.foreach { rule =>
              val id = node_id("spec_rule", theory_name + "." + rule.name)
              val file = Position.File.unapply(rule.pos).getOrElse(source_file)
              val normalized_file = entity_file(file, source_file, root)
              val node = Node(
                id, "spec_rule", rule.name, short_name(rule.name),
                theory = theory_name,
                session = session,
                file = normalized_file,
                line = entity_line(rule.pos, normalized_file),
                statement = trim_statement(rule.rules.mkString("; ")))
              nodes.update(id, node)
              edges += Edge(theory_id(theory_name), id, "DECLARES", theory_name)
              rule.terms.foreach { case (term, _) =>
                add_term_edges(id, term, theory_name, edges)
              }
              rule.rules.foreach(add_term_edges(id, _, theory_name, edges))
            }
          }
        }
      }
    }

    edges.foreach { edge =>
      if (!nodes.contains(edge.source)) nodes.update(edge.source, placeholder(edge.source))
      if (!nodes.contains(edge.target)) nodes.update(edge.target, placeholder(edge.target))
    }

    val kind_counts =
      nodes.values.groupBy(_.kind).view.mapValues(_.size).toMap
    val edge_counts =
      edges.groupBy(_.kind).view.mapValues(_.size).toMap
    val project_node_count = nodes.values.count(!_.external)

    val graph =
      JSON.Object(
        "schema" -> "isabelle-kg-v1",
        "generated_at" -> Instant.now.toString,
        "isabelle_version" -> Isabelle_System.getenv("ISABELLE_IDENTIFIER"),
        "project_root" -> root.toAbsolutePath.normalize.toString,
        "sessions" -> sessions,
        "stats" -> JSON.Object(
          "nodes" -> nodes.size,
          "edges" -> edges.size,
          "project_nodes" -> project_node_count,
          "external_boundary_nodes" -> (nodes.size - project_node_count),
          "node_kinds" -> kind_counts,
          "edge_kinds" -> edge_counts),
        "nodes" -> nodes.values.toList.map(_.json),
        "edges" -> edges.toList.map(_.json))

    Files.createDirectories(output.getParent)
    Files.writeString(output, JSON.Format(graph))

    val summary =
      "Isabelle knowledge graph\n" +
      "  project theories: " + nodes.values.count(n => n.kind == "theory" && !n.external) + "\n" +
      "  project entities: " + project_node_count + "\n" +
      "  external boundary nodes: " + (nodes.size - project_node_count) + "\n" +
      "  total nodes: " + nodes.size + "\n" +
      "  total edges: " + edges.size + "\n" +
      "  output: " + output.toAbsolutePath.normalize + "\n"
    Console.out.print(summary)
  }

  def main(args: Array[String]): Unit = {
    Command_Line.tool {
      if (args.length < 3) {
        error(
          "Usage: Isabelle_KG PROJECT_ROOT OUTPUT_JSON SESSION [SESSION ...]")
      }
      val root = Paths.get(args(0)).toAbsolutePath.normalize
      val output = Paths.get(args(1)).toAbsolutePath.normalize
      val sessions = args.drop(2).toList
      build(root, output, sessions, Options.init())
    }
  }
}
