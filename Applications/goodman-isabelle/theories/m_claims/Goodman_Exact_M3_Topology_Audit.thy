theory Goodman_Exact_M3_Topology_Audit
  imports Goodman_Exact_M3_Topology
begin

section \<open>M3 product-topology proof objects and exact statements\<close>

ML \<open>
local
  val names = ["gi_M3_cylinder_self", "gi_M3_cylinder_nonempty", "gi_M3_product_meager_mono",
    "gi_M3_fresh_cone_point", "gi_M3_necessary_cone_nowhere_dense", "gi_M3_word_enum_surjective",
    "gi_M3_top_view_class_is_product_meager", "gi_exact_M3_fun_prime_class_is_product_meager",
    "gi_native_M3_fun_prime_class_is_product_meager", "gi_native_M3_free_generator_class_is_product_meager"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-m3-topology: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-m3-topology: residual obligations in " ^ name)
  val report = "EXACT-M3-TOPOLOGY-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: explicit finite-cylinder product topology on propositions; exact closed-logical fun-prime and native free-generator classes are meager by proved extreme-view coverage. No arbitrary-stock theorem, particular glued-r identification, or PP model. HOL-ZF exact instantiation retained.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m3-topology-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m3-topology-statements.txt")) [XML.Text statements]
in end
\<close>

end
