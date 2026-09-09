theory Bacon_Book_Simultaneous_Substitution_Syntax
  imports Bacon_Book_Constant_Substitution_Syntax
begin

section \<open>Finite simultaneous replacement with typed keys\<close>

text \<open>
  A[θ] replaces the selected free variables and nonlogical constants
  simultaneously, with type-matching payloads and no variable capture.
  Source: Bacon, Definition 5.2, p.99, motivates the typed, capture-free
  replacement discipline. This leaf supplies a finite simultaneous syntax;
  it does not identify simultaneous replacement with a sequential execution
  of individual replacements or prove its admissibility in a logic.

  Representation. θ is a finite list of key–payload pairs; map_of gives
  its first-match lookup if a key is repeated. Variable keys and constant
  keys are distinct and carry types. A variable n uses the fixed type G(n).
  Beneath λn, only the key for that variable is disabled. Constant keys
  remain active. A selected payload is returned unchanged, not recursively
  transformed. The total operation may capture variables; free-for below
  separately tests every payload inserted under each binder.
\<close>

datatype 'c book_subst_key = BSVar nat otype | BSConst 'c otype

fun book_subst_key_type :: "'c book_subst_key \<Rightarrow> otype" where
  "book_subst_key_type (BSVar n \<sigma>) = \<sigma>"
| "book_subst_key_type (BSConst c \<sigma>) = \<sigma>"

type_synonym ('c,'l) book_subst_table =
  "('c book_subst_key \<times> ('c,'l) named_term) list"

definition book_subst_disable ::
  "'c book_subst_key \<Rightarrow> ('c,'l) book_subst_table \<Rightarrow> ('c,'l) book_subst_table" where
  "book_subst_disable k \<theta> = filter (\<lambda>p. fst p \<noteq> k) \<theta>"

fun book_term_keys :: "sgcontext \<Rightarrow> ('c,'l) named_term \<Rightarrow> 'c book_subst_key set" where
  "book_term_keys G (NVar n) = {BSVar n (G n)}"
| "book_term_keys G (NConst c \<sigma>) = {BSConst c \<sigma>}"
| "book_term_keys G (NLogical l) = {}"
| "book_term_keys G (NApp F A) = book_term_keys G F \<union> book_term_keys G A"
| "book_term_keys G (NLam n A) = book_term_keys G A - {BSVar n (G n)}"

fun book_simult_subst ::
  "sgcontext \<Rightarrow> ('c,'l) book_subst_table \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term" where
  "book_simult_subst G \<theta> (NVar n) =
    (case map_of \<theta> (BSVar n (G n)) of None \<Rightarrow> NVar n | Some B \<Rightarrow> B)"
| "book_simult_subst G \<theta> (NConst c \<sigma>) =
    (case map_of \<theta> (BSConst c \<sigma>) of None \<Rightarrow> NConst c \<sigma> | Some B \<Rightarrow> B)"
| "book_simult_subst G \<theta> (NLogical l) = NLogical l"
| "book_simult_subst G \<theta> (NApp F A) =
    NApp (book_simult_subst G \<theta> F) (book_simult_subst G \<theta> A)"
| "book_simult_subst G \<theta> (NLam n A) =
    NLam n (book_simult_subst G (book_subst_disable (BSVar n (G n)) \<theta>) A)"

fun book_simult_free_for ::
  "sgcontext \<Rightarrow> ('c,'l) book_subst_table \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  "book_simult_free_for G \<theta> (NVar n) = True"
| "book_simult_free_for G \<theta> (NConst c \<sigma>) = True"
| "book_simult_free_for G \<theta> (NLogical l) = True"
| "book_simult_free_for G \<theta> (NApp F A) =
    (book_simult_free_for G \<theta> F \<and> book_simult_free_for G \<theta> A)"
| "book_simult_free_for G \<theta> (NLam n A) =
    (book_simult_free_for G (book_subst_disable (BSVar n (G n)) \<theta>) A \<and>
     (\<forall>k \<in> book_term_keys G A. \<forall>B.
       map_of (book_subst_disable (BSVar n (G n)) \<theta>) k = Some B \<longrightarrow> n \<notin> named_fv B))"

definition book_subst_table_typed ::
  "('l \<Rightarrow> otype) \<Rightarrow> sgcontext \<Rightarrow> ('c,'l) book_subst_table \<Rightarrow> bool" where
  "book_subst_table_typed L G \<theta> \<longleftrightarrow>
    (\<forall>k B. map_of \<theta> k = Some B \<longrightarrow> has_ntype L G B (book_subst_key_type k))"

section \<open>Finite occurrence sets and effective lookup\<close>

lemma book_term_keys_finite: "finite (book_term_keys G A)"
  by (induction A) simp_all

lemma book_term_keys_variable:
  "BSVar n \<sigma> \<in> book_term_keys G A \<longleftrightarrow> \<sigma> = G n \<and> n \<in> named_fv A"
  by (induction A) auto

lemma book_term_keys_constant:
  "BSConst c \<sigma> \<in> book_term_keys G A \<longleftrightarrow> book_const_occurs c \<sigma> A"
  by (induction A) auto

lemma book_subst_lookup_disable:
  "map_of (book_subst_disable k \<theta>) j = (if j = k then None else map_of \<theta> j)"
  unfolding book_subst_disable_def
  by (induction \<theta>) (auto split: prod.splits if_splits)

lemma book_subst_disable_variable:
  "map_of (book_subst_disable (BSVar n (G n)) \<theta>) (BSVar n (G n)) = None"
  by (simp add: book_subst_lookup_disable)

lemma book_subst_disable_constant:
  "map_of (book_subst_disable (BSVar n (G n)) \<theta>) (BSConst c \<sigma>) = map_of \<theta> (BSConst c \<sigma>)"
  by (simp add: book_subst_lookup_disable)

lemma book_subst_table_keys_finite: "finite (set (map fst \<theta>))"
  by (rule finite_set)

lemma book_subst_lookup_member:
  "map_of \<theta> k = Some B \<Longrightarrow> (k,B) \<in> set \<theta>"
  by (induction \<theta>) (auto split: prod.splits if_splits)

lemma book_subst_effective_keys_finite: "finite {k. \<exists>B. map_of \<theta> k = Some B}"
proof -
  have inclusion: "{k. \<exists>B. map_of \<theta> k = Some B} \<subseteq> set (map fst \<theta>)"
  proof
    fix k
    assume member: "k \<in> {k. \<exists>B. map_of \<theta> k = Some B}"
    obtain B where found: "map_of \<theta> k = Some B" using member by blast
    have pair_member: "(k,B) \<in> set \<theta>" by (rule book_subst_lookup_member[OF found])
    have projected: "fst (k,B) \<in> fst ` set \<theta>" by (rule imageI[OF pair_member])
    show "k \<in> set (map fst \<theta>)" using projected by simp
  qed
  show ?thesis by (rule finite_subset[OF inclusion book_subst_table_keys_finite])
qed

lemma book_subst_table_typed_lookup:
  assumes typed: "book_subst_table_typed L G \<theta>" and found: "map_of \<theta> k = Some B"
  shows "has_ntype L G B (book_subst_key_type k)"
  using typed found unfolding book_subst_table_typed_def by blast

lemma book_subst_table_typed_disable:
  assumes typed: "book_subst_table_typed L G \<theta>"
  shows "book_subst_table_typed L G (book_subst_disable k \<theta>)"
proof (unfold book_subst_table_typed_def, intro allI impI)
  fix j B
  assume found: "map_of (book_subst_disable k \<theta>) j = Some B"
  have original: "map_of \<theta> j = Some B"
    using found by (auto simp only: book_subst_lookup_disable split: if_splits)
  show "has_ntype L G B (book_subst_key_type j)"
    by (rule book_subst_table_typed_lookup[OF typed original])
qed

lemma book_simult_subst_empty: "book_simult_subst G [] A = A"
  by (induction A) (simp_all add: book_subst_disable_def)

lemma book_simult_free_for_empty: "book_simult_free_for G [] A"
  by (induction A) (simp_all add: book_subst_disable_def)

section \<open>Typing of raw simultaneous replacement\<close>

text \<open>
  If A:τ and every effective payload has its key's type, then A[θ]:τ.
  Fixed variable types make this true even for a capturing raw replacement.
  The theorem therefore does not dispense with book_simult_free_for.
\<close>

theorem book_simult_subst_type:
  assumes body: "has_ntype L G A \<tau>" and table: "book_subst_table_typed L G \<theta>"
  shows "has_ntype L G (book_simult_subst G \<theta> A) \<tau>"
  using body table
proof (induction A arbitrary: \<tau> \<theta>)
  case (NVar n)
  have result_type: "\<tau> = G n" using NVar.prems(1) by (simp only: named_var_type_iff)
  show ?case
  proof (cases "map_of \<theta> (BSVar n (G n))")
    case None
    show ?thesis by (simp only: book_simult_subst.simps None option.simps; rule NVar.prems(1))
  next
    case (Some B)
    have payload: "has_ntype L G B (G n)"
      using book_subst_table_typed_lookup[OF NVar.prems(2) Some] by (simp only: book_subst_key_type.simps)
    show ?thesis by (simp only: book_simult_subst.simps Some option.simps result_type; rule payload)
  qed
next
  case (NConst c \<sigma>)
  have result_type: "\<tau> = \<sigma>" using NConst.prems(1) by (simp only: named_const_type_iff)
  show ?case
  proof (cases "map_of \<theta> (BSConst c \<sigma>)")
    case None
    show ?thesis by (simp only: book_simult_subst.simps None option.simps; rule NConst.prems(1))
  next
    case (Some B)
    have payload: "has_ntype L G B \<sigma>"
      using book_subst_table_typed_lookup[OF NConst.prems(2) Some] by (simp only: book_subst_key_type.simps)
    show ?thesis by (simp only: book_simult_subst.simps Some option.simps result_type; rule payload)
  qed
next
  case (NLogical l)
  show ?case by (simp only: book_simult_subst.simps; rule NLogical.prems(1))
next
  case (NApp F A)
  obtain \<sigma> where ft: "has_ntype L G F (Arr \<sigma> \<tau>)" and at: "has_ntype L G A \<sigma>"
    by (rule named_app_type_obtain[OF NApp.prems(1)]; rule that; assumption)
  have fs: "has_ntype L G (book_simult_subst G \<theta> F) (Arr \<sigma> \<tau>)"
    by (rule NApp.IH(1)[OF ft NApp.prems(2)])
  have asub: "has_ntype L G (book_simult_subst G \<theta> A) \<sigma>"
    by (rule NApp.IH(2)[OF at NApp.prems(2)])
  show ?case unfolding book_simult_subst.simps by (rule has_ntype.App[OF fs asub])
next
  case (NLam n A)
  obtain \<rho> where result_type: "\<tau> = Arr (G n) \<rho>" and at: "has_ntype L G A \<rho>"
    by (rule named_lam_type_obtain[OF NLam.prems(1)]; rule that; assumption)
  have restricted: "book_subst_table_typed L G (book_subst_disable (BSVar n (G n)) \<theta>)"
    by (rule book_subst_table_typed_disable[OF NLam.prems(2)])
  have asub: "has_ntype L G (book_simult_subst G (book_subst_disable (BSVar n (G n)) \<theta>) A) \<rho>"
    by (rule NLam.IH[OF at restricted])
  show ?case unfolding book_simult_subst.simps result_type by (rule has_ntype.Lam[OF asub])
qed

end
