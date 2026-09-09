theory Bacon_Book_Full_General_Language
  imports Bacon_Book_General_Lambda_Language
begin

section \<open>Full-language application components at their uniquely determined types\<close>

lemma book_full_application_head_language:
  assumes whole: "book_in_language L \<Lambda> \<Sigma> G (NApp F A) \<tau>"
    and head_type: "has_ntype L G F (Arr \<sigma> \<tau>)"
  shows "book_in_language L \<Lambda> \<Sigma> G F (Arr \<sigma> \<tau>)"
proof -
  obtain \<rho> where head: "book_in_language L \<Lambda> \<Sigma> G F (Arr \<rho> \<tau>)"
    and argument: "book_in_language L \<Lambda> \<Sigma> G A \<rho>"
    by (rule book_language_App_obtain[OF whole]; rule that; assumption)
  have equality: "Arr \<rho> \<tau> = Arr \<sigma> \<tau>"
    by (rule named_type_unique[OF book_language_type[OF head] head_type])
  have types: "\<rho> = \<sigma>" using equality by simp
  show ?thesis using head by (simp only: types)
qed

lemma book_full_application_argument_language:
  assumes whole: "book_in_language L \<Lambda> \<Sigma> G (NApp F A) \<tau>"
    and argument_type: "has_ntype L G A \<sigma>"
  shows "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
proof -
  obtain \<rho> where head: "book_in_language L \<Lambda> \<Sigma> G F (Arr \<rho> \<tau>)"
    and argument: "book_in_language L \<Lambda> \<Sigma> G A \<rho>"
    by (rule book_language_App_obtain[OF whole]; rule that; assumption)
  have types: "\<rho> = \<sigma>"
    by (rule named_type_unique[OF book_language_type[OF argument] argument_type])
  show ?thesis using argument by (simp only: types)
qed

section \<open>The full typed language satisfies Definition 9.1\<close>

text \<open>
  Set 𝒥τ={A: A belongs to the full typed language at τ}. This
  collection satisfies every clause of Bacon's Definition 9.1, p.190,
  including directed reduction with α relabelling and finite relettering.
  L, Λ and Σ remain arbitrary: only the permitted logical symbols and
  declared nonlogical constants occur in the language.

  This is an instance proof, not a strengthening of the general-language
  predicate. Its application-argument clause retains the source's
  variable exception, even though this particular full language contains
  variables. Typing of substitution and relettering holds independently
  of some printed free-for guards; those guards remain present in the
  locale obligations. No model, richness, or extra closure axiom is used.
\<close>

theorem book_full_general_lambda_language:
  fixes L :: "'l \<Rightarrow> otype" and \<Sigma> :: "'c ssignature"
  shows "book_general_lambda_language L \<Lambda> \<Sigma> G
    (\<lambda>\<tau>. {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>})"
proof unfold_locales
  fix A \<tau>
  assume member: "A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
  show "book_in_language L \<Lambda> \<Sigma> G A \<tau>" using member by simp
next
  fix c \<tau>
  assume declared: "c \<in> \<Sigma> \<tau>"
  show "NConst c \<tau> \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    by (simp add: book_language_const_iff declared)
next
  fix l
  assume present: "l \<in> \<Lambda>"
  show "NLogical l \<in> {A. book_in_language L \<Lambda> \<Sigma> G A (L l)}"
    by (simp only: mem_Collect_eq; rule book_language_Logical[OF present])
next
  fix F A \<sigma> \<tau>
  assume head: "F \<in> {A. book_in_language L \<Lambda> \<Sigma> G A (Arr \<sigma> \<tau>)}"
    and argument: "A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<sigma>}"
  have fl: "book_in_language L \<Lambda> \<Sigma> G F (Arr \<sigma> \<tau>)" using head by simp
  have al: "book_in_language L \<Lambda> \<Sigma> G A \<sigma>" using argument by simp
  show "NApp F A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    by (simp only: mem_Collect_eq; rule book_language_App[OF fl al])
next
  fix F A \<sigma> \<tau>
  assume member: "NApp F A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    and typed: "has_ntype L G F (Arr \<sigma> \<tau>)"
  have whole: "book_in_language L \<Lambda> \<Sigma> G (NApp F A) \<tau>" using member by simp
  show "F \<in> {A. book_in_language L \<Lambda> \<Sigma> G A (Arr \<sigma> \<tau>)}"
    by (simp only: mem_Collect_eq; rule book_full_application_head_language[OF whole typed])
next
  fix F A \<sigma> \<tau>
  assume member: "NApp F A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    and typed: "has_ntype L G A \<sigma>" and nonvariable: "\<not> (\<exists>n. A = NVar n)"
  have whole: "book_in_language L \<Lambda> \<Sigma> G (NApp F A) \<tau>" using member by simp
  show "A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<sigma>}"
    by (simp only: mem_Collect_eq; rule book_full_application_argument_language[OF whole typed])
next
  fix A B \<tau>
  assume member: "A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    and reduction: "book_source_reduces G A B"
  have al: "book_in_language L \<Lambda> \<Sigma> G A \<tau>" using member by simp
  show "B \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    by (simp only: mem_Collect_eq; rule book_source_reduces_language[OF reduction al])
next
  fix A B \<tau> n
  assume member: "A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    and replacement: "B \<in> {A. book_in_language L \<Lambda> \<Sigma> G A (G n)}"
    and free_for: "book_printed_free_for B n A"
  have al: "book_in_language L \<Lambda> \<Sigma> G A \<tau>" using member by simp
  have bl: "book_in_language L \<Lambda> \<Sigma> G B (G n)" using replacement by simp
  show "named_subst n B A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    by (simp only: mem_Collect_eq; rule book_variable_subst_language[OF al bl])
next
  fix A B \<tau> c \<sigma>
  assume member: "A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    and declared: "c \<in> \<Sigma> \<sigma>"
    and replacement: "B \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<sigma>}"
    and free_for: "book_printed_free_for B 0 A"
  have al: "book_in_language L \<Lambda> \<Sigma> G A \<tau>" using member by simp
  have bl: "book_in_language L \<Lambda> \<Sigma> G B \<sigma>" using replacement by simp
  show "book_const_subst c \<sigma> B A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    by (simp only: mem_Collect_eq; rule book_const_subst_language[OF al bl])
next
  fix A B \<tau> l
  assume member: "A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    and present: "l \<in> \<Lambda>"
    and replacement: "B \<in> {A. book_in_language L \<Lambda> \<Sigma> G A (L l)}"
    and free_for: "book_printed_free_for B 0 A"
  have al: "book_in_language L \<Lambda> \<Sigma> G A \<tau>" using member by simp
  have bl: "book_in_language L \<Lambda> \<Sigma> G B (L l)" using replacement by simp
  show "book_logical_subst l B A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    by (simp only: mem_Collect_eq; rule book_logical_subst_language[OF al bl])
next
  fix A \<tau> xs ys
  assume member: "A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    and sources_distinct: "distinct xs" and targets_distinct: "distinct ys"
    and source_names: "set xs \<subseteq> named_fv A"
    and aligned: "list_all2 (\<lambda>x y. G x = G y) xs ys"
    and free_for: "\<And>x y. (x,y) \<in> set (zip xs ys) \<Longrightarrow> book_printed_free_for (NVar y) x A"
  have al: "book_in_language L \<Lambda> \<Sigma> G A \<tau>" using member by simp
  show "book_variable_reletter G xs ys A \<in> {A. book_in_language L \<Lambda> \<Sigma> G A \<tau>}"
    by (simp only: mem_Collect_eq; rule book_variable_reletter_language[OF al aligned])
qed

end
