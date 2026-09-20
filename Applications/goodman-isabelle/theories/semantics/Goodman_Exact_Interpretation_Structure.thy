theory Goodman_Exact_Interpretation_Structure
  imports Goodman_Exact_Named_Denotation
    "Bacon_Book_Environment_Development.Bacon_Book_Environment"
begin

section \<open>The exact named evaluator is a typed interpretation structure\<close>

context pp_e_constants
begin

theorem gi_exact_book_interpretation_structure:
  "book_interpretation_structure gi_exact_domain gi_exact_app
    book_minimal_logical_type UNIV \<Sigma> G UNIV (gi_exact_named_denote C G)"
  by (unfold_locales;
    (rule gi_exact_app_closed | rule gi_exact_named_denote_type |
      rule gi_exact_named_denote_var | rule gi_exact_named_denote_app); assumption)

end

section \<open>Two typed assignments can be joined on compatible free-name sets\<close>

lemma gi_exact_assignment_join_typed:
  assumes gt: "book_env_typed gi_exact_domain G g" and ht: "book_env_typed gi_exact_domain G h"
  shows "book_env_typed gi_exact_domain G (\<lambda>n. if n \<in> S then g n else h n)"
  using gt ht unfolding book_env_typed_def by auto

theorem gi_exact_environment_from_same_assignment_conversion:
  assumes gt: "book_env_typed gi_exact_domain G g" and ht: "book_env_typed gi_exact_domain G h"
    and agree: "\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> g n = h n"
    and conversion: "\<And>v. book_env_typed gi_exact_domain G v \<Longrightarrow>
      gi_exact_named_denote C G v A = gi_exact_named_denote C G v B"
  shows "gi_exact_named_denote C G g A = gi_exact_named_denote C G h B"
proof -
  let ?v = "\<lambda>n. if n \<in> named_fv A then g n else h n"
  have vt: "book_env_typed gi_exact_domain G ?v"
    by (rule gi_exact_assignment_join_typed[OF gt ht])
  have left: "gi_exact_named_denote C G g A = gi_exact_named_denote C G ?v A"
    by (rule gi_exact_named_denote_locality; simp)
  have middle: "gi_exact_named_denote C G ?v A = gi_exact_named_denote C G ?v B"
    by (rule conversion[OF vt])
  have right: "gi_exact_named_denote C G ?v B = gi_exact_named_denote C G h B"
    by (rule gi_exact_named_denote_locality; use agree in auto)
  show ?thesis by (rule trans[OF left trans[OF middle right]])
qed

text \<open>
  This establishes the typed interpretation structure only. The second
  theorem reduces the book's intersection-of-free-names condition to
  same-assignment conversion preservation, by joining the two assignments.
  It does not assert conversion preservation: that is the next obligation.
  No environment locale or minimal-model locale is interpreted here.
\<close>

end
