theory Bacon_Source_Relational_Classicism_Soundness
  imports Bacon_Source_Relational_Classicism_Presentation
    Bacon_Source_Relational_Equivalence_Soundness
begin

section \<open>Soundness of source-defined R Classicism in the small category setting\<close>

text \<open>
  Every theorem of Cᴿ belongs to the common theory of every
  supplied intensional selected R BBK category. Cᴿ is defined
  by H-certified Logical Equivalence and H-theory closure,
  following p.12. The semantic conclusion is the small,
  common-carrier instance of Theorem 3.12's soundness direction.

  The proof uses only the forward inclusion into the independent
  Equivalence-rule presentation and its checked soundness. It
  does not assume the converse inclusion, the Figures 3–4 axiomatization
  theorem, a separating-model construction,
  arbitrary-cardinality category transport or completeness.
  Signature and named stock are unchanged.
\<close>

theorem paper_R_classicism_category_soundness:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows"
    and derivation: "paper_R_classicism_proves \<Sigma> G A"
  shows "A \<in> paper_R_common_theory \<Sigma> G Obj"
  by (rule paper_R_equivalence_category_soundness[
    OF category intensional paper_R_classicism_into_equivalence[OF derivation]])

corollary paper_R_classicism_model_truth:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows"
    and derivation: "paper_R_classicism_proves \<Sigma> G A"
    and object: "M \<in> Obj"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g A"
  shows "paper_bbk_valuation M (paper_bbk_denote M g A)"
  by (rule paper_R_common_theory_truth[
    OF paper_R_classicism_category_soundness[OF category intensional derivation] object typed adequate])

end
