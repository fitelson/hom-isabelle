theory Bacon_Source_Relational_Equivalence_Soundness
  imports Bacon_Source_Relational_Equivalence_Presentation
    Bacon_Source_Relational_Common_Equivalence Bacon_Source_Relational_Common_Quantifier_Rules
begin

section \<open>Soundness of the independent R Equivalence-rule presentation\<close>

text \<open>
  Every theorem of Hᴿ closed under MP, Gen, Inst and full
  Equivalence belongs to the common theory of each intensional
  selected R BBK category. Source: the rule presentation on p.14
  and the soundness argument of Theorem 3.12, p.51.

  This induction uses the proved common-theory closure rules.
  It assumes neither the soundness of the axiom-based C judgment
  nor an F model extension. The independent source-rule presentation
  is sound; its equality with the printed identity-axiom presentation
  and the separating-model/completeness constructions remain separate.
\<close>

theorem paper_R_equivalence_category_soundness:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows"
    and derivation: "paper_R_equivalence_proves \<Sigma> G A"
  shows "A \<in> paper_R_common_theory \<Sigma> G Obj"
proof -
  have models: "paper_R_bbk_data_valid \<Sigma> G M" if "M \<in> Obj" for M
    by (rule paper_R_bbk_subcategory_models[OF category that])
  show ?thesis using derivation
  proof (induction rule: paper_R_equivalence_proves.induct)
    case H
    show ?case by (rule paper_R_common_contains_H[OF models H.hyps])
  next
    case MP
    show ?case by (rule paper_R_common_MP[OF models MP.IH(1,2) MP.hyps(3)])
  next
    case Gen
    show ?case by (rule paper_R_common_Gen[OF models Gen.IH Gen.hyps(2,3,4)])
  next
    case Inst
    show ?case by (rule paper_R_common_Inst[OF models Inst.IH Inst.hyps(2,3,4)])
  next
    case Equivalence
    show ?case by (rule paper_R_common_Equivalence[
      OF category intensional Equivalence.hyps(2,3,4) Equivalence.IH])
  qed
qed

corollary paper_R_equivalence_model_truth:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows"
    and derivation: "paper_R_equivalence_proves \<Sigma> G A"
    and object: "M \<in> Obj"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g A"
  shows "paper_bbk_valuation M (paper_bbk_denote M g A)"
  by (rule paper_R_common_theory_truth[
    OF paper_R_equivalence_category_soundness[OF category intensional derivation] object typed adequate])

end
