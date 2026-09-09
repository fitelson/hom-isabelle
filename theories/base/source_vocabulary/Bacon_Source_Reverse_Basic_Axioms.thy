theory Bacon_Source_Reverse_Basic_Axioms
  imports Bacon_Source_Global_Proof_Basics Bacon_Source_Reverse_Identity_Axioms
    Bacon_Source_Reverse_Conversion Bacon_Source_Renaming_Conversion
    Bacon_Source_Global_Existence
begin

section \<open>Reverse conversion axioms, target existence, and modus ponens\<close>

text \<open>
  Target β/η gives a conjunction of two implications.  The source
  conversion axiom first gives its literal ↔; a proved source PC/MP
  consequence then expands it to the required conjunction.  The target's
  explicit individual-existence clause is supplied by the source's derived
  Existence theorem in a rich variable stock, not by an added source axiom.
  Source: Bacon--Dorr Figure 1, p.6; Figure 2 and Existence, pp.7–8.

  Isabelle representation.  Every converted endpoint is globally typed
  through paper_back_embedding_language.  Raw β/η steps pass through
  pterm_to_paper and srename.  Reverse MP obtains its conclusion language
  directly from the source implication theorem.
  Status.  These are individual reverse proof cases, not a presupposed
  proof-reflection theorem or identity between connective operations.
\<close>

lemma paper_reverse_biconditional_shape:
  "srename r (pterm_to_paper (PObjIff A B)) =
    paper_and
      (paper_imp (srename r (pterm_to_paper A)) (srename r (pterm_to_paper B)))
      (paper_imp (srename r (pterm_to_paper B)) (srename r (pterm_to_paper A)))"
  by (simp only: pterm_to_paper.simps paper_and_def srename.simps srename_paper_imp)

theorem paper_reverse_Beta:
  assumes A: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    and B: "pterm_in_language \<Sigma> \<Gamma> B Prop"
    and step: "pcompatible_step pbeta_contract A B"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_H \<Sigma> G (srename r (pterm_to_paper (PObjIff A B)))"
proof -
  let ?A = "srename r (pterm_to_paper A)"
  let ?B = "srename r (pterm_to_paper B)"
  have A_language: "sgterm_in_language paper_logical_type \<Sigma> G ?A Prop"
    by (rule paper_back_embedding_language[where G=G and r=r, OF A map])
  have B_language: "sgterm_in_language paper_logical_type \<Sigma> G ?B Prop"
    by (rule paper_back_embedding_language[where G=G and r=r, OF B map])
  have source_step: "scompatible_step sbeta_contract ?A ?B"
    by (rule srename_beta_step[OF pterm_to_paper_beta_step[OF step]])
  have biconditional: "paper_global_H \<Sigma> G (paper_iff ?A ?B)"
    by (rule paper_global_beta_biconditional[OF A_language B_language source_step])
  have expanded: "paper_global_H \<Sigma> G (paper_and (paper_imp ?A ?B) (paper_imp ?B ?A))"
    by (rule paper_global_H_iff_expanded[OF A_language B_language biconditional])
  show ?thesis using expanded by (simp only: paper_reverse_biconditional_shape)
qed

theorem paper_reverse_Eta:
  assumes A: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    and B: "pterm_in_language \<Sigma> \<Gamma> B Prop"
    and step: "pcompatible_step peta_contract A B"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_H \<Sigma> G (srename r (pterm_to_paper (PObjIff A B)))"
proof -
  let ?A = "srename r (pterm_to_paper A)"
  let ?B = "srename r (pterm_to_paper B)"
  have A_language: "sgterm_in_language paper_logical_type \<Sigma> G ?A Prop"
    by (rule paper_back_embedding_language[where G=G and r=r, OF A map])
  have B_language: "sgterm_in_language paper_logical_type \<Sigma> G ?B Prop"
    by (rule paper_back_embedding_language[where G=G and r=r, OF B map])
  have source_step: "scompatible_step seta_contract ?A ?B"
    by (rule srename_eta_step[OF pterm_to_paper_eta_step[OF step]])
  have biconditional: "paper_global_H \<Sigma> G (paper_iff ?A ?B)"
    by (rule paper_global_eta_biconditional[OF A_language B_language source_step])
  have expanded: "paper_global_H \<Sigma> G (paper_and (paper_imp ?A ?B) (paper_imp ?B ?A))"
    by (rule paper_global_H_iff_expanded[OF A_language B_language biconditional])
  show ?thesis using expanded by (simp only: paper_reverse_biconditional_shape)
qed

theorem paper_reverse_IndividualExistence:
  assumes rich: "sg_rich G"
  shows "paper_global_H \<Sigma> G
    (srename r (pterm_to_paper (PExists Ind (PEq Ind (PVar 0) (PVar 0)))))"
  using paper_global_type_existence[where \<Sigma>=\<Sigma> and \<sigma>=Ind, OF rich]
  by (simp only: pterm_to_paper.simps srename.simps lift_ren.simps)

theorem paper_reverse_MP:
  assumes premise: "paper_global_H \<Sigma> G (srename r (pterm_to_paper A))"
    and implication: "paper_global_H \<Sigma> G (srename r (pterm_to_paper (PImp A B)))"
  shows "paper_global_H \<Sigma> G (srename r (pterm_to_paper B))"
proof -
  let ?A = "srename r (pterm_to_paper A)"
  let ?B = "srename r (pterm_to_paper B)"
  have literal_implication: "paper_global_H \<Sigma> G (paper_imp ?A ?B)"
    using implication by (simp only: pterm_to_paper.simps srename_paper_imp)
  have implication_language: "sgterm_in_language paper_logical_type \<Sigma> G (paper_imp ?A ?B) Prop"
    by (rule paper_global_H_language[OF literal_implication])
  have conclusion_language: "sgterm_in_language paper_logical_type \<Sigma> G ?B Prop"
    by (rule conjunct2[OF iffD1[OF paper_global_imp_language_iff implication_language]])
  show ?thesis by (rule paper_global_H.MP[OF premise literal_implication conclusion_language])
qed

end
