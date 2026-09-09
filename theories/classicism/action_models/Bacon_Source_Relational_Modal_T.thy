theory Bacon_Source_Relational_Modal_T
  imports Bacon_Source_Relational_Box_Unfolding
    Bacon_Source_Relational_Propositional_Identity_Derivations
    Bacon_Source_Relational_Local_Exchange Bacon_Source_Relational_Boolean_PC
    Bacon_Source_Relational_Classicism_Presentation
begin

section \<open>The literal native R necessity operator satisfies T\<close>

theorem paper_R_named_H_modal_T:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G P Prop"
  shows "paper_R_named_H \<Sigma> G (named_paper_imp G (paper_R_named_box G P) P)"
proof -
  let ?B = "paper_R_named_box G P"
  let ?A = "named_paper_or P (named_paper_not P)"
  have box_language: "paper_R_in_language \<Sigma> G ?B Prop" by (rule paper_R_named_box_language[OF rich language])
  have taut_language: "paper_R_in_language \<Sigma> G ?A Prop"
    by (rule paper_R_named_or_language[OF language paper_R_named_not_language[OF language]])
  have tautology: "sprop_tautology (SPOr (SPAtom (0::nat)) (SPNot (SPAtom 0)))"
    by (auto simp: sprop_tautology_def)
  have taut_H: "paper_R_named_H \<Sigma> G ?A"
    using paper_R_named_H_binary_PC[OF rich language language tautology] by simp
  have assumed: "paper_R_named_derivable \<Sigma> G {?B} ?B"
    by (rule paper_R_named_derivable.Assumption[OF insertI1 box_language])
  have identity: "paper_R_named_derivable \<Sigma> G {?B} (named_paper_eq Prop P ?A)"
    by (rule paper_R_named_derivable_box_unfold[OF rich language assumed])
  have reverse: "paper_R_named_derivable \<Sigma> G {?B} (named_paper_eq Prop ?A P)"
    by (rule paper_R_named_identity_sym[OF rich language taut_language identity])
  have taut_local: "paper_R_named_derivable \<Sigma> G {?B} ?A"
    by (rule paper_R_named_derivable.Theorem[OF taut_H])
  have recovered: "paper_R_named_derivable \<Sigma> G {?B} P"
    by (rule paper_R_named_derivable_propositional_identity[OF rich taut_language language reverse taut_local])
  have discharged: "paper_R_named_derivable \<Sigma> G {} (named_paper_imp G ?B P)"
    by (rule paper_R_named_derivable_deduction[OF rich box_language recovered])
  show ?thesis by (rule iffD1[OF paper_R_named_derivable_empty_iff discharged])
qed

corollary paper_R_classicism_modal_T:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G P Prop"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_imp G (paper_R_named_box G P) P)"
  by (rule paper_R_classicism_proves.H[OF paper_R_named_H_modal_T[OF rich language]])

text \<open>
  T already follows in native H: □P β-unfolds to the identity of P
  with P∨¬P, and LL transfers the PC theorem P∨¬P across that
  identity. The local derivation uses only an assumption, H theorems,
  and MP; its deduction step introduces no local Gen or Necessitation.
  P may be open. Source: the modal discussion, pp.16–17 n.21.
\<close>

end
