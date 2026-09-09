theory Bacon_Source_Relational_Modal_Four
  imports Bacon_Source_Relational_Modal_T Bacon_Source_Relational_Identity_Stability
    Bacon_Source_Relational_Classicism_Box_Monotonicity
begin

section \<open>The literal native R necessity operator satisfies 4\<close>

theorem paper_R_classicism_modal_4:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G P Prop"
  shows "paper_R_classicism_proves \<Sigma> G
    (named_paper_imp G (paper_R_named_box G P) (paper_R_named_box G (paper_R_named_box G P)))"
proof -
  let ?B = "paper_R_named_box G P"
  let ?A = "named_paper_or P (named_paper_not P)"
  let ?E = "named_paper_eq Prop P ?A"
  let ?BE = "paper_R_named_box G ?E"
  let ?BB = "paper_R_named_box G ?B"
  let ?T = "{A. paper_R_classicism_proves \<Sigma> G A}"
  let ?S = "insert ?B ?T"
  have al: "paper_R_in_language \<Sigma> G ?A Prop"
    by (rule paper_R_named_or_language[OF language paper_R_named_not_language[OF language]])
  have el: "paper_R_in_language \<Sigma> G ?E Prop" by (rule paper_R_named_identity_language[OF language al])
  have bl: "paper_R_in_language \<Sigma> G ?B Prop" by (rule paper_R_named_box_language[OF rich language])
  have bel: "paper_R_in_language \<Sigma> G ?BE Prop" by (rule paper_R_named_box_language[OF rich el])
  have bbl: "paper_R_in_language \<Sigma> G ?BB Prop" by (rule paper_R_named_box_language[OF rich bl])
  have stability: "named_paper_imp G ?E ?BE \<in> ?T"
    by (rule paper_R_H_theory_identity_stability[OF rich paper_R_classicism_is_H_theory
      paper_R_classicism_is_PE_closed[OF rich] language al])
  have fold: "paper_R_classicism_proves \<Sigma> G (named_paper_imp G ?E ?B)"
    by (rule paper_R_classicism_proves.H[OF paper_R_named_H_box_fold[OF rich language]])
  have monotone: "paper_R_classicism_proves \<Sigma> G (named_paper_imp G ?BE ?BB)"
    by (rule paper_R_classicism_box_monotone[OF rich el bl fold])
  have monotone_member: "named_paper_imp G ?BE ?BB \<in> ?T" using monotone by simp
  have stability_language: "paper_R_in_language \<Sigma> G (named_paper_imp G ?E ?BE) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich el bel])
  have monotone_language: "paper_R_in_language \<Sigma> G (named_paper_imp G ?BE ?BB) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich bel bbl])
  have assumed: "paper_R_named_derivable \<Sigma> G ?S ?B"
    by (rule paper_R_named_derivable.Assumption[OF insertI1 bl])
  have identity: "paper_R_named_derivable \<Sigma> G ?S ?E"
    by (rule paper_R_named_derivable_box_unfold[OF rich language assumed])
  have stability_local: "paper_R_named_derivable \<Sigma> G ?S (named_paper_imp G ?E ?BE)"
    by (rule paper_R_named_derivable.Assumption[OF insertI2[OF stability] stability_language])
  have necessary_identity: "paper_R_named_derivable \<Sigma> G ?S ?BE"
    by (rule paper_R_named_derivable.MP[OF identity stability_local bel])
  have monotone_local: "paper_R_named_derivable \<Sigma> G ?S (named_paper_imp G ?BE ?BB)"
    by (rule paper_R_named_derivable.Assumption[OF insertI2[OF monotone_member] monotone_language])
  have iterated: "paper_R_named_derivable \<Sigma> G ?S ?BB"
    by (rule paper_R_named_derivable.MP[OF necessary_identity monotone_local bbl])
  have discharged: "paper_R_named_derivable \<Sigma> G ?T (named_paper_imp G ?B ?BB)"
    by (rule paper_R_named_derivable_deduction[OF rich bl iterated])
  have member: "named_paper_imp G ?B ?BB \<in> ?T"
    by (rule paper_R_H_theory_local_consequences[OF paper_R_classicism_is_H_theory discharged subset_refl])
  show ?thesis using member by simp
qed

text \<open>
  Write E for P=ₜ(P∨¬P). The proof composes □P→E,
  E→□E, and □E→□□P. Identity stability is obtained in the
  original native C theory. The third implication follows by Box
  monotonicity from H's fold E→□P; Necessitation applies only to
  that original C theorem, not to the temporary assumption □P.

  Together with the native Necessitation and K results, T and 4 give
  positive modal principles for the exact literal Box. No Kripke
  countermodel extension or exact-S4 converse is claimed here.
  Source: p.17 and n.21; the book's preorder route remains separate.
\<close>

end
