theory Bacon_Source_Relational_Box_Unfolding
  imports Bacon_Source_Relational_Box_Syntax Bacon_Source_Relational_H_Theory
begin

theorem paper_R_named_H_box_unfold:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_imp G (paper_R_named_box G P) (named_paper_eq Prop P (named_paper_or P (named_paper_not P))))"
proof -
  have bl: "paper_R_in_language \<Sigma> G (paper_R_named_box G P) Prop" by (rule paper_R_named_box_language[OF rich pl])
  have el: "paper_R_in_language \<Sigma> G (named_paper_eq Prop P (named_paper_or P (named_paper_not P))) Prop"
    by (rule paper_R_named_identity_language[OF pl paper_R_named_or_language[OF pl paper_R_named_not_language[OF pl]]])
  have il: "paper_R_in_language \<Sigma> G
    (named_paper_iff G (paper_R_named_box G P) (named_paper_eq Prop P (named_paper_or P (named_paper_not P)))) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich bl el])
  have conversion: "paper_R_named_H \<Sigma> G
    (named_paper_iff G (paper_R_named_box G P) (named_paper_eq Prop P (named_paper_or P (named_paper_not P))))"
    by (rule paper_R_named_H.Beta[OF bl el paper_R_named_box_beta il])
  show ?thesis by (rule paper_R_named_H.MP[OF conversion paper_R_named_H_iff_forward[OF rich bl el]
    paper_R_named_paper_imp_language[OF rich bl el]])
qed

lemma paper_R_named_derivable_box_unfold:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and premise: "paper_R_named_derivable \<Sigma> G S (paper_R_named_box G P)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop P (named_paper_or P (named_paper_not P)))"
  by (rule paper_R_named_derivable.MP[OF premise paper_R_named_derivable.Theorem[OF paper_R_named_H_box_unfold[OF rich pl]]
    paper_R_named_identity_language[OF pl paper_R_named_or_language[OF pl paper_R_named_not_language[OF pl]]]])

lemma paper_R_named_derivable_box_fold:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and premise: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop P (named_paper_or P (named_paper_not P)))"
  shows "paper_R_named_derivable \<Sigma> G S (paper_R_named_box G P)"
  by (rule paper_R_named_derivable.MP[OF premise paper_R_named_derivable.Theorem[OF paper_R_named_H_box_fold[OF rich pl]]
    paper_R_named_box_language[OF rich pl]])

lemma paper_R_H_theory_PE_H:
  assumes theory_h: "paper_R_H_theory \<Sigma> G T" and pe: "paper_R_PE_closed \<Sigma> G T"
    and pl: "paper_R_in_language \<Sigma> G P Prop" and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and theorem_H: "paper_R_named_H \<Sigma> G (named_paper_iff G P Q)"
  shows "named_paper_eq Prop P Q \<in> T"
  by (rule paper_R_PE_closedD[OF pe pl ql paper_R_H_theory_H[OF theory_h theorem_H]])

text \<open>
  Box folding/unfolding are native H consequences of the literal β
  clause. The last lemma uses PE only as an explicit condition on T,
  turning an H-certified Boolean biconditional into an identity in T.
  These helpers assume no modal law, C rule, or semantic model.
  Source: Figure 1, pp.16–17 and the modal reasoning in p.52 n.73.
\<close>

end
