theory Bacon_Source_Relational_H_Theory_Necessitation
  imports Bacon_Source_Relational_H_Theory Bacon_Source_Relational_Box_Syntax
begin

section \<open>The explicit PC certificate in the printed Necessitation argument\<close>

lemma paper_R_named_H_necessitation_PC:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_imp G P (named_paper_iff G P (named_paper_or P (named_paper_not P))))"
proof -
  have em: "paper_R_in_language \<Sigma> G (named_paper_or P (named_paper_not P)) Prop"
    by (rule paper_R_named_or_language[OF pl paper_R_named_not_language[OF pl]])
  have il: "paper_R_in_language \<Sigma> G (named_paper_iff G P (named_paper_or P (named_paper_not P))) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich pl em])
  have whole: "paper_R_in_language \<Sigma> G
    (named_paper_imp G P (named_paper_iff G P (named_paper_or P (named_paper_not P)))) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich pl il])
  have tautology: "sprop_tautology (SPImp (SPAtom (0::nat))
    (SPIff (SPAtom 0) (SPOr (SPAtom 0) (SPNot (SPAtom 0)))))"
    by (auto simp: sprop_tautology_def)
  show ?thesis by (rule paper_R_named_H_PC_instance[OF whole tautology, where v="\<lambda>_. P"]; simp)
qed

section \<open>Necessitation is conditional on the supplied theory's PE closure\<close>

text \<open>
  If T is an H-theory closed under Propositional Equivalence, P∈T
  implies □P∈T. Native PC gives P↔(P∨¬P) in T; T's
  explicit PE condition gives P=ₜ(P∨¬P), and the proved H β
  implication folds this identity into the literal □P.
  Source: pp.16–17, and the Necessitation step in p.52 n.73.

  No PE or Necessitation rule is added to H. The theorem is about
  a supplied T satisfying the stated independent closure predicates.
  No C presentation, model, semantics or completeness premise is used.
\<close>

theorem paper_R_H_theory_necessitation:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T" and member: "P \<in> T"
  shows "paper_R_named_box G P \<in> T"
proof -
  let ?E = "named_paper_or P (named_paper_not P)"
  have pl: "paper_R_in_language \<Sigma> G P Prop" by (rule paper_R_H_theory_language[OF theory_h member])
  have el: "paper_R_in_language \<Sigma> G ?E Prop" by (rule paper_R_named_or_language[OF pl paper_R_named_not_language[OF pl]])
  have il: "paper_R_in_language \<Sigma> G (named_paper_iff G P ?E) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich pl el])
  have schema: "named_paper_imp G P (named_paper_iff G P ?E) \<in> T"
    by (rule paper_R_H_theory_H[OF theory_h paper_R_named_H_necessitation_PC[OF rich pl]])
  have biconditional: "named_paper_iff G P ?E \<in> T" by (rule paper_R_H_theory_MP[OF theory_h member schema il])
  have identity: "named_paper_eq Prop P ?E \<in> T" by (rule paper_R_PE_closedD[OF pe pl el biconditional])
  have folding: "named_paper_imp G (named_paper_eq Prop P ?E) (paper_R_named_box G P) \<in> T"
    by (rule paper_R_H_theory_H[OF theory_h paper_R_named_H_box_fold[OF rich pl]])
  show ?thesis by (rule paper_R_H_theory_MP[OF theory_h identity folding paper_R_named_box_language[OF rich pl]])
qed

end
