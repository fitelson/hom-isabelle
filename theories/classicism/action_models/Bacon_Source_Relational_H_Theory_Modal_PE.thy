theory Bacon_Source_Relational_H_Theory_Modal_PE
  imports Bacon_Source_Relational_Box_Unfolding Bacon_Source_Relational_Boolean_Identity_Congruence
    Bacon_Source_Relational_Boolean_PC
begin

section \<open>Modalized Propositional Equivalence in an H-theory closed under PE\<close>

text \<open>
  T contains □(P↔Q)→P=ₜQ. Put R=P↔Q and E=R∨¬R.
  Scalar H tautologies and T's explicit PE closure give
  P=(Q∧R)∨(¬Q∧¬R) and (Q∧E)∨(¬Q∧¬E)=Q.
  Under the temporary Box assumption, literal unfolding gives R=E.
  Native application congruence replaces both occurrences in the
  selector, and identity transitivity gives P=Q. Local deduction
  discharges the Box assumption.

  Source: the Modalized Fregean Axiom on p.18 and the modal step
  of p.52 n.73. No Necessitation is used under an assumption.
  This independent scalar proof imports no Top/A.3 result, C or ζ
  rule, semantic Boolean algebra, or model theorem.
\<close>

theorem paper_R_H_theory_modal_PE:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T"
    and pl: "paper_R_in_language \<Sigma> G P Prop" and ql: "paper_R_in_language \<Sigma> G Q Prop"
  shows "named_paper_imp G (paper_R_named_box G (named_paper_iff G P Q)) (named_paper_eq Prop P Q) \<in> T"
proof -
  let ?R = "named_paper_iff G P Q"
  let ?E = "named_paper_or ?R (named_paper_not ?R)"
  let ?U = "named_paper_or (named_paper_and Q ?R) (named_paper_and (named_paper_not Q) (named_paper_not ?R))"
  let ?V = "named_paper_or (named_paper_and Q ?E) (named_paper_and (named_paper_not Q) (named_paper_not ?E))"
  let ?S = "insert (paper_R_named_box G ?R) T"
  have rl: "paper_R_in_language \<Sigma> G ?R Prop" by (rule paper_R_named_paper_iff_language[OF rich pl ql])
  have el: "paper_R_in_language \<Sigma> G ?E Prop" by (rule paper_R_named_or_language[OF rl paper_R_named_not_language[OF rl]])
  have nq: "paper_R_in_language \<Sigma> G (named_paper_not Q) Prop" by (rule paper_R_named_not_language[OF ql])
  have nr: "paper_R_in_language \<Sigma> G (named_paper_not ?R) Prop" by (rule paper_R_named_not_language[OF rl])
  have ne: "paper_R_in_language \<Sigma> G (named_paper_not ?E) Prop" by (rule paper_R_named_not_language[OF el])
  have qr: "paper_R_in_language \<Sigma> G (named_paper_and Q ?R) Prop" by (rule paper_R_named_and_language[OF ql rl])
  have qe: "paper_R_in_language \<Sigma> G (named_paper_and Q ?E) Prop" by (rule paper_R_named_and_language[OF ql el])
  have nqr: "paper_R_in_language \<Sigma> G (named_paper_and (named_paper_not Q) (named_paper_not ?R)) Prop"
    by (rule paper_R_named_and_language[OF nq nr])
  have nqe: "paper_R_in_language \<Sigma> G (named_paper_and (named_paper_not Q) (named_paper_not ?E)) Prop"
    by (rule paper_R_named_and_language[OF nq ne])
  have ul: "paper_R_in_language \<Sigma> G ?U Prop" by (rule paper_R_named_or_language[OF qr nqr])
  have vl: "paper_R_in_language \<Sigma> G ?V Prop" by (rule paper_R_named_or_language[OF qe nqe])
  let ?TR = "SPIff (SPAtom (0::nat)) (SPAtom 1)"
  let ?TE = "SPOr ?TR (SPNot ?TR)"
  have start_tautology: "sprop_tautology (SPIff (SPAtom 0)
    (SPOr (SPAnd (SPAtom 1) ?TR) (SPAnd (SPNot (SPAtom 1)) (SPNot ?TR))))"
    by (auto simp: sprop_tautology_def)
  have start_H: "paper_R_named_H \<Sigma> G (named_paper_iff G P ?U)"
    using paper_R_named_H_binary_PC[OF rich pl ql start_tautology] by simp
  have start_T: "named_paper_eq Prop P ?U \<in> T" by (rule paper_R_H_theory_PE_H[OF theory_h pe pl ul start_H])
  have end_tautology: "sprop_tautology (SPIff
    (SPOr (SPAnd (SPAtom 1) ?TE) (SPAnd (SPNot (SPAtom 1)) (SPNot ?TE))) (SPAtom 1))"
    by (auto simp: sprop_tautology_def)
  have end_H: "paper_R_named_H \<Sigma> G (named_paper_iff G ?V Q)"
    using paper_R_named_H_binary_PC[OF rich pl ql end_tautology] by simp
  have end_T: "named_paper_eq Prop ?V Q \<in> T" by (rule paper_R_H_theory_PE_H[OF theory_h pe vl ql end_H])
  have box_language: "paper_R_in_language \<Sigma> G (paper_R_named_box G ?R) Prop" by (rule paper_R_named_box_language[OF rich rl])
  have assumed: "paper_R_named_derivable \<Sigma> G ?S (paper_R_named_box G ?R)"
    by (rule paper_R_named_derivable.Assumption; (rule insertI1 | rule box_language))
  have identity: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop ?R ?E)"
    by (rule paper_R_named_derivable_box_unfold[OF rich rl assumed])
  have negated: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop (named_paper_not ?R) (named_paper_not ?E))"
    by (rule paper_R_named_identity_boolean_not[OF rich rl el identity])
  have positive_branch: "paper_R_named_derivable \<Sigma> G ?S
    (named_paper_eq Prop (named_paper_and Q ?R) (named_paper_and Q ?E))"
    by (rule paper_R_named_identity_boolean_and[OF rich ql ql rl el paper_R_named_identity_refl[OF ql] identity])
  have negative_branch: "paper_R_named_derivable \<Sigma> G ?S
    (named_paper_eq Prop (named_paper_and (named_paper_not Q) (named_paper_not ?R))
      (named_paper_and (named_paper_not Q) (named_paper_not ?E)))"
    by (rule paper_R_named_identity_boolean_and[OF rich nq nq nr ne paper_R_named_identity_refl[OF nq] negated])
  have replacement: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop ?U ?V)"
    by (rule paper_R_named_identity_boolean_or[OF rich qr qe nqr nqe positive_branch negative_branch])
  have start: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop P ?U)"
    by (rule paper_R_named_derivable.Assumption; (rule insertI2[OF start_T] | rule paper_R_named_identity_language[OF pl ul]))
  have finish: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop ?V Q)"
    by (rule paper_R_named_derivable.Assumption; (rule insertI2[OF end_T] | rule paper_R_named_identity_language[OF vl ql]))
  have intermediate: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop P ?V)"
    by (rule paper_R_named_identity_trans[OF rich pl ul vl start replacement])
  have result: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop P Q)"
    by (rule paper_R_named_identity_trans[OF rich pl vl ql intermediate finish])
  have discharged: "paper_R_named_derivable \<Sigma> G T
    (named_paper_imp G (paper_R_named_box G ?R) (named_paper_eq Prop P Q))"
    by (rule paper_R_named_derivable_deduction[OF rich box_language result])
  show ?thesis by (rule paper_R_H_theory_local_consequences[OF theory_h discharged subset_refl])
qed

end
