theory Bacon_Source_Relational_H_Theory_Normal_K
  imports Bacon_Source_Relational_Box_Unfolding Bacon_Source_Relational_Boolean_Identity_Congruence
    Bacon_Source_Relational_Boolean_PC
begin

section \<open>Normal K from scalar PE identities and literal Box unfolding\<close>

text \<open>
  In an H-theory T closed under PE, □(P→Q)→(□P→□Q)
  follows by local reasoning. T already contains
  Q=Q∨(P∧(P→Q)) and
  Q∨((P∨¬P)∧((P→Q)∨¬(P→Q)))=Q∨¬Q.
  The two temporary Box assumptions supply the two defining identities;
  native Boolean application congruence replaces their operands.
  Fold Q=Q∨¬Q into □Q, then discharge the assumptions.
  Source: K on p.16 and its role in p.52 n.73.

  No Necessitation is applied under either assumption. No Top or
  A.3 theorem, C or ζ judgment, or semantic model is used.
\<close>

theorem paper_R_H_theory_normal_K:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T"
    and pl: "paper_R_in_language \<Sigma> G P Prop" and ql: "paper_R_in_language \<Sigma> G Q Prop"
  shows "named_paper_imp G (paper_R_named_box G (named_paper_imp G P Q))
    (named_paper_imp G (paper_R_named_box G P) (paper_R_named_box G Q)) \<in> T"
proof -
  let ?R = "named_paper_imp G P Q"
  let ?EP = "named_paper_or P (named_paper_not P)"
  let ?ER = "named_paper_or ?R (named_paper_not ?R)"
  let ?EQ = "named_paper_or Q (named_paper_not Q)"
  let ?U = "named_paper_or Q (named_paper_and P ?R)"
  let ?V = "named_paper_or Q (named_paper_and ?EP ?ER)"
  let ?S = "insert (paper_R_named_box G P) (insert (paper_R_named_box G ?R) T)"
  have rl: "paper_R_in_language \<Sigma> G ?R Prop" by (rule paper_R_named_paper_imp_language[OF rich pl ql])
  have ep: "paper_R_in_language \<Sigma> G ?EP Prop" by (rule paper_R_named_or_language[OF pl paper_R_named_not_language[OF pl]])
  have er: "paper_R_in_language \<Sigma> G ?ER Prop" by (rule paper_R_named_or_language[OF rl paper_R_named_not_language[OF rl]])
  have eq: "paper_R_in_language \<Sigma> G ?EQ Prop" by (rule paper_R_named_or_language[OF ql paper_R_named_not_language[OF ql]])
  have old_and: "paper_R_in_language \<Sigma> G (named_paper_and P ?R) Prop" by (rule paper_R_named_and_language[OF pl rl])
  have new_and: "paper_R_in_language \<Sigma> G (named_paper_and ?EP ?ER) Prop" by (rule paper_R_named_and_language[OF ep er])
  have ul: "paper_R_in_language \<Sigma> G ?U Prop" by (rule paper_R_named_or_language[OF ql old_and])
  have vl: "paper_R_in_language \<Sigma> G ?V Prop" by (rule paper_R_named_or_language[OF ql new_and])
  have start_tautology: "sprop_tautology (SPIff (SPAtom (1::nat))
    (SPOr (SPAtom 1) (SPAnd (SPAtom 0) (SPImp (SPAtom 0) (SPAtom 1)))))"
    by (auto simp: sprop_tautology_def)
  have start_H: "paper_R_named_H \<Sigma> G (named_paper_iff G Q ?U)"
    using paper_R_named_H_binary_PC[OF rich pl ql start_tautology] by simp
  have start_T: "named_paper_eq Prop Q ?U \<in> T" by (rule paper_R_H_theory_PE_H[OF theory_h pe ql ul start_H])
  let ?TR = "SPImp (SPAtom (0::nat)) (SPAtom 1)"
  let ?TEP = "SPOr (SPAtom (0::nat)) (SPNot (SPAtom 0))"
  let ?TER = "SPOr ?TR (SPNot ?TR)"
  let ?TEQ = "SPOr (SPAtom (1::nat)) (SPNot (SPAtom 1))"
  have end_tautology: "sprop_tautology (SPIff (SPOr (SPAtom 1) (SPAnd ?TEP ?TER)) ?TEQ)"
    by (auto simp: sprop_tautology_def)
  have end_H: "paper_R_named_H \<Sigma> G (named_paper_iff G ?V ?EQ)"
    using paper_R_named_H_binary_PC[OF rich pl ql end_tautology] by simp
  have end_T: "named_paper_eq Prop ?V ?EQ \<in> T" by (rule paper_R_H_theory_PE_H[OF theory_h pe vl eq end_H])
  have boxP: "paper_R_in_language \<Sigma> G (paper_R_named_box G P) Prop" by (rule paper_R_named_box_language[OF rich pl])
  have boxR: "paper_R_in_language \<Sigma> G (paper_R_named_box G ?R) Prop" by (rule paper_R_named_box_language[OF rich rl])
  have assumed_P: "paper_R_named_derivable \<Sigma> G ?S (paper_R_named_box G P)"
    by (rule paper_R_named_derivable.Assumption; (rule insertI1 | rule boxP))
  have assumed_R: "paper_R_named_derivable \<Sigma> G ?S (paper_R_named_box G ?R)"
    by (rule paper_R_named_derivable.Assumption; (rule insertI2, rule insertI1 | rule boxR))
  have p_identity: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop P ?EP)"
    by (rule paper_R_named_derivable_box_unfold[OF rich pl assumed_P])
  have r_identity: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop ?R ?ER)"
    by (rule paper_R_named_derivable_box_unfold[OF rich rl assumed_R])
  have conjunction: "paper_R_named_derivable \<Sigma> G ?S
    (named_paper_eq Prop (named_paper_and P ?R) (named_paper_and ?EP ?ER))"
    by (rule paper_R_named_identity_boolean_and[OF rich pl ep rl er p_identity r_identity])
  have replacement: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop ?U ?V)"
    by (rule paper_R_named_identity_boolean_or[OF rich ql ql old_and new_and
      paper_R_named_identity_refl[OF ql] conjunction])
  have start: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop Q ?U)"
    by (rule paper_R_named_derivable.Assumption;
      (rule insertI2, rule insertI2, rule start_T | rule paper_R_named_identity_language[OF ql ul]))
  have finish: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop ?V ?EQ)"
    by (rule paper_R_named_derivable.Assumption;
      (rule insertI2, rule insertI2, rule end_T | rule paper_R_named_identity_language[OF vl eq]))
  have intermediate: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop Q ?V)"
    by (rule paper_R_named_identity_trans[OF rich ql ul vl start replacement])
  have result_identity: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop Q ?EQ)"
    by (rule paper_R_named_identity_trans[OF rich ql vl eq intermediate finish])
  have result: "paper_R_named_derivable \<Sigma> G ?S (paper_R_named_box G Q)"
    by (rule paper_R_named_derivable_box_fold[OF rich ql result_identity])
  have first_discharge: "paper_R_named_derivable \<Sigma> G (insert (paper_R_named_box G ?R) T)
    (named_paper_imp G (paper_R_named_box G P) (paper_R_named_box G Q))"
    by (rule paper_R_named_derivable_deduction[OF rich boxP result])
  have discharged: "paper_R_named_derivable \<Sigma> G T (named_paper_imp G (paper_R_named_box G ?R)
    (named_paper_imp G (paper_R_named_box G P) (paper_R_named_box G Q)))"
    by (rule paper_R_named_derivable_deduction[OF rich boxR first_discharge])
  show ?thesis by (rule paper_R_H_theory_local_consequences[OF theory_h discharged subset_refl])
qed

end
