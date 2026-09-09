theory Bacon_Source_Relational_Inst_Gen_Certificate
  imports Bacon_Source_Relational_Existential_Duality_Proof
begin

section \<open>Native material certificates connecting Inst to Gen\<close>

lemma paper_R_named_H_contraposition_iff:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
  shows "paper_R_named_H \<Sigma> G (named_paper_iff G (named_paper_imp G P Q)
    (named_paper_imp G (named_paper_not Q) (named_paper_not P)))"
proof -
  have tautology: "sprop_tautology (SPIff (SPImp (SPAtom (0::nat)) (SPAtom 1))
      (SPImp (SPNot (SPAtom 1)) (SPNot (SPAtom 0))))" by (auto simp: sprop_tautology_def)
  show ?thesis using paper_R_named_H_binary_PC[OF rich pl ql tautology] by simp
qed

text \<open>
  H proves (¬Q→∀u.¬P)↔((∃u.P)→Q), using the proved
  quantifier duality and an explicit propositional certificate. P and Q
  may be open. The material equivalence itself does not require u-fresh Q;
  that guard is needed separately when applying Gen to ¬Q→¬P.
  Source role: the dual Inst calculation of Appendix A.2, p.67.
  No C rule, semantic premise or abstraction identity is assumed.
\<close>

theorem paper_R_named_H_Inst_Gen_equivalence:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_R_named_H \<Sigma> G (named_paper_iff G
    (named_paper_imp G (named_paper_not Q) (named_paper_all \<sigma> (NLam u (named_paper_not P))))
    (named_paper_imp G (named_paper_ex \<sigma> (NLam u P)) Q))"
proof -
  let ?A = "named_paper_all \<sigma> (NLam u (named_paper_not P))"
  let ?E = "named_paper_ex \<sigma> (NLam u P)"
  have al: "paper_R_in_language \<Sigma> G ?A Prop"
    by (rule paper_R_named_all_binder_language[OF paper_R_named_not_language[OF pl] variable rt])
  have el: "paper_R_in_language \<Sigma> G ?E Prop"
    by (rule paper_R_named_ex_binder_language[OF pl variable rt])
  have duality: "paper_R_named_H \<Sigma> G (named_paper_iff G ?A (named_paper_not ?E))"
    by (rule paper_R_named_H_all_not_exists_duality[OF rich pl variable rt])
  have tautology: "sprop_tautology (SPImp (SPIff (SPAtom (0::nat)) (SPNot (SPAtom 1)))
    (SPIff (SPImp (SPNot (SPAtom 2)) (SPAtom 0)) (SPImp (SPAtom 1) (SPAtom 2))))"
    by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Sigma> G (named_paper_imp G
      (named_paper_iff G ?A (named_paper_not ?E))
      (named_paper_iff G (named_paper_imp G (named_paper_not Q) ?A) (named_paper_imp G ?E Q)))"
    using paper_R_named_H_ternary_PC[OF rich al el ql tautology] by simp
  have left: "paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_not Q) ?A) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich paper_R_named_not_language[OF ql] al])
  have right: "paper_R_in_language \<Sigma> G (named_paper_imp G ?E Q) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich el ql])
  show ?thesis by (rule paper_R_named_H.MP[OF duality schema paper_R_named_paper_iff_language[OF rich left right]])
qed

end
