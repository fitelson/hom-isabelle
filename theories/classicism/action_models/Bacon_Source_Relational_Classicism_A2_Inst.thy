theory Bacon_Source_Relational_Classicism_A2_Inst
  imports Bacon_Source_Relational_Classicism_A2_Gen
    Bacon_Source_Relational_Inst_Gen_Certificate Bacon_Source_Relational_Classicism_Identity_Consequences
begin

section \<open>The dual Inst case of Appendix A.2\<close>

text \<open>
  Transfer the induction hypothesis for P→Q to ¬Q→¬P
  using its H-certified contraposition biconditional. Apply the proved
  Gen case, retaining u∉FV(Q), to obtain the abstraction-to-truth
  property for ¬Q→∀u.¬P. Native H duality identifies this formula
  materially with (∃u.P)→Q, and H-certified Logical Equivalence
  transfers the result at the requested prefix.

  Source: the dual Inst calculation in Appendix A.2, p.67. This proof
  neither treats material equivalence as H identity nor assumes the
  general C Equivalence rule. All identity transfers use H certificates
  and the p.12 schema; the original eigenvariable condition remains.
\<close>

theorem paper_R_classicism_A2_Inst:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>" and fresh: "u \<notin> named_fv Q"
    and binders: "list_all paper_R_type (map G ns)"
    and premise: "\<And>ms. list_all paper_R_type (map G ms) \<Longrightarrow>
      paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ms) Prop)
        (named_lam_vec ms (named_paper_imp G P Q)) (named_lam_vec ms (paper_R_named_top G)))"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns (named_paper_imp G (named_paper_ex \<sigma> (NLam u P)) Q))
    (named_lam_vec ns (paper_R_named_top G)))"
proof -
  let ?NP = "named_paper_not P"
  let ?NQ = "named_paper_not Q"
  let ?I = "named_paper_imp G P Q"
  let ?C = "named_paper_imp G ?NQ ?NP"
  let ?L = "named_paper_imp G ?NQ (named_paper_all \<sigma> (NLam u ?NP))"
  let ?R = "named_paper_imp G (named_paper_ex \<sigma> (NLam u P)) Q"
  have npl: "paper_R_in_language \<Sigma> G ?NP Prop" by (rule paper_R_named_not_language[OF pl])
  have nql: "paper_R_in_language \<Sigma> G ?NQ Prop" by (rule paper_R_named_not_language[OF ql])
  have il: "paper_R_in_language \<Sigma> G ?I Prop" by (rule paper_R_named_paper_imp_language[OF rich pl ql])
  have cl: "paper_R_in_language \<Sigma> G ?C Prop" by (rule paper_R_named_paper_imp_language[OF rich nql npl])
  have contra: "paper_R_named_H \<Sigma> G (named_paper_iff G ?I ?C)"
    by (rule paper_R_named_H_contraposition_iff[OF rich pl ql])
  have transformed: "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ms) Prop)
      (named_lam_vec ms ?C) (named_lam_vec ms (paper_R_named_top G)))"
    if "list_all paper_R_type (map G ms)" for ms
    by (rule paper_R_classicism_A2_H_equivalent[OF rich il cl contra that premise[OF that]])
  have fresh_negative: "u \<notin> named_fv ?NQ"
    by (simp only: named_paper_primitive_fv; rule fresh)
  have generalized: "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
      (named_lam_vec ns ?L) (named_lam_vec ns (paper_R_named_top G)))"
    by (rule paper_R_classicism_A2_Gen[OF rich nql npl variable rt fresh_negative binders transformed])
  have ll: "paper_R_in_language \<Sigma> G ?L Prop"
    by (rule paper_R_named_paper_imp_language[OF rich nql paper_R_named_all_binder_language[OF npl variable rt]])
  have rl: "paper_R_in_language \<Sigma> G ?R Prop"
    by (rule paper_R_named_paper_imp_language[OF rich paper_R_named_ex_binder_language[OF pl variable rt] ql])
  have certificate: "paper_R_named_H \<Sigma> G (named_paper_iff G ?L ?R)"
    by (rule paper_R_named_H_Inst_Gen_equivalence[OF rich pl ql variable rt])
  show ?thesis by (rule paper_R_classicism_A2_H_equivalent[OF rich ll rl certificate binders generalized])
qed

end
