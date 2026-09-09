theory Bacon_Source_Relational_Existential_Duality_Proof
  imports Bacon_Source_Relational_Existential_Proof_Basics
begin

section \<open>Native H proves the duality needed by Inst\<close>

text \<open>
  ⊢H (∀u.¬P)↔¬(∃u.P). The body P may be open and may
  contain u freely. UI gives ∀u.¬P→¬P; PC and Inst give
  ∀u.¬P→¬∃u.P. In the other direction EG gives P→∃u.P,
  and contraposition followed by Gen gives ¬∃u.P→∀u.¬P.
  The bound u is absent from both quantified formulas, exactly as
  the two eigenvariable guards require. Source: Figure 2, p.8 and
  the dual quantifier calculation in Appendix A.2, p.67.
\<close>

theorem paper_R_named_H_all_not_exists_duality:
  assumes rich: "paper_R_rich G" and body: "paper_R_in_language \<Sigma> G P Prop"
    and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_R_named_H \<Sigma> G (named_paper_iff G
    (named_paper_all \<sigma> (NLam u (named_paper_not P)))
    (named_paper_not (named_paper_ex \<sigma> (NLam u P))))"
proof -
  let ?A = "named_paper_all \<sigma> (NLam u (named_paper_not P))"
  let ?E = "named_paper_ex \<sigma> (NLam u P)"
  have negative: "paper_R_in_language \<Sigma> G (named_paper_not P) Prop"
    by (rule paper_R_named_not_language[OF body])
  have al: "paper_R_in_language \<Sigma> G ?A Prop"
    by (rule paper_R_named_all_binder_language[OF negative variable rt])
  have el: "paper_R_in_language \<Sigma> G ?E Prop"
    by (rule paper_R_named_ex_binder_language[OF body variable rt])
  have nal: "paper_R_in_language \<Sigma> G (named_paper_not ?A) Prop"
    by (rule paper_R_named_not_language[OF al])
  have nel: "paper_R_in_language \<Sigma> G (named_paper_not ?E) Prop"
    by (rule paper_R_named_not_language[OF el])
  have ui: "paper_R_named_H \<Sigma> G (named_paper_imp G ?A (named_paper_not P))"
    by (rule paper_R_named_H_all_binder_instance[OF rich negative variable rt])
  have reversed: "paper_R_named_H \<Sigma> G (named_paper_imp G P (named_paper_not ?A))"
    by (rule paper_R_named_H_negative_swap[OF rich al body ui])
  have fresh_A: "u \<notin> named_fv (named_paper_not ?A)"
    by (simp add: named_paper_primitive_fv)
  have instantiated: "paper_R_named_H \<Sigma> G (named_paper_imp G ?E (named_paper_not ?A))"
    by (rule paper_R_named_H.Inst[OF reversed variable fresh_A
      paper_R_named_paper_imp_language[OF rich el nal]])
  have forward: "paper_R_named_H \<Sigma> G (named_paper_imp G ?A (named_paper_not ?E))"
    by (rule paper_R_named_H_negative_swap[OF rich el al instantiated])
  have eg: "paper_R_named_H \<Sigma> G (named_paper_imp G P ?E)"
    by (rule paper_R_named_H_ex_binder_instance[OF rich body variable rt])
  have contraposed: "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_not ?E) (named_paper_not P))"
    by (rule paper_R_named_H_contraposition[OF rich body el eg])
  have fresh_E: "u \<notin> named_fv (named_paper_not ?E)"
    by (simp add: named_paper_primitive_fv)
  have backward: "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_not ?E) ?A)"
    by (rule paper_R_named_H.Gen[OF contraposed variable fresh_E
      paper_R_named_paper_imp_language[OF rich nel al]])
  show ?thesis by (rule paper_R_named_H_iff_intro[OF rich al nel forward backward])
qed

end
