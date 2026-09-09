theory Bacon_Source_Relational_H_Theory_Substitution
  imports Bacon_Source_Relational_H_Theory_Universal_Closure
    Bacon_Source_Relational_Substitution_Syntax
begin

section \<open>Capture-free variable substitution in every H-theory\<close>

text \<open>
  If P belongs to an H-theory T, so does P[B/n] whenever B has
  the type of n and is free for n in P. First generalize P in the
  ORIGINAL T. Native UI gives (λn.P)B, and literal β followed by
  the forward biconditional consequence gives P[B/n].

  Source: Figure 2, p.8, and n.73's extension by fresh parameters.
  This is a derived closure property, not an extra substitution rule.
  No closure under replacement of old nonlogical constants, PE,
  C principle, local generalization or semantic premise is assumed.
\<close>

theorem paper_R_H_theory_substitution:
  assumes rich: "paper_R_rich G"
    and theory_h: "paper_R_H_theory \<Sigma> G T"
    and member: "P \<in> T"
    and payload: "paper_R_in_language \<Sigma> G B (G n)"
    and free_for: "named_free_for B n P"
  shows "named_subst n B P \<in> T"
proof -
  have pl: "paper_R_in_language \<Sigma> G P Prop"
    by (rule paper_R_H_theory_language[OF theory_h member])
  have nr: "paper_R_type (G n)"
    by (rule paper_R_language_result_type[OF payload])
  have predicate: "paper_R_in_language \<Sigma> G (NLam n P) (Arr (G n) Prop)"
    by (rule paper_R_named_identity_test_language[OF pl nr])
  have all_language: "paper_R_in_language \<Sigma> G (named_paper_all (G n) (NLam n P)) Prop"
    by (rule paper_R_named_all_binder_language[OF pl refl nr])
  have app_language: "paper_R_in_language \<Sigma> G (NApp (NLam n P) B) Prop"
    by (rule paper_R_language_App[OF predicate payload])
  have result_language: "paper_R_in_language \<Sigma> G (named_subst n B P) Prop"
    by (rule paper_R_subst_language_pure[OF pl payload])
  have generalized: "named_paper_all (G n) (NLam n P) \<in> T"
    by (rule paper_R_H_theory_generalize[OF rich theory_h member refl nr])
  have ui: "paper_R_named_H \<Sigma> G
      (named_paper_imp G (named_paper_all (G n) (NLam n P)) (NApp (NLam n P) B))"
    by (rule paper_R_named_H.UI[OF
      paper_R_named_paper_imp_language[OF rich all_language app_language]])
  have applied: "NApp (NLam n P) B \<in> T"
    by (rule paper_R_H_theory_MP[OF theory_h generalized
      paper_R_H_theory_H[OF theory_h ui] app_language])
  have root_step: "named_beta_contract (NApp (NLam n P) B) (named_subst n B P)"
    by (rule named_beta_contract.beta[OF free_for])
  have step: "named_compatible_step named_beta_contract
      (NApp (NLam n P) B) (named_subst n B P)"
    by (rule named_compatible_step.root[where R=named_beta_contract
      and M="NApp (NLam n P) B" and N="named_subst n B P", OF root_step])
  have beta: "paper_R_named_H \<Sigma> G
      (named_paper_iff G (NApp (NLam n P) B) (named_subst n B P))"
    by (rule paper_R_named_H.Beta[OF app_language result_language step
      paper_R_named_paper_iff_language[OF rich app_language result_language]])
  have forward: "paper_R_named_H \<Sigma> G
      (named_paper_imp G (NApp (NLam n P) B) (named_subst n B P))"
    by (rule paper_R_named_H.MP[OF beta
      paper_R_named_H_iff_forward[OF rich app_language result_language]
      paper_R_named_paper_imp_language[OF rich app_language result_language]])
  show ?thesis by (rule paper_R_H_theory_MP[OF theory_h applied
    paper_R_H_theory_H[OF theory_h forward] result_language])
qed

end
