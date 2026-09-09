theory Bacon_Source_Relational_Gen_Distribution_Proof
  imports Bacon_Source_Relational_Universal_Biconditionals Bacon_Source_Relational_Forall_Disjunction_Proof
begin

lemma paper_R_named_H_material_reverse_imp:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
  shows "paper_R_named_H \<Sigma> G (named_paper_iff G (named_paper_imp G A B) (named_paper_or B (named_paper_not A)))"
proof -
  have tautology: "sprop_tautology (SPIff (SPImp (SPAtom (0::nat)) (SPAtom 1)) (SPOr (SPAtom 1) (SPNot (SPAtom 0))))"
    by (auto simp: sprop_tautology_def)
  show ?thesis using paper_R_named_H_binary_PC[OF rich al bl tautology] by simp
qed

lemma paper_R_beta_all_or_self:
  "named_compatible_step named_beta_contract
    (named_paper_all \<sigma> (NLam u (named_paper_or (NApp (NLam u Q) (NVar u)) R)))
    (named_paper_all \<sigma> (NLam u (named_paper_or Q R)))"
proof -
  have contract: "named_beta_contract (NApp (NLam u Q) (NVar u)) Q"
    using named_beta_contract.beta[OF named_free_for_same_variable, where x=u and A=Q]
    by (simp only: named_subst_same_variable)
  have root_step: "named_compatible_step named_beta_contract (NApp (NLam u Q) (NVar u)) Q"
    by (rule named_compatible_step.root[where R=named_beta_contract and M="NApp (NLam u Q) (NVar u)" and N=Q, OF contract])
  show ?thesis unfolding named_paper_all_def named_paper_or_def
    by (rule named_compatible_step.App_right, rule named_compatible_step.Lam_body,
      rule named_compatible_step.App_left, rule named_compatible_step.App_right, rule root_step)
qed

section \<open>The exact H certificate used by the A.2 Gen step\<close>

text \<open>
  If u:σ is not free in P, H proves
  (P→∀u.Q) ↔ ∀u.(P→Q).
  Use Distribution-∨∀ with F=λu.Q and parameter ¬P, normalize
  (λu.Q)u by one actual contextual β step, and use native PC
  material-implication biconditionals. Ordinary H universal congruence
  transports the inner biconditional; no identity abstraction is used.
  Source: Appendix A.2, p.66. P and Q may be open, and the displayed
  implication and quantifier operators remain literal source terms.
\<close>

theorem paper_R_named_H_Gen_distribution:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>" and fresh: "u \<notin> named_fv P"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_iff G (named_paper_imp G P (named_paper_all \<sigma> (NLam u Q)))
      (named_paper_all \<sigma> (NLam u (named_paper_imp G P Q))))"
proof -
  let ?F = "NLam u Q"
  let ?N = "named_paper_not P"
  let ?All = "named_paper_all \<sigma> ?F"
  let ?A = "named_paper_imp G P ?All"
  let ?B = "named_paper_or ?All ?N"
  let ?Raw = "named_paper_all \<sigma> (NLam u (named_paper_or (NApp ?F (NVar u)) ?N))"
  let ?C = "named_paper_all \<sigma> (NLam u (named_paper_or Q ?N))"
  let ?D = "named_paper_all \<sigma> (NLam u (named_paper_imp G P Q))"
  have ur: "paper_R_type (G u)" by (simp only: variable; rule rt)
  have fl: "paper_R_in_language \<Sigma> G ?F (Arr \<sigma> Prop)"
    using paper_R_named_identity_test_language[OF ql ur] by (simp only: variable)
  have nl: "paper_R_in_language \<Sigma> G ?N Prop" by (rule paper_R_named_not_language[OF pl])
  have all_language: "paper_R_in_language \<Sigma> G ?All Prop" by (rule paper_R_predicate_all_language[OF fl])
  have al: "paper_R_in_language \<Sigma> G ?A Prop" by (rule paper_R_named_paper_imp_language[OF rich pl all_language])
  have bl: "paper_R_in_language \<Sigma> G ?B Prop" by (rule paper_R_named_or_language[OF all_language nl])
  have body: "paper_R_in_language \<Sigma> G (named_paper_or Q ?N) Prop" by (rule paper_R_named_or_language[OF ql nl])
  have implication: "paper_R_in_language \<Sigma> G (named_paper_imp G P Q) Prop" by (rule paper_R_named_paper_imp_language[OF rich pl ql])
  have cl: "paper_R_in_language \<Sigma> G ?C Prop" by (rule paper_R_named_all_binder_language[OF body variable rt])
  have dl: "paper_R_in_language \<Sigma> G ?D Prop" by (rule paper_R_named_all_binder_language[OF implication variable rt])
  have argument: "paper_R_in_language \<Sigma> G (NVar u) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=u, OF variable rt])
  have app_language: "paper_R_in_language \<Sigma> G (NApp ?F (NVar u)) Prop" by (rule paper_R_language_App[OF fl argument])
  have raw_language: "paper_R_in_language \<Sigma> G ?Raw Prop"
    by (rule paper_R_named_all_binder_language[OF paper_R_named_or_language[OF app_language nl] variable rt])
  have fresh_F: "u \<notin> named_fv ?F" by simp
  have fresh_N: "u \<notin> named_fv ?N" by (simp only: named_paper_primitive_fv; rule fresh)
  have distribution: "paper_R_named_H \<Sigma> G (named_paper_iff G ?Raw ?B)"
    by (rule paper_R_named_H_forall_or_distribution[OF rich fl nl variable fresh_F fresh_N])
  have reverse_distribution: "paper_R_named_H \<Sigma> G (named_paper_iff G ?B ?Raw)"
    by (rule paper_R_named_H_iff_sym[OF rich raw_language bl distribution])
  have beta_iff: "paper_R_named_H \<Sigma> G (named_paper_iff G ?Raw ?C)"
    by (rule paper_R_named_H.Beta[OF raw_language cl paper_R_beta_all_or_self
      paper_R_named_paper_iff_language[OF rich raw_language cl]])
  have bc: "paper_R_named_H \<Sigma> G (named_paper_iff G ?B ?C)"
    by (rule paper_R_named_H_iff_trans[OF rich bl raw_language cl reverse_distribution beta_iff])
  have material: "paper_R_named_H \<Sigma> G (named_paper_iff G (named_paper_imp G P Q) (named_paper_or Q ?N))"
    by (rule paper_R_named_H_material_reverse_imp[OF rich pl ql])
  have inner: "paper_R_named_H \<Sigma> G (named_paper_iff G (named_paper_or Q ?N) (named_paper_imp G P Q))"
    by (rule paper_R_named_H_iff_sym[OF rich implication body material])
  have cd: "paper_R_named_H \<Sigma> G (named_paper_iff G ?C ?D)"
    by (rule paper_R_named_H_all_binder_iff[OF rich body implication variable rt inner])
  have bd: "paper_R_named_H \<Sigma> G (named_paper_iff G ?B ?D)"
    by (rule paper_R_named_H_iff_trans[OF rich bl cl dl bc cd])
  have ab: "paper_R_named_H \<Sigma> G (named_paper_iff G ?A ?B)"
    by (rule paper_R_named_H_material_reverse_imp[OF rich pl all_language])
  show ?thesis by (rule paper_R_named_H_iff_trans[OF rich al bl dl ab bd])
qed

end
