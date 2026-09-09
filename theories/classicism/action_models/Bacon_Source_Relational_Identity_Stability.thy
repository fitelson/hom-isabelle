theory Bacon_Source_Relational_Identity_Stability
  imports Bacon_Source_Relational_H_Theory_Necessitation Bacon_Source_Relational_Application_Identity_Tests
begin

section \<open>The fresh LL predicate has literal capture-safe β instances\<close>

lemma paper_R_box_identity_test_beta:
  assumes fresh: "x \<notin> named_fv A"
  shows "named_compatible_step named_beta_contract
    (NApp (NLam x (paper_R_named_box G (named_paper_eq \<sigma> A (NVar x)))) B)
    (paper_R_named_box G (named_paper_eq \<sigma> A B))"
proof -
  have box_fresh: "x \<notin> named_fv (paper_R_named_box_const G)"
    by (simp only: paper_R_named_box_const_closed; simp)
  have free_box: "named_free_for B x (paper_R_named_box_const G)"
    by (rule named_free_for_fresh[OF box_fresh])
  have free_A: "named_free_for B x A" by (rule named_free_for_fresh[OF fresh])
  have fixed_box: "named_subst x B (paper_R_named_box_const G) = paper_R_named_box_const G"
    by (rule named_subst_fresh[OF box_fresh])
  have fixed_A: "named_subst x B A = A" by (rule named_subst_fresh[OF fresh])
  have free_for: "named_free_for B x (paper_R_named_box G (named_paper_eq \<sigma> A (NVar x)))"
    by (simp only: paper_R_named_box_def named_paper_eq_def named_free_for.simps free_box free_A; simp)
  have substitution: "named_subst x B (paper_R_named_box G (named_paper_eq \<sigma> A (NVar x))) =
    paper_R_named_box G (named_paper_eq \<sigma> A B)"
    by (simp only: paper_R_named_box_def named_paper_eq_def named_subst.simps fixed_box fixed_A; simp)
  have contract: "named_beta_contract
    (NApp (NLam x (paper_R_named_box G (named_paper_eq \<sigma> A (NVar x)))) B)
    (paper_R_named_box G (named_paper_eq \<sigma> A B))"
    using named_beta_contract.beta[OF free_for] by (simp only: substitution)
  show ?thesis by (rule named_compatible_step.root[where R=named_beta_contract
    and M="NApp (NLam x (paper_R_named_box G (named_paper_eq \<sigma> A (NVar x)))) B"
    and N="paper_R_named_box G (named_paper_eq \<sigma> A B)", OF contract])
qed

section \<open>Identities imply their own necessities in an H-theory closed under PE\<close>

text \<open>
  T contains A=σB → □(A=σB). First obtain □(A=σA)
  in the ORIGINAL T, using H's Ref and the proved conditional
  Necessitation theorem. Only then assume A=σB locally. LL with
  λx.□(A=σx), for a fresh x:σ, and literal β yield □(A=σB).
  Local deduction discharges A=σB, and T absorbs the consequence.
  Source: the identity-stability step in Theorem 3.12, p.52 n.73.

  Necessitation is never applied to the temporary assumption or to an
  enlarged theory. A and B may be open. The internal Box binder is
  protected by closedness and the exact free-for vacuity condition;
  no global binder-avoidance shortcut, ζ, C, model, or semantic
  necessity principle is assumed.
\<close>

theorem paper_R_H_theory_identity_stability:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T"
    and al: "paper_R_in_language \<Sigma> G A \<sigma>" and bl: "paper_R_in_language \<Sigma> G B \<sigma>"
  shows "named_paper_imp G (named_paper_eq \<sigma> A B) (paper_R_named_box G (named_paper_eq \<sigma> A B)) \<in> T"
proof -
  let ?E = "named_paper_eq \<sigma> A B"
  let ?R = "named_paper_eq \<sigma> A A"
  have el: "paper_R_in_language \<Sigma> G ?E Prop" by (rule paper_R_named_identity_language[OF al bl])
  have rl: "paper_R_in_language \<Sigma> G ?R Prop" by (rule paper_R_named_identity_language[OF al al])
  have ref_H: "paper_R_named_H \<Sigma> G ?R" by (rule paper_R_named_H.Ref[OF rl])
  have ref_T: "?R \<in> T" by (rule paper_R_H_theory_H[OF theory_h ref_H])
  have boxed_ref_T: "paper_R_named_box G ?R \<in> T"
    by (rule paper_R_H_theory_necessitation[OF rich theory_h pe ref_T])
  have rt: "paper_R_type \<sigma>" by (rule paper_R_language_result_type[OF al])
  have finite: "finite (named_vars A \<union> named_vars B)" by (rule finite_UnI[OF named_vars_finite named_vars_finite])
  obtain x where xt: "G x = \<sigma>" and avoids: "x \<notin> named_vars A \<union> named_vars B"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>=\<sigma>, OF rich rt finite])
  have fresh: "x \<notin> named_fv A" using avoids named_fv_subset_vars[of A] by blast
  have variable: "paper_R_in_language \<Sigma> G (NVar x) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=x, OF xt rt])
  let ?Test = "NLam x (paper_R_named_box G (named_paper_eq \<sigma> A (NVar x)))"
  have body: "paper_R_in_language \<Sigma> G (paper_R_named_box G (named_paper_eq \<sigma> A (NVar x))) Prop"
    by (rule paper_R_named_box_language[OF rich paper_R_named_identity_language[OF al variable]])
  have xr: "paper_R_type (G x)" by (simp only: xt; rule rt)
  have predicate: "paper_R_in_language \<Sigma> G ?Test (Arr \<sigma> Prop)"
    using paper_R_named_identity_test_language[OF body xr] by (simp only: xt)
  have brl: "paper_R_in_language \<Sigma> G (paper_R_named_box G ?R) Prop" by (rule paper_R_named_box_language[OF rich rl])
  have bel: "paper_R_in_language \<Sigma> G (paper_R_named_box G ?E) Prop" by (rule paper_R_named_box_language[OF rich el])
  have first_step: "named_compatible_step named_beta_contract (NApp ?Test A) (paper_R_named_box G ?R)"
    by (rule paper_R_box_identity_test_beta[OF fresh])
  have second_step: "named_compatible_step named_beta_contract (NApp ?Test B) (paper_R_named_box G ?E)"
    by (rule paper_R_box_identity_test_beta[OF fresh])
  have temporary: "paper_R_named_derivable \<Sigma> G (insert ?E T) ?E"
    by (rule paper_R_named_derivable.Assumption; (rule insertI1 | rule el))
  have initial: "paper_R_named_derivable \<Sigma> G (insert ?E T) (paper_R_named_box G ?R)"
    by (rule paper_R_named_derivable.Assumption; (rule insertI2[OF boxed_ref_T] | rule brl))
  have local_result: "paper_R_named_derivable \<Sigma> G (insert ?E T) (paper_R_named_box G ?E)"
    by (rule paper_R_named_derivable_LL_beta[OF rich al bl predicate brl bel first_step second_step temporary initial])
  have discharged: "paper_R_named_derivable \<Sigma> G T (named_paper_imp G ?E (paper_R_named_box G ?E))"
    by (rule paper_R_named_derivable_deduction[OF rich el local_result])
  show ?thesis by (rule paper_R_H_theory_local_consequences[OF theory_h discharged subset_refl])
qed

end
