theory Bacon_Source_Relational_Global_Abstraction_Beta
  imports Bacon_Source_Relational_H_Theory_Substitution
    Bacon_Source_Relational_Conversion_Identity_Steps
begin

section \<open>Fresh variable tests of typed abstractions have native H identity certificates\<close>

lemma paper_R_global_abstraction_language:
  assumes body: "paper_R_in_language \<Sigma> G A \<tau>"
    and nr: "paper_R_type (G n)" and result: "\<tau> \<noteq> Ind"
  shows "paper_R_in_language \<Sigma> G (NLam n A) (Arr (G n) \<tau>)"
  using body nr result unfolding paper_R_in_language_def
  by (auto intro: paper_R_has_type.Lam)

lemma paper_R_global_abstraction_variable_free_for:
  assumes fresh: "v \<notin> named_vars A"
  shows "named_free_for (NVar v) n A"
  using fresh by (induction A) auto

theorem paper_R_named_H_fresh_abstraction_beta_identity:
  assumes rich: "paper_R_rich G"
    and body: "paper_R_in_language \<Sigma> G A \<tau>"
    and nr: "paper_R_type (G n)" and result: "\<tau> \<noteq> Ind"
    and variable: "G v = G n" and fresh: "v \<notin> named_vars A"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_eq \<tau> (NApp (NLam n A) (NVar v)) (named_subst n (NVar v) A))"
proof -
  have vl: "paper_R_in_language \<Sigma> G (NVar v) (G n)"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=v, OF variable nr])
  have abstraction: "paper_R_in_language \<Sigma> G (NLam n A) (Arr (G n) \<tau>)"
    by (rule paper_R_global_abstraction_language[OF body nr result])
  have left: "paper_R_in_language \<Sigma> G (NApp (NLam n A) (NVar v)) \<tau>"
    by (rule paper_R_language_App[OF abstraction vl])
  have right: "paper_R_in_language \<Sigma> G (named_subst n (NVar v) A) \<tau>"
    by (rule paper_R_subst_language_pure[OF body vl])
  have free_for: "named_free_for (NVar v) n A"
    by (rule paper_R_global_abstraction_variable_free_for[OF fresh])
  have contraction: "named_beta_contract (NApp (NLam n A) (NVar v)) (named_subst n (NVar v) A)"
    by (rule named_beta_contract.beta[OF free_for])
  have step: "named_compatible_step named_beta_contract
      (NApp (NLam n A) (NVar v)) (named_subst n (NVar v) A)"
    by (rule named_compatible_step.root[where R=named_beta_contract
      and M="NApp (NLam n A) (NVar v)" and N="named_subst n (NVar v) A", OF contraction])
  show ?thesis by (rule paper_R_named_H_beta_identity[OF rich left right step])
qed

text \<open>
  All-type identity is derived from the formula-level β schema and
  Ref through the already proved native certificate theorem. The test
  variable avoids every binder in A, ensuring literal free-for.
  No semantic conversion principle or new all-type β axiom is assumed.
  Source: Figure 2 and the theorem-level ζ argument of pp.14–16.
\<close>

end
