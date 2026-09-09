theory Bacon_Source_Relational_Application_Identity_Tests
  imports Bacon_Source_Relational_Identity_Derivations
begin

section \<open>Typed λ tests and native LL followed by literal β\<close>

lemma paper_R_named_identity_test_language:
  assumes body: "paper_R_in_language \<Sigma> G P Prop" and binder_type: "paper_R_type (G n)"
  shows "paper_R_in_language \<Sigma> G (NLam n P) (Arr (G n) Prop)"
proof -
  have bt: "paper_R_has_type G P Prop" and names: "named_in_signature \<Sigma> P"
    using body unfolding paper_R_in_language_def by blast+
  have lt: "paper_R_has_type G (NLam n P) (Arr (G n) Prop)"
    by (rule paper_R_has_type.Lam[OF bt binder_type]; simp)
  show ?thesis using lt names by (simp add: paper_R_in_language_def)
qed

lemma paper_R_named_derivable_LL_beta:
  assumes rich: "paper_R_rich G" and left: "paper_R_in_language \<Sigma> G A \<sigma>"
    and right: "paper_R_in_language \<Sigma> G B \<sigma>"
    and predicate: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
    and xl: "paper_R_in_language \<Sigma> G X Prop" and yl: "paper_R_in_language \<Sigma> G Y Prop"
    and first_step: "named_compatible_step named_beta_contract (NApp F A) X"
    and second_step: "named_compatible_step named_beta_contract (NApp F B) Y"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
    and initial: "paper_R_named_derivable \<Sigma> G S X"
  shows "paper_R_named_derivable \<Sigma> G S Y"
proof -
  have fa: "paper_R_in_language \<Sigma> G (NApp F A) Prop" by (rule paper_R_language_App[OF predicate left])
  have fb: "paper_R_in_language \<Sigma> G (NApp F B) Prop" by (rule paper_R_language_App[OF predicate right])
  have first: "paper_R_named_derivable \<Sigma> G S (NApp F A)"
    by (rule iffD2[OF paper_R_named_derivable_beta_iff[OF rich fa xl first_step] initial])
  have second: "paper_R_named_derivable \<Sigma> G S (NApp F B)"
    by (rule paper_R_named_derivable_LL[OF rich left right predicate equality first])
  show ?thesis by (rule iffD1[OF paper_R_named_derivable_beta_iff[OF rich fb yl second_step] second])
qed

section \<open>The two raw application tests have explicit no-capture proofs\<close>

text \<open>
  (λn.L=τF n)A →β L=τF A, and
  (λn.L=τn A)F →β L=τF A.
  Only the fixed terms of each predicate must be fresh for n.
  The inserted payload may itself mention n: no remaining binder
  surrounds its insertion site. Source: Figure 2, p.8.
\<close>

lemma paper_R_identity_argument_test_beta:
  assumes fresh_left: "n \<notin> named_fv L" and fresh_head: "n \<notin> named_fv F"
  shows "named_compatible_step named_beta_contract
    (NApp (NLam n (named_paper_eq \<tau> L (NApp F (NVar n)))) A)
    (named_paper_eq \<tau> L (NApp F A))"
proof -
  have left_free: "named_free_for A n L" by (rule named_free_for_fresh[OF fresh_left])
  have head_free: "named_free_for A n F" by (rule named_free_for_fresh[OF fresh_head])
  have free_for: "named_free_for A n (named_paper_eq \<tau> L (NApp F (NVar n)))"
    by (simp add: named_paper_eq_def left_free head_free)
  have substitution: "named_subst n A (named_paper_eq \<tau> L (NApp F (NVar n))) =
    named_paper_eq \<tau> L (NApp F A)"
    by (simp add: named_paper_eq_def named_subst_fresh[OF fresh_left] named_subst_fresh[OF fresh_head])
  have contract: "named_beta_contract (NApp (NLam n (named_paper_eq \<tau> L (NApp F (NVar n)))) A)
    (named_paper_eq \<tau> L (NApp F A))"
    using named_beta_contract.beta[OF free_for] by (simp only: substitution)
  show ?thesis by (rule named_compatible_step.root[where R=named_beta_contract
    and M="NApp (NLam n (named_paper_eq \<tau> L (NApp F (NVar n)))) A"
    and N="named_paper_eq \<tau> L (NApp F A)", OF contract])
qed

lemma paper_R_identity_head_test_beta:
  assumes fresh_left: "n \<notin> named_fv L" and fresh_argument: "n \<notin> named_fv A"
  shows "named_compatible_step named_beta_contract
    (NApp (NLam n (named_paper_eq \<tau> L (NApp (NVar n) A))) F)
    (named_paper_eq \<tau> L (NApp F A))"
proof -
  have left_free: "named_free_for F n L" by (rule named_free_for_fresh[OF fresh_left])
  have argument_free: "named_free_for F n A" by (rule named_free_for_fresh[OF fresh_argument])
  have free_for: "named_free_for F n (named_paper_eq \<tau> L (NApp (NVar n) A))"
    by (simp add: named_paper_eq_def left_free argument_free)
  have substitution: "named_subst n F (named_paper_eq \<tau> L (NApp (NVar n) A)) =
    named_paper_eq \<tau> L (NApp F A)"
    by (simp add: named_paper_eq_def named_subst_fresh[OF fresh_left] named_subst_fresh[OF fresh_argument])
  have contract: "named_beta_contract (NApp (NLam n (named_paper_eq \<tau> L (NApp (NVar n) A))) F)
    (named_paper_eq \<tau> L (NApp F A))"
    using named_beta_contract.beta[OF free_for] by (simp only: substitution)
  show ?thesis by (rule named_compatible_step.root[where R=named_beta_contract
    and M="NApp (NLam n (named_paper_eq \<tau> L (NApp (NVar n) A))) F"
    and N="named_paper_eq \<tau> L (NApp F A)", OF contract])
qed

end
