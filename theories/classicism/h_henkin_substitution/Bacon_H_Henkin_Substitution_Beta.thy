theory Bacon_H_Henkin_Substitution_Beta
  imports Bacon_H_Henkin_Substitution_Basics
begin

section \<open>Beta decomposition for closed simultaneous substitutions\<close>

text \<open>
  (λx.M)[s₁,s₂,…] s₀ ∼ₜ M[s₀,s₁,…]. Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon,
  Theorem 15.3, pp. 320–321.

  Isabelle representation: The source substitution is a type-respecting map into
  closed terms. The proof checks the abstraction, head argument, and β-contractum
  before applying identity conversion.

  Status: The identity-level decomposition is proved; the following theory combines it
  with context induction.
\<close>

context H_closed_Henkin
begin

lemma H_term_eq_substitution_beta:
  assumes typed: "\<sigma> # \<Gamma> \<turnstile> M : \<tau>"
    and s_typed: "term_subst_typed (\<sigma> # \<Gamma>) [] s"
  shows "H_term_eq \<tau>
    (App (subst (\<lambda>n. s (Suc n)) (Lam \<sigma> M)) (s 0)) (subst s M)"
proof -
  let ?tail = "\<lambda>n. s (Suc n)"
  have head_type: "[] \<turnstile> s 0 : \<sigma>"
    using s_typed by (rule H_closed_substitution_head_type)
  have tail_type: "term_subst_typed \<Gamma> [] ?tail"
    using s_typed by (rule H_closed_substitution_tail_type)
  have lam_type: "\<Gamma> \<turnstile> Lam \<sigma> M : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using typed by (rule has_type.Lam)
  have fun_type: "[] \<turnstile> subst ?tail (Lam \<sigma> M) : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using lam_type tail_type by (rule term_subst_preserves_typing)
  have app_type: "[] \<turnstile> App (subst ?tail (Lam \<sigma> M)) (s 0) : \<tau>"
    using fun_type head_type by (rule has_type.App)
  have result_type: "[] \<turnstile> subst s M : \<tau>"
    using typed s_typed by (rule term_subst_preserves_typing)
  have root: "compatible_step beta_contract
      (App (Lam \<sigma> (subst (lift_subst ?tail) M)) (s 0))
      (subst0 (s 0) (subst (lift_subst ?tail) M))"
    by (intro compatible_step.root beta_contract.beta)
  have step: "compatible_step beta_contract
      (App (subst ?tail (Lam \<sigma> M)) (s 0)) (subst s M)"
    using root
    by (simp only: subst.simps H_substitution_head_tail[where s=s and M=M])
  have conversion: "beta_eta_equiv [] \<tau>
      (App (subst ?tail (Lam \<sigma> M)) (s 0)) (subst s M)"
    using app_type result_type step by (rule beta_eta_equiv.Beta)
  show ?thesis using conversion by (rule H_term_eq_beta_eta)
qed

lemma H_term_eq_substitution_head:
  assumes pointwise: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      H_term_eq \<rho> (s n) (r n)"
  shows "H_term_eq \<sigma> (s 0) (r 0)"
  by (rule pointwise) simp

lemma H_term_eq_substitution_tail:
  assumes pointwise: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      H_term_eq \<rho> (s n) (r n)"
    and lookup: "lookup \<Gamma> n = Some \<rho>"
  shows "H_term_eq \<rho> (s (Suc n)) (r (Suc n))"
  using lookup by (intro pointwise) simp

end
end
