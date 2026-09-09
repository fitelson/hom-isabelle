theory Bacon_Source_Named_Binder_Conversion
  imports Bacon_Source_Named_Conversion_Contexts
begin

section \<open>Changing a binder by η expansion and literal β\<close>

text \<open>
  λx.A ≡βη λy.A[y/x] when G(x) = G(y) and y ∉ Vars(A).
  Source: Bacon–Dorr Figure 2, p.8, with its contextual convention on
  p.7. The intermediate term is λy.((λx.A)y).

  Isabelle representation. The inner β contraction uses literal
  named_subst and the proved named_free_for condition. The outer λy
  deliberately binds the inserted occurrence of y, as the source permits
  Φ[−] to bind free variables of the replaced term. No outer-context
  freshness condition is added.

  Status. Every node has its common type and declared signature.
  Only β, η, symmetry, transitivity, and abstraction congruence are used;
  no α rule, representation equation, or semantic assumption is used.
\<close>

lemma named_fresh_variable_free_for:
  assumes fresh: "y \<notin> named_vars A"
  shows "named_free_for (NVar y) x A"
  using fresh by (induction A) auto

lemma named_conversion_variable_language:
  "named_in_language L \<Sigma> G (NVar n) (G n)"
  unfolding named_in_language_def
  by (rule conjI; (rule has_ntype.Var | simp only: named_in_signature.simps))

lemma named_conversion_swap_language:
  assumes language: "named_in_language L \<Sigma> G A \<tau>" and same: "G x = G y"
  shows "named_in_language L \<Sigma> G (named_swap x y A) \<tau>"
proof -
  have typed: "has_ntype L G A \<tau>" and sig: "named_in_signature \<Sigma> A"
    using language unfolding named_in_language_def by blast+
  have swapped: "has_ntype L G (named_swap x y A) \<tau>"
    by (rule named_swap_type[OF same typed])
  show ?thesis unfolding named_in_language_def
    by (rule conjI[OF swapped]) (simp only: named_swap_signature sig)
qed

lemma named_binder_literal_rename:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
    and same: "G x = G y" and fresh: "y \<notin> named_vars A"
  shows "named_beta_eta_in_language L \<Sigma> G (Arr (G x) \<tau>)
    (NLam x A) (NLam y (named_subst x (NVar y) A))"
proof -
  let ?F = "NLam x A"
  let ?R = "NApp ?F (NVar y)"
  let ?S = "named_subst x (NVar y) A"
  have variable: "named_in_language L \<Sigma> G (NVar y) (G x)"
    using named_conversion_variable_language[where L=L and \<Sigma>=\<Sigma> and G=G and n=y]
    by (simp only: same)
  have fn: "named_in_language L \<Sigma> G ?F (Arr (G x) \<tau>)"
    by (rule named_language_Lam[OF language])
  have redex: "named_in_language L \<Sigma> G ?R \<tau>"
    by (rule named_language_App[OF fn variable])
  have expanded: "named_in_language L \<Sigma> G (NLam y ?R) (Arr (G x) \<tau>)"
    using named_language_Lam[where n=y, OF redex] by (simp only: same)
  have substituted: "named_in_language L \<Sigma> G ?S \<tau>"
    by (rule named_subst_language[OF language variable])
  have not_free: "y \<notin> named_fv ?F"
    using fresh named_fv_subset_vars[where A=A] by auto
  have eta_root: "named_eta_contract (NLam y ?R) ?F"
    by (rule named_eta_contract.eta[OF not_free])
  have eta_step: "named_compatible_step named_eta_contract (NLam y ?R) ?F"
    by (rule named_compatible_step.root[where R=named_eta_contract
      and M="NLam y ?R" and N="?F", OF eta_root])
  have eta: "named_beta_eta_in_language L \<Sigma> G (Arr (G x) \<tau>) (NLam y ?R) ?F"
    by (rule named_beta_eta_in_language.Eta[OF expanded fn eta_step])
  have free_for: "named_free_for (NVar y) x A"
    by (rule named_fresh_variable_free_for[OF fresh])
  have beta_root: "named_beta_contract ?R ?S"
    by (rule named_beta_contract.beta[OF free_for])
  have beta_step: "named_compatible_step named_beta_contract ?R ?S"
    by (rule named_compatible_step.root[where R=named_beta_contract
      and M="?R" and N="?S", OF beta_root])
  have beta: "named_beta_eta_in_language L \<Sigma> G \<tau> ?R ?S"
    by (rule named_beta_eta_in_language.Beta[OF redex substituted beta_step])
  have under_binder: "named_beta_eta_in_language L \<Sigma> G (Arr (G x) \<tau>)
    (NLam y ?R) (NLam y ?S)"
    using named_conversion_Lam[where n=y, OF beta] by (simp only: same)
  show ?thesis
    by (rule named_beta_eta_in_language.Trans[OF named_beta_eta_in_language.Sym[OF eta] under_binder])
qed

lemma named_binder_conversion_from_alignment:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
    and same: "G x = G y" and fresh: "y \<notin> named_vars A"
    and alignment: "named_beta_eta_in_language L \<Sigma> G \<tau>
      (named_subst x (NVar y) A) (named_swap x y A)"
  shows "named_beta_eta_in_language L \<Sigma> G (Arr (G x) \<tau>)
    (NLam x A) (NLam y (named_swap x y A))"
proof -
  have literal: "named_beta_eta_in_language L \<Sigma> G (Arr (G x) \<tau>)
    (NLam x A) (NLam y (named_subst x (NVar y) A))"
    by (rule named_binder_literal_rename[OF language same fresh])
  have aligned: "named_beta_eta_in_language L \<Sigma> G (Arr (G x) \<tau>)
    (NLam y (named_subst x (NVar y) A)) (NLam y (named_swap x y A))"
    using named_conversion_Lam[where n=y, OF alignment] by (simp only: same)
  show ?thesis by (rule named_beta_eta_in_language.Trans[OF literal aligned])
qed

end
