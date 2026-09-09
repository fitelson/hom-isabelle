theory Bacon_Source_BBK_Reverse_Quantifiers
  imports Bacon_Source_BBK_Binding Bacon_Source_Reverse_Syntax
begin

section \<open>A source abstraction applied to the fresh slot β-reduces to its body\<close>

text \<open>
  The term (λx.A) applied to the fresh x, with the abstraction shifted
  beneath that slot, β-reduces to A.  All terms retain their type and
  membership in ℒ(Σ).  Source: Bacon--Dorr Figure 2 β, pp.7–8.
  Isabelle representation.  paper_db_beta_slot_restore performs the
  de Bruijn cancellation; this preliminary conversion has no model premise.
\<close>

lemma paper_db_fresh_lambda_beta:
  assumes body: "sterm_in_language paper_logical_type \<Sigma> (\<sigma> # \<Gamma>) A \<tau>"
  shows "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> (\<sigma> # \<Gamma>) \<tau>
    (SApp (sshift (SLam \<sigma> A)) (SVar 0)) A"
proof -
  have abstraction: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SLam \<sigma> A) (Arr \<sigma> \<tau>)"
    by (rule paper_db_lam_language[OF body])
  have shifted: "sterm_in_language paper_logical_type \<Sigma> (\<sigma> # \<Gamma>)
    (sshift (SLam \<sigma> A)) (Arr \<sigma> \<tau>)"
    by (rule paper_db_shift_language[OF abstraction])
  have variable: "sterm_in_language paper_logical_type \<Sigma> (\<sigma> # \<Gamma>) (SVar 0) \<sigma>"
    unfolding sterm_in_language_def by (rule conjI) (rule has_stype.Var[OF lookup_Cons_0], simp)
  have source: "sterm_in_language paper_logical_type \<Sigma> (\<sigma> # \<Gamma>)
    (SApp (sshift (SLam \<sigma> A)) (SVar 0)) \<tau>"
    by (rule paper_db_app_language[OF shifted variable])
  have step: "scompatible_step sbeta_contract (SApp (sshift (SLam \<sigma> A)) (SVar 0)) A"
  proof -
    have "scompatible_step sbeta_contract
      (SApp (SLam \<sigma> (srename (lift_ren Suc) A)) (SVar 0))
      (ssubst0 (SVar 0) (srename (lift_ren Suc) A))"
      by (rule scompatible_step.root[where R=sbeta_contract]) (rule sbeta_contract.beta)
    then show ?thesis by (simp add: sshift_def paper_db_beta_slot_restore)
  qed
  note source_parts = source[unfolded sterm_in_language_def]
  note body_parts = body[unfolded sterm_in_language_def]
  show ?thesis by (rule sbeta_eta_equiv_in_signature.Beta[OF
    conjunct1[OF source_parts] conjunct1[OF body_parts]
    conjunct2[OF source_parts] conjunct2[OF body_parts] step])
qed

context paper_db_bbk_structure
begin

section \<open>First-class quantifier truth specializes to the binder clauses\<close>

text \<open>
  M,g ⊨ ∀σ(λx.A) iff M,g[x ↦ a] ⊨ A for every a ∈ Dσ;
  the existential clause uses some a ∈ Dσ.
  Source: Bacon--Dorr Definition 3.1(iii.d–e), pp.43–44.

  Isabelle representation.  The structure's arbitrary-predicate clauses
  give a fresh-variable application.  Its guarded β interpretation
  identifies that application with the body at each typed extended
  environment.
  Status.  These results use the weaker finite-frame structure directly:
  no target model, optional renaming field, Functionality, or named-model
  correspondence is assumed.
\<close>

lemma paper_db_fresh_lambda_denote:
  assumes body: "sterm_in_language paper_logical_type signature (\<sigma> # \<Gamma>) A \<tau>"
    and env: "pbbk_env_typed domain (\<sigma> # \<Gamma>) h"
  shows "denote h (SApp (sshift (SLam \<sigma> A)) (SVar 0)) = denote h A"
  by (rule denote_beta_eta[OF paper_db_fresh_lambda_beta[OF body] env])

theorem paper_db_forall_body:
  assumes body: "sterm_in_language paper_logical_type signature (\<sigma> # \<Gamma>) A Prop"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> A))) =
    (\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) A))"
proof -
  have predicate: "sterm_in_language paper_logical_type signature \<Gamma> (SLam \<sigma> A) (Arr \<sigma> Prop)"
    by (rule paper_db_lam_language[OF body])
  have expanded: "valuation (denote g (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> A))) =
    (\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) (SApp (sshift (SLam \<sigma> A)) (SVar 0))))"
    by (rule valuation_forall[OF predicate env])
  have bodies: "(\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g)
      (SApp (sshift (SLam \<sigma> A)) (SVar 0)))) =
    (\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) A))"
  proof (rule ball_cong[OF refl])
    fix a
    assume member: "a \<in> domain \<sigma>"
    have extended: "pbbk_env_typed domain (\<sigma> # \<Gamma>) (pbbk_extend a g)"
      by (rule pbbk_env_extend[OF env member])
    show "valuation (denote (pbbk_extend a g) (SApp (sshift (SLam \<sigma> A)) (SVar 0))) =
      valuation (denote (pbbk_extend a g) A)"
      by (simp only: paper_db_fresh_lambda_denote[OF body extended])
  qed
  show ?thesis by (rule trans[OF expanded bodies])
qed

theorem paper_db_exists_body:
  assumes body: "sterm_in_language paper_logical_type signature (\<sigma> # \<Gamma>) A Prop"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> A))) =
    (\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) A))"
proof -
  have predicate: "sterm_in_language paper_logical_type signature \<Gamma> (SLam \<sigma> A) (Arr \<sigma> Prop)"
    by (rule paper_db_lam_language[OF body])
  have expanded: "valuation (denote g (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> A))) =
    (\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) (SApp (sshift (SLam \<sigma> A)) (SVar 0))))"
    by (rule valuation_exists[OF predicate env])
  have bodies: "(\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g)
      (SApp (sshift (SLam \<sigma> A)) (SVar 0)))) =
    (\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) A))"
  proof (rule bex_cong[OF refl])
    fix a
    assume member: "a \<in> domain \<sigma>"
    have extended: "pbbk_env_typed domain (\<sigma> # \<Gamma>) (pbbk_extend a g)"
      by (rule pbbk_env_extend[OF env member])
    show "valuation (denote (pbbk_extend a g) (SApp (sshift (SLam \<sigma> A)) (SVar 0))) =
      valuation (denote (pbbk_extend a g) A)"
      by (simp only: paper_db_fresh_lambda_denote[OF body extended])
  qed
  show ?thesis by (rule trans[OF expanded bodies])
qed

subsection \<open>The corresponding clauses for reverse-translated target syntax\<close>

corollary paper_db_reverse_forall:
  assumes body: "pterm_in_language signature (\<sigma> # \<Gamma>) A Prop"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (pterm_to_paper (PForall \<sigma> A))) =
    (\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) (pterm_to_paper A)))"
  using paper_db_forall_body[OF pterm_to_paper_language[OF body] env]
  by (simp only: pterm_to_paper.simps)

corollary paper_db_reverse_exists:
  assumes body: "pterm_in_language signature (\<sigma> # \<Gamma>) A Prop"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (pterm_to_paper (PExists \<sigma> A))) =
    (\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) (pterm_to_paper A)))"
  using paper_db_exists_body[OF pterm_to_paper_language[OF body] env]
  by (simp only: pterm_to_paper.simps)

end

end
