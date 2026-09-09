theory Bacon_Source_BBK_Binding
  imports Bacon_Source_BBK_Interface Bacon_Source_Closing_Structure Bacon_Source_Global_Substitution
begin

section \<open>Language guards for source binder operations\<close>

text \<open>
  If A:τ in the context x:σ,Γ and T:σ in Γ, both terms in ℒ(Σ),
  then (λx.A)T and A[T/x] are Γ-terms of type τ in the same language.
  Source: Bacon--Dorr §1.1 and Figure 2, pp.5–8.
  Isabelle representation.  These preliminary lemmas concern only source
  syntax, signature membership, and finite-context typing.
  Status.  No interpretation or semantic substitution law is assumed here.
\<close>

lemma paper_db_ssubst_signature:
  assumes body: "sterm_in_signature \<Sigma> A"
    and replacements: "\<And>n. sterm_in_signature \<Sigma> (s n)"
  shows "sterm_in_signature \<Sigma> (ssubst s A)"
  using body replacements
proof (induction A arbitrary: s)
  case SVar
  show ?case using SVar.prems(2) by simp
next
  case SConst
  show ?case using SConst.prems(1) by simp
next
  case SLogical
  show ?case by simp
next
  case (SApp M N)
  have M: "sterm_in_signature \<Sigma> M" and N: "sterm_in_signature \<Sigma> N"
    using SApp.prems(1) by simp_all
  show ?case using SApp.IH(1)[OF M SApp.prems(2)] SApp.IH(2)[OF N SApp.prems(2)] by simp
next
  case (SLam \<sigma> A)
  have A: "sterm_in_signature \<Sigma> A" using SLam.prems(1) by simp
  have lifted: "\<And>n. sterm_in_signature \<Sigma> (slift_subst s n)"
    using SLam.prems(2) by (case_tac n) (simp_all add: srename_signature)
  show ?case using SLam.IH[OF A lifted] by simp
qed

lemma paper_db_ssubst0_signature:
  assumes body: "sterm_in_signature \<Sigma> A" and argument: "sterm_in_signature \<Sigma> T"
  shows "sterm_in_signature \<Sigma> (ssubst0 T A)"
  unfolding ssubst0_def
  by (rule paper_db_ssubst_signature[OF body]) (case_tac n; simp add: argument)

lemma paper_db_lam_language:
  assumes body: "sterm_in_language paper_logical_type \<Sigma> (\<sigma> # \<Gamma>) A \<tau>"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SLam \<sigma> A) (Arr \<sigma> \<tau>)"
  using body unfolding sterm_in_language_def by (auto intro: has_stype.Lam)

lemma paper_db_app_language:
  assumes F: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> \<tau>)"
    and A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp F A) \<tau>"
  using F A unfolding sterm_in_language_def by (auto intro: has_stype.App)

lemma paper_db_shift_language:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<tau>"
  shows "sterm_in_language paper_logical_type \<Sigma> (\<sigma> # \<Gamma>) (sshift A) \<tau>"
proof -
  have typed: "has_stype paper_logical_type \<Gamma> A \<tau>"
    using A unfolding sterm_in_language_def by (rule conjunct1)
  have names: "sterm_in_signature \<Sigma> A"
    using A unfolding sterm_in_language_def by (rule conjunct2)
  have shifted_names: "sterm_in_signature \<Sigma> (sshift A)"
    using names by (simp only: sshift_def srename_signature)
  show ?thesis unfolding sterm_in_language_def
    by (rule conjI[OF sshift_preserves_typing[OF typed] shifted_names])
qed

lemma paper_db_subst0_language:
  assumes body: "sterm_in_language paper_logical_type \<Sigma> (\<sigma> # \<Gamma>) A \<tau>"
    and argument: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> T \<sigma>"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (ssubst0 T A) \<tau>"
proof -
  note A = body[unfolded sterm_in_language_def]
  note T = argument[unfolded sterm_in_language_def]
  show ?thesis unfolding sterm_in_language_def
    by (rule conjI[OF ssubst0_preserves_typing[OF conjunct1[OF A] conjunct1[OF T]]
      paper_db_ssubst0_signature[OF conjunct2[OF A] conjunct2[OF T]]])
qed

lemma paper_db_beta_slot_restore:
  "ssubst0 (SVar 0) (srename (lift_ren Suc) A) = A"
  unfolding ssubst0_def
  by (rule ssubst_srename_inverse) (case_tac n; simp)

context paper_db_bbk_model
begin

section \<open>Shift coherence, guarded β interpretation, and one-binder substitution\<close>

text \<open>
  ⟦A↑⟧ᵍ[x↦a] = ⟦A⟧ᵍ follows from the explicit de Bruijn coherence
  field.  Guarded β then gives ⟦(λx.A)T⟧ᵍ = ⟦A[T/x]⟧ᵍ.
  Comparing that application with (λx.A) applied to the fresh variable
  under g[x ↦ ⟦T⟧ᵍ] yields the one-binder substitution equation.

  Isabelle representation.  pbbk_extend inserts slot zero.  The
  application clause compares two typed assignments, while the conversion
  clause applies only to signature-guarded source βη derivations.
  Status.  These are conditional consequences of paper_db_bbk_model,
  including its separately stated renaming-coherence field. The later
  paper_db_structure_is_model theorem derives that field from the weaker
  finite-frame structure, so it imposes no extra model restriction.
  The statements here are unchanged. No model is constructed in this leaf,
  and no correspondence with adequate named assignments, Γ-erasure, or
  the book's distinct general-model semantics is asserted.
\<close>

lemma paper_db_shift_assignment:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> A \<tau>"
    and env: "pbbk_env_typed domain \<Gamma> g" and member: "a \<in> domain \<sigma>"
  shows "denote (pbbk_extend a g) (sshift A) = denote g A"
proof -
  have extended: "pbbk_env_typed domain (\<sigma> # \<Gamma>) (pbbk_extend a g)"
    by (rule pbbk_env_extend[OF env member])
  have injection: "inj Suc" by (rule injI) simp
  have renaming: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> lookup (\<sigma> # \<Gamma>) (Suc n) = Some \<rho>"
    by simp
  have equality: "denote (pbbk_extend a g) (srename Suc A) =
    denote (\<lambda>n. pbbk_extend a g (Suc n)) A"
    by (rule denote_rename[OF language injection extended renaming])
  show ?thesis using equality by (simp only: sshift_def pbbk_extend_Suc)
qed

lemma paper_db_denote_beta:
  assumes body: "sterm_in_language paper_logical_type signature (\<sigma> # \<Gamma>) A \<tau>"
    and argument: "sterm_in_language paper_logical_type signature \<Gamma> T \<sigma>"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "denote g (SApp (SLam \<sigma> A) T) = denote g (ssubst0 T A)"
proof -
  have source: "sterm_in_language paper_logical_type signature \<Gamma> (SApp (SLam \<sigma> A) T) \<tau>"
    by (rule paper_db_app_language[OF paper_db_lam_language[OF body] argument])
  have target: "sterm_in_language paper_logical_type signature \<Gamma> (ssubst0 T A) \<tau>"
    by (rule paper_db_subst0_language[OF body argument])
  have step: "scompatible_step sbeta_contract (SApp (SLam \<sigma> A) T) (ssubst0 T A)"
    by (rule scompatible_step.root[where R=sbeta_contract]) (rule sbeta_contract.beta)
  note S = source[unfolded sterm_in_language_def]
  note T = target[unfolded sterm_in_language_def]
  have conversion: "sbeta_eta_equiv_in_signature paper_logical_type signature \<Gamma> \<tau>
    (SApp (SLam \<sigma> A) T) (ssubst0 T A)"
    by (rule sbeta_eta_equiv_in_signature.Beta[OF conjunct1[OF S] conjunct1[OF T]
      conjunct2[OF S] conjunct2[OF T] step])
  show ?thesis by (rule denote_beta_eta[OF conversion env])
qed

theorem paper_db_one_binder:
  assumes body: "sterm_in_language paper_logical_type signature (\<sigma> # \<Gamma>) A \<tau>"
    and argument: "sterm_in_language paper_logical_type signature \<Gamma> T \<sigma>"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "denote (pbbk_extend (denote g T) g) A = denote g (ssubst0 T A)"
proof -
  let ?h = "pbbk_extend (denote g T) g"
  let ?L = "SLam \<sigma> A"
  let ?redex = "SApp (sshift ?L) (SVar 0)"
  have L: "sterm_in_language paper_logical_type signature \<Gamma> ?L (Arr \<sigma> \<tau>)"
    by (rule paper_db_lam_language[OF body])
  have T_domain: "denote g T \<in> domain \<sigma>" by (rule denote_type[OF argument env])
  have extended: "pbbk_env_typed domain (\<sigma> # \<Gamma>) ?h"
    by (rule pbbk_env_extend[OF env T_domain])
  have shifted_L: "sterm_in_language paper_logical_type signature (\<sigma> # \<Gamma>) (sshift ?L) (Arr \<sigma> \<tau>)"
    by (rule paper_db_shift_language[OF L])
  have zero: "sterm_in_language paper_logical_type signature (\<sigma> # \<Gamma>) (SVar 0) \<sigma>"
    unfolding sterm_in_language_def by (rule conjI) (rule has_stype.Var[OF lookup_Cons_0], simp)
  have redex: "sterm_in_language paper_logical_type signature (\<sigma> # \<Gamma>) ?redex \<tau>"
    by (rule paper_db_app_language[OF shifted_L zero])
  have step: "scompatible_step sbeta_contract ?redex A"
  proof -
    have "scompatible_step sbeta_contract
      (SApp (SLam \<sigma> (srename (lift_ren Suc) A)) (SVar 0))
      (ssubst0 (SVar 0) (srename (lift_ren Suc) A))"
      by (rule scompatible_step.root[where R=sbeta_contract]) (rule sbeta_contract.beta)
    then show ?thesis by (simp add: sshift_def paper_db_beta_slot_restore)
  qed
  note R = redex[unfolded sterm_in_language_def]
  note A = body[unfolded sterm_in_language_def]
  have conversion: "sbeta_eta_equiv_in_signature paper_logical_type signature (\<sigma> # \<Gamma>) \<tau> ?redex A"
    by (rule sbeta_eta_equiv_in_signature.Beta[OF conjunct1[OF R] conjunct1[OF A]
      conjunct2[OF R] conjunct2[OF A] step])
  have beta_left: "denote ?h ?redex = denote ?h A"
    by (rule denote_beta_eta[OF conversion extended])
  have same_function: "denote ?h (sshift ?L) = denote g ?L"
    by (rule paper_db_shift_assignment[OF L env T_domain])
  have same_argument: "denote ?h (SVar 0) = denote g T"
    using denote_var[OF lookup_Cons_0 extended] by (simp only: pbbk_extend_zero)
  have same_application: "denote ?h ?redex = denote g (SApp ?L T)"
    by (rule denote_application_cong[OF shifted_L zero L argument extended env same_function same_argument])
  have beta_right: "denote g (SApp ?L T) = denote g (ssubst0 T A)"
    by (rule paper_db_denote_beta[OF body argument env])
  have "denote ?h A = denote ?h ?redex" by (rule sym[OF beta_left])
  also have "... = denote g (SApp ?L T)" by (rule same_application)
  also have "... = denote g (ssubst0 T A)" by (rule beta_right)
  finally show ?thesis .
qed

end

end
