theory Bacon_C_Vector_Quantifier_Congruence
  imports Bacon_C_Appendix_A2_MP
begin

section \<open>Quantifying supplied vector identities\<close>

text \<open>
  From ⊢C (λv̄λx:σ.A) = (λv̄λx:σ.B), derive
  ⊢C (λv̄.∀x:σ.A) = (λv̄.∀x:σ.B), and likewise for ∃.
  Source role: typed operation replacement supporting the Gen and Inst
  cases of Bacon–Dorr Appendix A.2, pp.65–66.

  Isabelle representation.  Δ is the de Bruijn prefix for v̄, so the
  supplied operations abstract σ # Δ.  A typed evaluation context puts
  the operation slot beneath ∀ or ∃ and applies it to all reversed fresh
  variables, including x.  Prefix substitution and β deabstraction then
  restore A and B.  The statements have only the supplied operation
  identity as premise; body typing is recovered from that identity.

  Status.  No arbitrary open equation is abstracted.  All object-language
  inference is in C, with no CE/CEV Equivalence or semantic assumption.
\<close>

lemma C_PC_beta_eta_Forall:
  assumes conversion: "beta_eta_equiv (\<sigma> # \<Gamma>) Prop A B"
  shows "beta_eta_equiv \<Gamma> Prop (Forall \<sigma> A) (Forall \<sigma> B)"
proof (rule C_PC_conversion_context[where f="Forall \<sigma>", OF conversion])
  fix X
  assume X: "\<sigma> # \<Gamma> \<turnstile> X : Prop"
  show "\<Gamma> \<turnstile> Forall \<sigma> X : Prop" by (rule has_type.Forall[OF X])
next
  fix X Y
  assume step: "compatible_step beta_contract X Y"
  show "compatible_step beta_contract (Forall \<sigma> X) (Forall \<sigma> Y)"
    by (rule compatible_step.Forall_body[OF step])
next
  fix X Y
  assume step: "compatible_step eta_contract X Y"
  show "compatible_step eta_contract (Forall \<sigma> X) (Forall \<sigma> Y)"
    by (rule compatible_step.Forall_body[OF step])
qed

lemma C_PC_beta_eta_Exists:
  assumes conversion: "beta_eta_equiv (\<sigma> # \<Gamma>) Prop A B"
  shows "beta_eta_equiv \<Gamma> Prop (Exists \<sigma> A) (Exists \<sigma> B)"
proof (rule C_PC_conversion_context[where f="Exists \<sigma>", OF conversion])
  fix X
  assume X: "\<sigma> # \<Gamma> \<turnstile> X : Prop"
  show "\<Gamma> \<turnstile> Exists \<sigma> X : Prop" by (rule has_type.Exists[OF X])
next
  fix X Y
  assume step: "compatible_step beta_contract X Y"
  show "compatible_step beta_contract (Exists \<sigma> X) (Exists \<sigma> Y)"
    by (rule compatible_step.Exists_body[OF step])
next
  fix X Y
  assume step: "compatible_step eta_contract X Y"
  show "compatible_step eta_contract (Exists \<sigma> X) (Exists \<sigma> Y)"
    by (rule compatible_step.Exists_body[OF step])
qed

lemma C_vector_identity_body_types:
  assumes identity: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) \<tau>)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> B)"
  shows "\<Delta> @ \<Gamma> \<turnstile> A : \<tau>" and "\<Delta> @ \<Gamma> \<turnstile> B : \<tau>"
proof -
  have formula: "\<Gamma> \<turnstile> Eq (arrow_type (rev \<Delta>) \<tau>)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> B) : Prop"
    by (rule C_proves_formula[OF identity])
  have A: "\<Gamma> \<turnstile> C_abstract_prefix \<Delta> A : arrow_type (rev \<Delta>) \<tau>"
    and B: "\<Gamma> \<turnstile> C_abstract_prefix \<Delta> B : arrow_type (rev \<Delta>) \<tau>"
    using formula by (auto elim: has_type.cases)
  show "\<Delta> @ \<Gamma> \<turnstile> A : \<tau>"
    using C_lam_vec_type_reflect[OF A[unfolded C_abstract_prefix_def]] by simp
  show "\<Delta> @ \<Gamma> \<turnstile> B : \<tau>"
    using C_lam_vec_type_reflect[OF B[unfolded C_abstract_prefix_def]] by simp
qed

lemma C_vector_evaluation_slot_type:
  "\<Xi> @ (arrow_type (rev \<Xi>) \<tau> # \<Gamma>) \<turnstile>
    app_vec (Var (length \<Xi>)) (rev (fresh_vars (length \<Xi>))) : \<tau>"
proof -
  let ?\<nu> = "arrow_type (rev \<Xi>) \<tau>"
  have zero: "lookup (?\<nu> # \<Gamma>) 0 = Some ?\<nu>" by simp
  have index: "lookup (\<Xi> @ (?\<nu> # \<Gamma>)) (length \<Xi>) = Some ?\<nu>"
    using lookup_append_shift[OF zero, where \<Delta>=\<Xi>] by simp
  have operator: "\<Xi> @ (?\<nu> # \<Gamma>) \<turnstile> Var (length \<Xi>) : ?\<nu>"
    by (rule has_type.Var[OF index])
  show ?thesis by (rule typed_app_vec[OF operator C_vector_reverse_fresh_vars_type])
qed

lemma C_vector_evaluation_subst:
  "subst (C_vector_lift_subst n (case_nat F Var)) (app_vec (Var n) (rev (fresh_vars n))) =
    app_vec (C_vector_raise n F) (rev (fresh_vars n))"
  by (simp only: C_Church_subst_app_vec subst.simps C_vector_lift_subst_slot C_vector_subst_reverse_fresh_vars)

lemma C_vector_forall_evaluation_subst:
  "subst (C_vector_lift_subst n (case_nat F Var))
    (Forall \<sigma> (app_vec (Var (Suc n)) (rev (fresh_vars (Suc n))))) =
    Forall \<sigma> (app_vec (C_vector_raise (Suc n) F) (rev (fresh_vars (Suc n))))"
  by (simp only: subst.simps C_vector_lift_subst.simps(2)[symmetric] C_vector_evaluation_subst)

lemma C_vector_exists_evaluation_subst:
  "subst (C_vector_lift_subst n (case_nat F Var))
    (Exists \<sigma> (app_vec (Var (Suc n)) (rev (fresh_vars (Suc n))))) =
    Exists \<sigma> (app_vec (C_vector_raise (Suc n) F) (rev (fresh_vars (Suc n))))"
  by (simp only: subst.simps C_vector_lift_subst.simps(2)[symmetric] C_vector_evaluation_subst)

theorem C_vector_Forall_congruence:
  assumes identity: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev (\<sigma> # \<Delta>)) Prop)
    (C_abstract_prefix (\<sigma> # \<Delta>) A) (C_abstract_prefix (\<sigma> # \<Delta>) B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Forall \<sigma> A)) (C_abstract_prefix \<Delta> (Forall \<sigma> B))"
proof -
  let ?n = "length \<Delta>"
  let ?\<nu> = "arrow_type (rev (\<sigma> # \<Delta>)) Prop"
  let ?F = "C_abstract_prefix (\<sigma> # \<Delta>) A"
  let ?G = "C_abstract_prefix (\<sigma> # \<Delta>) B"
  let ?eval = "app_vec (Var (Suc ?n)) (rev (fresh_vars (Suc ?n)))"
  have A: "(\<sigma> # \<Delta>) @ \<Gamma> \<turnstile> A : Prop" by (rule C_vector_identity_body_types(1)[OF identity])
  have B: "(\<sigma> # \<Delta>) @ \<Gamma> \<turnstile> B : Prop" by (rule C_vector_identity_body_types(2)[OF identity])
  have F: "\<Gamma> \<turnstile> ?F : ?\<nu>" by (rule C_abstract_prefix_type[OF A])
  have G: "\<Gamma> \<turnstile> ?G : ?\<nu>" by (rule C_abstract_prefix_type[OF B])
  have eval_type: "\<sigma> # (\<Delta> @ (?\<nu> # \<Gamma>)) \<turnstile> ?eval : Prop"
    using C_vector_evaluation_slot_type[where \<Xi>="\<sigma> # \<Delta>" and \<tau>=Prop and \<Gamma>=\<Gamma>] by simp
  have context_type: "\<Delta> @ (?\<nu> # \<Gamma>) \<turnstile> Forall \<sigma> ?eval : Prop"
    by (rule has_type.Forall[OF eval_type])
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Forall \<sigma> (app_vec (C_vector_raise (Suc ?n) ?F) (rev (fresh_vars (Suc ?n))))))
    (C_abstract_prefix \<Delta> (Forall \<sigma> (app_vec (C_vector_raise (Suc ?n) ?G) (rev (fresh_vars (Suc ?n))))))"
    using C_vector_identity_context[OF F G context_type identity] by (simp only: C_vector_forall_evaluation_subst)
  have left_body: "beta_eta_equiv (\<sigma> # (\<Delta> @ \<Gamma>)) Prop
    (app_vec (C_vector_raise (Suc ?n) ?F) (rev (fresh_vars (Suc ?n)))) A"
    using C_vector_deabstract_beta_eta[OF A] by simp
  have right_body: "beta_eta_equiv (\<sigma> # (\<Delta> @ \<Gamma>)) Prop
    (app_vec (C_vector_raise (Suc ?n) ?G) (rev (fresh_vars (Suc ?n)))) B"
    using C_vector_deabstract_beta_eta[OF B] by simp
  show ?thesis by (rule C_A1_transport[OF raw
    C_vector_conversion_identity[OF C_PC_beta_eta_Forall[OF left_body]]
    C_vector_conversion_identity[OF C_PC_beta_eta_Forall[OF right_body]]])
qed

theorem C_vector_Exists_congruence:
  assumes identity: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev (\<sigma> # \<Delta>)) Prop)
    (C_abstract_prefix (\<sigma> # \<Delta>) A) (C_abstract_prefix (\<sigma> # \<Delta>) B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Exists \<sigma> A)) (C_abstract_prefix \<Delta> (Exists \<sigma> B))"
proof -
  let ?n = "length \<Delta>"
  let ?\<nu> = "arrow_type (rev (\<sigma> # \<Delta>)) Prop"
  let ?F = "C_abstract_prefix (\<sigma> # \<Delta>) A"
  let ?G = "C_abstract_prefix (\<sigma> # \<Delta>) B"
  let ?eval = "app_vec (Var (Suc ?n)) (rev (fresh_vars (Suc ?n)))"
  have A: "(\<sigma> # \<Delta>) @ \<Gamma> \<turnstile> A : Prop" by (rule C_vector_identity_body_types(1)[OF identity])
  have B: "(\<sigma> # \<Delta>) @ \<Gamma> \<turnstile> B : Prop" by (rule C_vector_identity_body_types(2)[OF identity])
  have F: "\<Gamma> \<turnstile> ?F : ?\<nu>" by (rule C_abstract_prefix_type[OF A])
  have G: "\<Gamma> \<turnstile> ?G : ?\<nu>" by (rule C_abstract_prefix_type[OF B])
  have eval_type: "\<sigma> # (\<Delta> @ (?\<nu> # \<Gamma>)) \<turnstile> ?eval : Prop"
    using C_vector_evaluation_slot_type[where \<Xi>="\<sigma> # \<Delta>" and \<tau>=Prop and \<Gamma>=\<Gamma>] by simp
  have context_type: "\<Delta> @ (?\<nu> # \<Gamma>) \<turnstile> Exists \<sigma> ?eval : Prop"
    by (rule has_type.Exists[OF eval_type])
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Exists \<sigma> (app_vec (C_vector_raise (Suc ?n) ?F) (rev (fresh_vars (Suc ?n))))))
    (C_abstract_prefix \<Delta> (Exists \<sigma> (app_vec (C_vector_raise (Suc ?n) ?G) (rev (fresh_vars (Suc ?n))))))"
    using C_vector_identity_context[OF F G context_type identity] by (simp only: C_vector_exists_evaluation_subst)
  have left_body: "beta_eta_equiv (\<sigma> # (\<Delta> @ \<Gamma>)) Prop
    (app_vec (C_vector_raise (Suc ?n) ?F) (rev (fresh_vars (Suc ?n)))) A"
    using C_vector_deabstract_beta_eta[OF A] by simp
  have right_body: "beta_eta_equiv (\<sigma> # (\<Delta> @ \<Gamma>)) Prop
    (app_vec (C_vector_raise (Suc ?n) ?G) (rev (fresh_vars (Suc ?n)))) B"
    using C_vector_deabstract_beta_eta[OF B] by simp
  show ?thesis by (rule C_A1_transport[OF raw
    C_vector_conversion_identity[OF C_PC_beta_eta_Exists[OF left_body]]
    C_vector_conversion_identity[OF C_PC_beta_eta_Exists[OF right_body]]])
qed

end
