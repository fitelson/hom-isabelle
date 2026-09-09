theory Bacon_C_Appendix_A2_Ref_Vector
  imports Bacon_C_Ref_Quantified_PC
begin

section \<open>Appendix A.2(iv): Ref beneath an arbitrary abstraction vector\<close>

text \<open>
  Identity Identity and β give
  (λx.x =σ x) = (λx.∀F:σ→t.(Fx ↔ Fx)).
  The preceding quantified-PC theorem identifies the latter operation
  with λx.⊤₀.  Replacing these identical unary operations inside λv̄.f M
  proves ⊢C (λv̄.M =σ M) = (λv̄.⊤₀).
  Source: Bacon--Dorr Figure 4 Identity Identity, p.13; A.2(iv), pp.65–66.

  Isabelle representation.  M may depend on every variable in Δ.
  The final application uses C_vector_function_congruence_beta.
  Status.  This is the full-vector Ref axiom case in C.  It does not
  abstract an arbitrary C identity or assume Functionality/Equivalence.
\<close>

definition C_Ref_identity_left :: "otype \<Rightarrow> oterm" where
  "C_Ref_identity_left \<sigma> = Lam \<sigma> (Lam \<sigma> (Eq \<sigma> (Var 1) (Var 0)))"

definition C_Ref_identity_right :: "otype \<Rightarrow> oterm" where
  "C_Ref_identity_right \<sigma> = Lam \<sigma> (Lam \<sigma> (Forall (pred_ty \<sigma>)
    (App (Var 0) (Var 2) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))))"

lemma C_Ref_identity_types:
  "\<Gamma> \<turnstile> C_Ref_identity_left \<sigma> : \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
  "\<Gamma> \<turnstile> C_Ref_identity_right \<sigma> : \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
proof -
  show "\<Gamma> \<turnstile> C_Ref_identity_left \<sigma> : \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: C_Ref_identity_left_def lookup_def)
  show "\<Gamma> \<turnstile> C_Ref_identity_right \<sigma> : \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: C_Ref_identity_right_def pred_ty_def lookup_def)
qed

lemma C_Ref_identity_rename:
  "rename r (C_Ref_identity_left \<sigma>) = C_Ref_identity_left \<sigma>"
  "rename r (C_Ref_identity_right \<sigma>) = C_Ref_identity_right \<sigma>"
  by (simp_all add: C_Ref_identity_left_def C_Ref_identity_right_def numeral_2_eq_2)

lemma C_Ref_identity_source:
  "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop)
    (C_Ref_identity_left \<sigma>) (C_Ref_identity_right \<sigma>)"
  using C_proves.IdentityIdentity[of \<Gamma> \<sigma>]
  by (simp add: classic_identity_identity_def identity_ty_def C_Ref_identity_left_def C_Ref_identity_right_def)

lemma C_Ref_identity_left_beta:
  assumes M: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "beta_eta_equiv \<Gamma> Prop
    (App (App (C_Ref_identity_left \<sigma>) M) M) (Eq \<sigma> M M)"
proof -
  have body: "\<sigma> # \<sigma> # \<Gamma> \<turnstile> Eq \<sigma> (Var 1) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  show ?thesis using C_A2_binary_application_beta[OF body M M]
    by (simp add: C_Ref_identity_left_def subst0_def C_subst_raised)
qed

lemma C_Ref_identity_right_beta:
  assumes M: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "beta_eta_equiv \<Gamma> Prop
    (App (App (C_Ref_identity_right \<sigma>) M) M)
    (Forall (pred_ty \<sigma>) (App (Var 0) (shift M) \<longleftrightarrow>\<^sub>o App (Var 0) (shift M)))"
proof -
  have body: "\<sigma> # \<sigma> # \<Gamma> \<turnstile> Forall (pred_ty \<sigma>)
    (App (Var 0) (Var 2) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)) : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  show ?thesis using C_A2_binary_application_beta[OF body M M]
    by (simp add: C_Ref_identity_right_def subst0_def shift_def numeral_2_eq_2 C_subst_twice_raised C_subst_raised)
qed

theorem C_Ref_diagonal_operation_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Eq \<sigma> (Var 0) (Var 0))) (Lam \<sigma> ObjTrue)"
proof -
  let ?K = "\<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
  let ?L = "App (App (C_Ref_identity_left \<sigma>) (Var 0)) (Var 0)"
  let ?R = "App (App (C_Ref_identity_right \<sigma>) (Var 0)) (Var 0)"
  let ?Q = "Forall (pred_ty \<sigma>) (App (Var 0) (Var 1) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))"
  have body: "[\<sigma>] @ (?K # \<Gamma>) \<turnstile> App (App (Var 1) (Var 0)) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> ?L) (Lam \<sigma> ?R)"
    using C_vector_identity_context[OF C_Ref_identity_types(1) C_Ref_identity_types(2) body C_Ref_identity_source]
    by (simp add: C_abstract_prefix_def C_vector_lift_subst.simps C_Ref_identity_rename)
  have variable: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  have left_identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> ?L) (Lam \<sigma> (Eq \<sigma> (Var 0) (Var 0)))"
    by (rule C_closure_beta_eta_identity[OF C_beta_eta_Lam[OF C_Ref_identity_left_beta[OF variable]]])
  have right_conversion: "beta_eta_equiv (\<sigma> # \<Gamma>) Prop ?R ?Q"
    using C_Ref_identity_right_beta[OF variable] by (simp add: shift_def)
  have right_identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> ?R) (Lam \<sigma> ?Q)"
    by (rule C_closure_beta_eta_identity[OF C_beta_eta_Lam[OF right_conversion]])
  have unfolded: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Eq \<sigma> (Var 0) (Var 0))) (Lam \<sigma> ?Q)"
    by (rule C_A1_transport[OF raw left_identity right_identity])
  show ?thesis by (rule C_A1_trans[OF unfolded C_Ref_quantified_PC_operation])
qed

theorem C_A2_Ref_vector_truth:
  assumes M: "\<Delta> @ \<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Eq \<sigma> M M)) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  let ?F = "Lam \<sigma> (Eq \<sigma> (Var 0) (Var 0))"
  let ?G = "Lam \<sigma> ObjTrue"
  have F_type: "\<Gamma> \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have G_type: "\<Gamma> \<turnstile> ?G : \<sigma> \<rightarrow>\<^sub>o Prop" by (intro has_type.Lam typed_ObjTrue)
  have F_raised: "C_vector_raise n ?F = ?F" for n by (induction n) simp_all
  have G_raised: "C_vector_raise n ?G = ?G" for n by (induction n) (simp_all add: ObjTrue_def)
  have body: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> Eq \<sigma> (Var 0) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have left_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (App (C_vector_raise (length \<Delta>) ?F) M) (Eq \<sigma> M M)"
    using C_UI_predicate_application_beta[OF body M] by (simp add: F_raised subst0_def)
  have right_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (App (C_vector_raise (length \<Delta>) ?G) M) ObjTrue"
    using C_UI_predicate_application_beta[OF typed_ObjTrue M]
    by (simp only: G_raised; simp add: subst0_def ObjTrue_def)
  show ?thesis by (rule C_vector_function_congruence_beta[OF F_type G_type M
    C_Ref_diagonal_operation_truth left_conversion right_conversion])
qed

end
