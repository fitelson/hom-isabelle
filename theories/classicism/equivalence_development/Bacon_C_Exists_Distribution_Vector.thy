theory Bacon_C_Exists_Distribution_Vector
  imports Bacon_C_Forall_Distribution_Vector Bacon_C_Appendix_A2_EG
begin

section \<open>Existential distribution beneath an arbitrary vector\<close>

text \<open>
  ⊢C (λv̄.B ∧ ∃x:σ.A) = (λv̄.∃x:σ.(B ∧ A)), with x not free in B.
  Source: Bacon--Dorr Figure 4 Distribution-∧∃, p.13, used in the Inst
  induction step of Appendix A.2, pp.65–67.
  Isabelle representation.  The inner occurrence of B is shift B.
  The closed source operations are applied to λx.A and B beneath Δ,
  then reduced by typed β conversions.
  Status.  No distribution rule is added; the theorem derives its
  vector instance from the supplied operation identity in C.
\<close>

definition C_Inst_dist_left :: "otype \<Rightarrow> oterm" where
  "C_Inst_dist_left \<sigma> = Lam (pred_ty \<sigma>) (Lam Prop
    (Conj (Var 0) (Exists \<sigma> (App (Var 2) (Var 0)))))"

definition C_Inst_dist_right :: "otype \<Rightarrow> oterm" where
  "C_Inst_dist_right \<sigma> = Lam (pred_ty \<sigma>) (Lam Prop
    (Exists \<sigma> (Conj (Var 1) (App (Var 2) (Var 0)))))"

lemma C_Inst_dist_types:
  "\<Gamma> \<turnstile> C_Inst_dist_left \<sigma> : pred_ty \<sigma> \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
  "\<Gamma> \<turnstile> C_Inst_dist_right \<sigma> : pred_ty \<sigma> \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
proof -
  show "\<Gamma> \<turnstile> C_Inst_dist_left \<sigma> : pred_ty \<sigma> \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: C_Inst_dist_left_def pred_ty_def lookup_def)
  show "\<Gamma> \<turnstile> C_Inst_dist_right \<sigma> : pred_ty \<sigma> \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: C_Inst_dist_right_def pred_ty_def lookup_def)
qed

lemma C_Inst_dist_source:
  "\<Gamma> \<turnstile>\<^sub>C Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
    (C_Inst_dist_left \<sigma>) (C_Inst_dist_right \<sigma>)"
  using C_proves.DistConjExists[of \<Gamma> \<sigma>]
  by (simp only: classic_dist_conj_exists_def C_Inst_dist_left_def C_Inst_dist_right_def)

lemma C_Inst_dist_raised:
  "C_vector_raise n (C_Inst_dist_left \<sigma>) = C_Inst_dist_left \<sigma>"
  "C_vector_raise n (C_Inst_dist_right \<sigma>) = C_Inst_dist_right \<sigma>"
proof -
  show "C_vector_raise n (C_Inst_dist_left \<sigma>) = C_Inst_dist_left \<sigma>"
    by (induction n) (simp_all add: C_Inst_dist_left_def numeral_2_eq_2)
  show "C_vector_raise n (C_Inst_dist_right \<sigma>) = C_Inst_dist_right \<sigma>"
    by (induction n) (simp_all add: C_Inst_dist_right_def numeral_2_eq_2)
qed

lemma C_Inst_dist_left_beta:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
  shows "beta_eta_equiv \<Gamma> Prop
    (App (App (C_Inst_dist_left \<sigma>) (Lam \<sigma> A)) B) (Conj B (Exists \<sigma> A))"
proof -
  have body: "Prop # pred_ty \<sigma> # \<Gamma> \<turnstile>
    Conj (Var 0) (Exists \<sigma> (App (Var 2) (Var 0))) : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have predicate_type: "\<Gamma> \<turnstile> Lam \<sigma> A : pred_ty \<sigma>"
    using has_type.Lam[OF A] by (simp only: pred_ty_def)
  have first: "beta_eta_equiv \<Gamma> Prop
    (App (App (C_Inst_dist_left \<sigma>) (Lam \<sigma> A)) B)
    (Conj B (Exists \<sigma> (App (shift (Lam \<sigma> A)) (Var 0))))"
    using C_A2_binary_application_beta[OF body predicate_type B]
    by (simp add: C_Inst_dist_left_def subst0_def numeral_2_eq_2 shift_def
      C_subst_twice_raised C_subst_raised C_remove_inserted_operation C_A2_subst_twice_lifted)
  show ?thesis by (rule beta_eta_equiv.Trans[OF first
    C_PC_beta_eta_Conj[OF beta_eta_equiv.Refl[OF B] C_EG_quantified_predicate_beta[OF A]]])
qed

lemma C_Inst_dist_right_beta:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
  shows "beta_eta_equiv \<Gamma> Prop
    (App (App (C_Inst_dist_right \<sigma>) (Lam \<sigma> A)) B)
    (Exists \<sigma> (Conj (shift B) A))"
proof -
  have body: "Prop # pred_ty \<sigma> # \<Gamma> \<turnstile>
    Exists \<sigma> (Conj (Var 1) (App (Var 2) (Var 0))) : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have predicate_type: "\<Gamma> \<turnstile> Lam \<sigma> A : pred_ty \<sigma>"
    using has_type.Lam[OF A] by (simp only: pred_ty_def)
  have first: "beta_eta_equiv \<Gamma> Prop
    (App (App (C_Inst_dist_right \<sigma>) (Lam \<sigma> A)) B)
    (Exists \<sigma> (Conj (shift B) (App (shift (Lam \<sigma> A)) (Var 0))))"
    using C_A2_binary_application_beta[OF body predicate_type B]
    by (simp add: C_Inst_dist_right_def subst0_def numeral_2_eq_2 shift_def
      C_subst_twice_raised C_subst_raised C_remove_inserted_operation C_A2_subst_twice_lifted)
  have shifted_B: "\<sigma> # \<Gamma> \<turnstile> shift B : Prop" by (rule weakening_front[OF B])
  have second: "beta_eta_equiv \<Gamma> Prop
    (Exists \<sigma> (Conj (shift B) (App (shift (Lam \<sigma> A)) (Var 0))))
    (Exists \<sigma> (Conj (shift B) A))"
    by (rule C_PC_beta_eta_Exists[OF C_PC_beta_eta_Conj[OF beta_eta_equiv.Refl[OF shifted_B]
      C_Gen_predicate_body_beta[OF A]]])
  show ?thesis by (rule beta_eta_equiv.Trans[OF first second])
qed

theorem C_vector_Exists_distribution:
  assumes A: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> A : Prop" and B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj B (Exists \<sigma> A)))
    (C_abstract_prefix \<Delta> (Exists \<sigma> (Conj (shift B) A)))"
proof -
  have predicate_type: "\<Delta> @ \<Gamma> \<turnstile> Lam \<sigma> A : pred_ty \<sigma>"
    using has_type.Lam[OF A] by (simp only: pred_ty_def)
  have left: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (App (App (C_vector_raise (length \<Delta>) (C_Inst_dist_left \<sigma>)) (Lam \<sigma> A)) B)
    (Conj B (Exists \<sigma> A))"
    using C_Inst_dist_left_beta[OF A B] by (simp only: C_Inst_dist_raised)
  have right: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (App (App (C_vector_raise (length \<Delta>) (C_Inst_dist_right \<sigma>)) (Lam \<sigma> A)) B)
    (Exists \<sigma> (Conj (shift B) A))"
    using C_Inst_dist_right_beta[OF A B] by (simp only: C_Inst_dist_raised)
  show ?thesis by (rule C_vector_binary_function_congruence_beta[OF C_Inst_dist_types(1)
    C_Inst_dist_types(2) predicate_type B C_Inst_dist_source left right])
qed

end
