theory Bacon_C_Ref_Quantified_PC
  imports Bacon_C_Appendix_A2_EG
begin

section \<open>The quantified Boolean operation in the Ref case\<close>

text \<open>
  Vector PC gives (λx.λF.Fx ↔ Fx) = (λx.λF.⊤₀).  Replace this
  operation in λx.∀F.h x F and reduce β.  Together with A.1 this yields
  ⊢C (λx.∀F.Fx ↔ Fx) = (λx.⊤₀).
  Source: Bacon--Dorr Appendix A.2(iv), pp.65–66.

  Isabelle representation.  C_Ref_PC_left/right name the two curried
  operations.  Quantifier congruence below concerns syntactic βη only;
  the C-level replacement acts on the entire proved operation identity.
  Status.  No arbitrary open identity is abstracted or generalized.
\<close>

lemma C_A2_beta_eta_Forall:
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

definition C_Ref_PC_left :: "otype \<Rightarrow> oterm" where
  "C_Ref_PC_left \<sigma> = Lam \<sigma> (Lam (pred_ty \<sigma>)
    (App (Var 0) (Var 1) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)))"

definition C_Ref_PC_right :: "otype \<Rightarrow> oterm" where
  "C_Ref_PC_right \<sigma> = Lam \<sigma> (Lam (pred_ty \<sigma>) ObjTrue)"

lemma C_Ref_PC_types:
  "\<Gamma> \<turnstile> C_Ref_PC_left \<sigma> : \<sigma> \<rightarrow>\<^sub>o pred_ty \<sigma> \<rightarrow>\<^sub>o Prop"
  "\<Gamma> \<turnstile> C_Ref_PC_right \<sigma> : \<sigma> \<rightarrow>\<^sub>o pred_ty \<sigma> \<rightarrow>\<^sub>o Prop"
proof -
  show "\<Gamma> \<turnstile> C_Ref_PC_left \<sigma> : \<sigma> \<rightarrow>\<^sub>o pred_ty \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: C_Ref_PC_left_def pred_ty_def lookup_def)
  show "\<Gamma> \<turnstile> C_Ref_PC_right \<sigma> : \<sigma> \<rightarrow>\<^sub>o pred_ty \<sigma> \<rightarrow>\<^sub>o Prop"
    unfolding C_Ref_PC_right_def by (intro has_type.Lam typed_ObjTrue)
qed

lemma C_Ref_PC_rename:
  "rename r (C_Ref_PC_left \<sigma>) = C_Ref_PC_left \<sigma>"
  "rename r (C_Ref_PC_right \<sigma>) = C_Ref_PC_right \<sigma>"
  by (simp_all add: C_Ref_PC_left_def C_Ref_PC_right_def ObjTrue_def)

lemma C_Ref_PC_operation_identity:
  "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o pred_ty \<sigma> \<rightarrow>\<^sub>o Prop)
    (C_Ref_PC_left \<sigma>) (C_Ref_PC_right \<sigma>)"
proof -
  have app: "pred_ty \<sigma> # \<sigma> # \<Gamma> \<turnstile> App (Var 0) (Var 1) : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have PC: "prop_tautology ([pred_ty \<sigma>, \<sigma>] @ \<Gamma>)
    (App (Var 0) (Var 1) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))"
    using C_A2_reflexive_biconditional_PC[OF app] by simp
  show ?thesis using C_PC_vector_abstraction[OF PC]
    by (simp add: C_abstract_prefix_def C_Ref_PC_left_def C_Ref_PC_right_def)
qed

lemma C_Ref_PC_left_beta:
  assumes X: "\<Gamma> \<turnstile> X : \<sigma>" and F: "\<Gamma> \<turnstile> F : pred_ty \<sigma>"
  shows "beta_eta_equiv \<Gamma> Prop
    (App (App (C_Ref_PC_left \<sigma>) X) F) (App F X \<longleftrightarrow>\<^sub>o App F X)"
proof -
  have body: "pred_ty \<sigma> # \<sigma> # \<Gamma> \<turnstile>
    (App (Var 0) (Var 1) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)) : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  show ?thesis using C_A2_binary_application_beta[OF body X F]
    by (simp add: C_Ref_PC_left_def subst0_def C_subst_raised)
qed

lemma C_Ref_PC_right_beta:
  assumes X: "\<Gamma> \<turnstile> X : \<sigma>" and F: "\<Gamma> \<turnstile> F : pred_ty \<sigma>"
  shows "beta_eta_equiv \<Gamma> Prop (App (App (C_Ref_PC_right \<sigma>) X) F) ObjTrue"
  using C_A2_binary_application_beta[OF typed_ObjTrue X F]
  by (simp add: C_Ref_PC_right_def subst0_def ObjTrue_def)

theorem C_Ref_quantified_PC_operation:
  "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Forall (pred_ty \<sigma>)
      (App (Var 0) (Var 1) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))))
    (Lam \<sigma> ObjTrue)"
proof -
  let ?K = "\<sigma> \<rightarrow>\<^sub>o pred_ty \<sigma> \<rightarrow>\<^sub>o Prop"
  let ?M = "Forall (pred_ty \<sigma>) (App (App (Var 2) (Var 1)) (Var 0))"
  let ?L = "Forall (pred_ty \<sigma>) (App (App (C_Ref_PC_left \<sigma>) (Var 1)) (Var 0))"
  let ?R = "Forall (pred_ty \<sigma>) (App (App (C_Ref_PC_right \<sigma>) (Var 1)) (Var 0))"
  let ?Q = "Forall (pred_ty \<sigma>) (App (Var 0) (Var 1) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))"
  have body: "[\<sigma>] @ (?K # \<Gamma>) \<turnstile> ?M : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> ?L) (Lam \<sigma> ?R)"
    using C_vector_identity_context[OF C_Ref_PC_types(1) C_Ref_PC_types(2) body
      C_Ref_PC_operation_identity]
    by (simp add: C_abstract_prefix_def C_vector_lift_subst.simps C_Ref_PC_rename numeral_2_eq_2)
  have X: "pred_ty \<sigma> # \<sigma> # \<Gamma> \<turnstile> Var 1 : \<sigma>"
    by (rule has_type.Var) simp
  have F: "pred_ty \<sigma> # \<sigma> # \<Gamma> \<turnstile> Var 0 : pred_ty \<sigma>"
    by (rule has_type.Var) simp
  have left_conversion: "beta_eta_equiv (\<sigma> # \<Gamma>) Prop ?L ?Q"
    by (rule C_A2_beta_eta_Forall[OF C_Ref_PC_left_beta[OF X F]])
  have right_conversion: "beta_eta_equiv (\<sigma> # \<Gamma>) Prop ?R (Forall (pred_ty \<sigma>) ObjTrue)"
    by (rule C_A2_beta_eta_Forall[OF C_Ref_PC_right_beta[OF X F]])
  have left_identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> ?L) (Lam \<sigma> ?Q)"
    by (rule C_closure_beta_eta_identity[OF C_beta_eta_Lam[OF left_conversion]])
  have right_identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> ?R) (Lam \<sigma> (Forall (pred_ty \<sigma>) ObjTrue))"
    by (rule C_closure_beta_eta_identity[OF C_beta_eta_Lam[OF right_conversion]])
  have quantified: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> ?Q) (Lam \<sigma> (Forall (pred_ty \<sigma>) ObjTrue))"
    by (rule C_A1_transport[OF raw left_identity right_identity])
  have A1: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall (pred_ty \<sigma>) (shift ObjTrue)) ObjTrue"
    by (rule C_Appendix_A1_universal_truth)
  have constant_truth: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Forall (pred_ty \<sigma>) ObjTrue)) (Lam \<sigma> ObjTrue)"
    using C_boolean_lambda_constant_congruence[where \<sigma>=\<sigma>, OF A1]
    by (simp add: shift_def ObjTrue_def)
  show ?thesis by (rule C_A1_trans[OF quantified constant_truth])
qed

end
