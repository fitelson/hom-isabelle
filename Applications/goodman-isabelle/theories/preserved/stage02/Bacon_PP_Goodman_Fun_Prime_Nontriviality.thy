theory Bacon_PP_Goodman_Fun_Prime_Nontriviality
  imports 
    "Goodman_Legacy_02.Bacon_PP_Goodman_Fun_Prime_Closure"
begin

section \<open>Goodman's nontriviality facts for \<open>fun\<acute>\<close>\<close>

subsection \<open>Evaluation respects operator identity\<close>

definition pp_evaluation_context :: "oterm \<Rightarrow> oterm" where
  "pp_evaluation_context p =
    Lam pp_unary_ty (App (Var 0) (shift p))"

lemma typed_pp_evaluation_context:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile> pp_evaluation_context p :
    pp_unary_ty \<rightarrow>\<^sub>o Prop"
  unfolding pp_evaluation_context_def
proof (rule has_type.Lam)
  have v_type:
    "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
    by (rule typed_var0)
  have p_shift:
    "pp_unary_ty # \<Gamma> \<turnstile> shift p : Prop"
    using p_type by (rule typed_shift_ctx)
  show "pp_unary_ty # \<Gamma> \<turnstile>
    App (Var 0) (shift p) : Prop"
    using v_type p_shift unfolding pp_unary_ty_def
    by (rule has_type.App)
qed

lemma pp_evaluation_context_beta:
  "compatible_step beta_contract
    (App (pp_evaluation_context p) F)
    (App F p)"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty (App (Var 0) (shift p)))
        F)
      (subst0 F (App (Var 0) (shift p)))"
    by (rule beta_contract.beta)
  show "beta_contract
    (App (pp_evaluation_context p) F)
    (App F p)"
    using step
    by (simp add: pp_evaluation_context_def subst0_def
      subst_lift_shift)
qed

lemma CEV_pp_evaluation_context_eq:
  assumes F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop
      (App (pp_evaluation_context p) F)
      (App F p)"
proof -
  have left_type:
    "\<Gamma> \<turnstile> App (pp_evaluation_context p) F : Prop"
    using typed_pp_evaluation_context[OF p_type] F_type
    by (rule has_type.App)
  have right_type: "\<Gamma> \<turnstile> App F p : Prop"
    using F_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have iff:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App (pp_evaluation_context p) F
        \<longleftrightarrow>\<^sub>o App F p)"
    using left_type right_type pp_evaluation_context_beta
    by (rule CEV_beta_step)
  show ?thesis
    using left_type right_type iff by (rule CEV_zeroary_equivalence)
qed

lemma CEV_axiom_from_pp_apply_cong_left:
  assumes F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and G_type: "\<Gamma> \<turnstile> G : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and FG:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty F G"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App F p) (App G p)"
proof -
  let ?K = "pp_evaluation_context p"
  let ?KF = "App ?K F"
  let ?KG = "App ?K G"
  have K_type: "\<Gamma> \<turnstile> ?K : pp_unary_ty \<rightarrow>\<^sub>o Prop"
    using p_type by (rule typed_pp_evaluation_context)
  have KF_type: "\<Gamma> \<turnstile> ?KF : Prop"
    using K_type F_type by (rule has_type.App)
  have KG_type: "\<Gamma> \<turnstile> ?KG : Prop"
    using K_type G_type by (rule has_type.App)
  have Fp_type: "\<Gamma> \<turnstile> App F p : Prop"
    using F_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Gp_type: "\<Gamma> \<turnstile> App G p : Prop"
    using G_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have context_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?KF ?KG"
    using K_type F_type G_type FG
    by (rule CEV_axiom_from_eq_app_right)
  have beta_F:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?KF (App F p)"
    using CEV_pp_evaluation_context_eq[OF F_type p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have beta_F_sym:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App F p) ?KF"
    using KF_type Fp_type beta_F by (rule CEV_axiom_from_eq_sym)
  have first:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App F p) ?KG"
    using Fp_type KF_type KG_type beta_F_sym context_eq
    by (rule CEV_axiom_from_eq_trans)
  have beta_G:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?KG (App G p)"
    using CEV_pp_evaluation_context_eq[OF G_type p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using Fp_type KG_type Gp_type first beta_G
    by (rule CEV_axiom_from_eq_trans)
qed

lemma CEV_axiom_from_eq_prop_elim:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    and AB:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop A B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
proof -
  have implication:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Eq Prop A B) (Imp A B)"
    using CEV_eq_prop_implication[OF A_type B_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have AB_imp:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp A B"
    using AB implication by (rule CEV_axiom_from.MP)
  show ?thesis
    using A AB_imp by (rule CEV_axiom_from.MP)
qed

subsection \<open>Constant operators\<close>

definition pp_constant_lambda :: "oterm \<Rightarrow> oterm" where
  "pp_constant_lambda P = Lam Prop (shift P)"

lemma typed_pp_constant_lambda:
  assumes P_type: "\<Gamma> \<turnstile> P : Prop"
  shows "\<Gamma> \<turnstile> pp_constant_lambda P : pp_unary_ty"
  unfolding pp_constant_lambda_def pp_unary_ty_def
  using typed_shift_ctx[OF P_type] by (rule has_type.Lam)

lemma pp_constant_operator_first_beta:
  "compatible_step beta_contract
    (App (pp_constant_operator P) Q)
    (App (pp_constant_lambda P) Q)"
proof (rule compatible_step.App_left, rule compatible_step.root)
  have step:
    "beta_contract
      (App (Lam Prop (Lam Prop (Var 1))) P)
      (subst0 P (Lam Prop (Var 1)))"
    by (rule beta_contract.beta)
  show "beta_contract
    (pp_constant_operator P)
    (pp_constant_lambda P)"
    using step
    by (simp add: pp_constant_operator_def pp_constant_builder_def
      pp_constant_lambda_def subst0_def shift_def)
qed

lemma pp_constant_operator_second_beta:
  "compatible_step beta_contract
    (App (pp_constant_lambda P) Q)
    P"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App (Lam Prop (shift P)) Q)
      (subst0 Q (shift P))"
    by (rule beta_contract.beta)
  show "beta_contract
    (App (pp_constant_lambda P) Q)
    P"
    using step
    by (simp add: pp_constant_lambda_def subst0_def)
qed

lemma CEV_pp_constant_operator_apply_eq:
  assumes P_type: "\<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop (App (pp_constant_operator P) Q) P"
proof -
  let ?K = "pp_constant_operator P"
  let ?L = "pp_constant_lambda P"
  have K_type: "\<Gamma> \<turnstile> ?K : pp_unary_ty"
    using P_type by (rule typed_pp_constant_operator)
  have L_type: "\<Gamma> \<turnstile> ?L : pp_unary_ty"
    using P_type by (rule typed_pp_constant_lambda)
  have KQ_type: "\<Gamma> \<turnstile> App ?K Q : Prop"
    using K_type Q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have LQ_type: "\<Gamma> \<turnstile> App ?L Q : Prop"
    using L_type Q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have first_iff:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App ?K Q \<longleftrightarrow>\<^sub>o App ?L Q)"
    using KQ_type LQ_type pp_constant_operator_first_beta
    by (rule CEV_beta_step)
  have first_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (App ?K Q) (App ?L Q)"
    using KQ_type LQ_type first_iff by (rule CEV_zeroary_equivalence)
  have second_iff:
    "\<Gamma> \<turnstile>\<^sub>CEV (App ?L Q \<longleftrightarrow>\<^sub>o P)"
    using LQ_type P_type pp_constant_operator_second_beta
    by (rule CEV_beta_step)
  have second_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (App ?L Q) P"
    using LQ_type P_type second_iff by (rule CEV_zeroary_equivalence)
  show ?thesis
    using KQ_type LQ_type P_type first_eq second_eq
    by (rule CEV_eq_trans_from)
qed

lemma CEV_pp_identity_operator_apply_eq:
  assumes P_type: "\<Gamma> \<turnstile> P : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop (App pp_identity_operator P) P"
proof -
  have left_type:
    "\<Gamma> \<turnstile> App pp_identity_operator P : Prop"
    using typed_pp_identity_operator P_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  show ?thesis
    using left_type P_type CEV_pp_identity_apply[OF P_type]
    by (rule CEV_zeroary_equivalence)
qed

subsection \<open>The PP-free stock needed by T2\<close>

definition pp_T2_min_axioms :: "oterm set" where
  "pp_T2_min_axioms =
    pp_purity_schema \<union> pp_application_closure_schema"

lemma pp_T2_min_axioms_subset_T6_core:
  "pp_T2_min_axioms \<subseteq> pp_T6_core_PP_axioms"
  unfolding pp_T2_min_axioms_def pp_T6_core_PP_axioms_def by blast

lemma pp_T2_min_axioms_into_T6_extension:
  assumes "pp_T6_core_PP_axioms \<subseteq> T"
  shows "pp_T2_min_axioms \<subseteq> T"
  using pp_T2_min_axioms_subset_T6_core assms by blast

subsection \<open>Core purity facts\<close>

lemma pp_T6_identity_purity_axiom:
  "pp_pure pp_unary_ty pp_identity_operator
    \<in> pp_T2_min_axioms"
  unfolding pp_T2_min_axioms_def
  using pp_identity_operator_purity_axiom by blast

lemma pp_constant_ObjTrue_purity_axiom:
  "pp_pure pp_unary_ty (pp_constant_operator ObjTrue)
    \<in> pp_T2_min_axioms"
  unfolding pp_T2_min_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
proof (intro UnI1 CollectI exI conjI)
  show "[] \<turnstile> pp_constant_operator ObjTrue : pp_unary_ty"
    using typed_ObjTrue by (rule typed_pp_constant_operator)
  show "consts_of (pp_constant_operator ObjTrue) = {}"
    by (simp add: pp_constant_operator_def pp_constant_builder_def
      ObjTrue_def)
qed simp

lemma pp_constant_ObjFalse_purity_axiom:
  "pp_pure pp_unary_ty (pp_constant_operator ObjFalse)
    \<in> pp_T2_min_axioms"
  unfolding pp_T2_min_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
proof (intro UnI1 CollectI exI conjI)
  show "[] \<turnstile> pp_constant_operator ObjFalse : pp_unary_ty"
    using typed_ObjFalse by (rule typed_pp_constant_operator)
  show "consts_of (pp_constant_operator ObjFalse) = {}"
    by (simp add: pp_constant_operator_def pp_constant_builder_def
      ObjFalse_def ObjTrue_def)
qed simp

lemma pp_identity_operator_pure_in_core_extension:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty pp_identity_operator"
proof -
  have core_proof:
    "\<Gamma> ; pp_T2_min_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty pp_identity_operator"
    using pp_T6_identity_purity_axiom
      typed_pp_pure[OF typed_pp_identity_operator]
    by (rule CEV_axiom_proves.Axiom)
  show ?thesis
    using core_proof core by (rule CEV_axiom_proves_mono)
qed

lemma pp_constant_ObjTrue_pure_in_core_extension:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty (pp_constant_operator ObjTrue)"
proof -
  have core_proof:
    "\<Gamma> ; pp_T2_min_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty (pp_constant_operator ObjTrue)"
    using pp_constant_ObjTrue_purity_axiom
      typed_pp_pure[
        OF typed_pp_constant_operator[OF typed_ObjTrue]]
    by (rule CEV_axiom_proves.Axiom)
  show ?thesis
    using core_proof core by (rule CEV_axiom_proves_mono)
qed

lemma pp_constant_ObjFalse_pure_in_core_extension:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty (pp_constant_operator ObjFalse)"
proof -
  have core_proof:
    "\<Gamma> ; pp_T2_min_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty (pp_constant_operator ObjFalse)"
    using pp_constant_ObjFalse_purity_axiom
      typed_pp_pure[
        OF typed_pp_constant_operator[OF typed_ObjFalse]]
    by (rule CEV_axiom_proves.Axiom)
  show ?thesis
    using core_proof core by (rule CEV_axiom_proves_mono)
qed

subsection \<open>Truth and falsity do not satisfy \<open>fun\<acute>\<close>\<close>

theorem CEV_not_fun_prime_ObjTrue:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (pp_fun_prime ObjTrue)"
proof -
  let ?I = "pp_identity_operator"
  let ?K = "pp_constant_operator ObjTrue"
  let ?A = "pp_fun_prime ObjTrue"
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using typed_ObjTrue by (rule typed_pp_fun_prime)
  have I_type: "\<Gamma> \<turnstile> ?I : pp_unary_ty"
    by (rule typed_pp_identity_operator)
  have K_type: "\<Gamma> \<turnstile> ?K : pp_unary_ty"
    using typed_ObjTrue by (rule typed_pp_constant_operator)
  have I_true_type: "\<Gamma> \<turnstile> App ?I ObjTrue : Prop"
    using I_type typed_ObjTrue unfolding pp_unary_ty_def
    by (rule has_type.App)
  have K_true_type: "\<Gamma> \<turnstile> App ?K ObjTrue : Prop"
    using K_type typed_ObjTrue unfolding pp_unary_ty_def
    by (rule has_type.App)
  have K_false_type: "\<Gamma> \<turnstile> App ?K ObjFalse : Prop"
    using K_type typed_ObjFalse unfolding pp_unary_ty_def
    by (rule has_type.App)
  have I_false_type: "\<Gamma> \<turnstile> App ?I ObjFalse : Prop"
    using I_type typed_ObjFalse unfolding pp_unary_ty_def
    by (rule has_type.App)
  have d_fun:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    using A_type by (intro CEV_axiom_from.Assumption) simp
  have d_pure_I:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?I"
    using pp_identity_operator_pure_in_core_extension[OF core]
    by (rule CEV_axiom_from.Theorem)
  have d_pure_K:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?K"
    using pp_constant_ObjTrue_pure_in_core_extension[OF core]
    by (rule CEV_axiom_from.Theorem)
  have I_true_eq:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I ObjTrue) ObjTrue"
    using CEV_pp_identity_operator_apply_eq[OF typed_ObjTrue]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have K_true_eq:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?K ObjTrue) ObjTrue"
    using CEV_pp_constant_operator_apply_eq[
      OF typed_ObjTrue typed_ObjTrue]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have K_true_eq_sym:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ObjTrue (App ?K ObjTrue)"
    using K_true_type typed_ObjTrue K_true_eq
    by (rule CEV_axiom_from_eq_sym)
  have same_at_true:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I ObjTrue) (App ?K ObjTrue)"
    using I_true_type typed_ObjTrue K_true_type
      I_true_eq K_true_eq_sym
    by (rule CEV_axiom_from_eq_trans)
  have I_eq_K:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?I ?K"
    using typed_ObjTrue I_type K_type d_fun d_pure_I d_pure_K
      same_at_true
    by (rule CEV_axiom_from_fun_prime)
  have K_eq_I:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?K ?I"
    using I_type K_type I_eq_K by (rule CEV_axiom_from_eq_sym)
  have K_false_eq_I_false:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?K ObjFalse) (App ?I ObjFalse)"
    using K_type I_type typed_ObjFalse K_eq_I
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have K_false_eq_true:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?K ObjFalse) ObjTrue"
    using CEV_pp_constant_operator_apply_eq[
      OF typed_ObjTrue typed_ObjFalse]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have true_eq_K_false:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ObjTrue (App ?K ObjFalse)"
    using K_false_type typed_ObjTrue K_false_eq_true
    by (rule CEV_axiom_from_eq_sym)
  have d_true:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjTrue"
    using CEV_axiom_proves_ObjTrue by (rule CEV_axiom_from.Theorem)
  have d_K_false:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      App ?K ObjFalse"
    using typed_ObjTrue K_false_type d_true true_eq_K_false
    by (rule CEV_axiom_from_eq_prop_elim)
  have d_I_false:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      App ?I ObjFalse"
    using K_false_type I_false_type d_K_false K_false_eq_I_false
    by (rule CEV_axiom_from_eq_prop_elim)
  have I_false_eq_false:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I ObjFalse) ObjFalse"
    using CEV_pp_identity_operator_apply_eq[OF typed_ObjFalse]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_false:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using I_false_type typed_ObjFalse d_I_false I_false_eq_false
    by (rule CEV_axiom_from_eq_prop_elim)
  have A_imp_false:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?A ObjFalse"
    using A_type d_false by (rule CEV_axiom_from_singleton_imp)
  have imp_to_neg:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp ?A ObjFalse) (Neg ?A)"
    using CEV_proves_imp_false_to_neg[OF A_type]
    by (rule CEV_axiom_proves.Base)
  show ?thesis
    using A_imp_false imp_to_neg by (rule CEV_axiom_proves.MP)
qed

theorem CEV_not_fun_prime_ObjFalse:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (pp_fun_prime ObjFalse)"
proof -
  let ?I = "pp_identity_operator"
  let ?K = "pp_constant_operator ObjFalse"
  let ?A = "pp_fun_prime ObjFalse"
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using typed_ObjFalse by (rule typed_pp_fun_prime)
  have I_type: "\<Gamma> \<turnstile> ?I : pp_unary_ty"
    by (rule typed_pp_identity_operator)
  have K_type: "\<Gamma> \<turnstile> ?K : pp_unary_ty"
    using typed_ObjFalse by (rule typed_pp_constant_operator)
  have I_false_type: "\<Gamma> \<turnstile> App ?I ObjFalse : Prop"
    using I_type typed_ObjFalse unfolding pp_unary_ty_def
    by (rule has_type.App)
  have K_false_type: "\<Gamma> \<turnstile> App ?K ObjFalse : Prop"
    using K_type typed_ObjFalse unfolding pp_unary_ty_def
    by (rule has_type.App)
  have I_true_type: "\<Gamma> \<turnstile> App ?I ObjTrue : Prop"
    using I_type typed_ObjTrue unfolding pp_unary_ty_def
    by (rule has_type.App)
  have K_true_type: "\<Gamma> \<turnstile> App ?K ObjTrue : Prop"
    using K_type typed_ObjTrue unfolding pp_unary_ty_def
    by (rule has_type.App)
  have d_fun:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    using A_type by (intro CEV_axiom_from.Assumption) simp
  have d_pure_I:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?I"
    using pp_identity_operator_pure_in_core_extension[OF core]
    by (rule CEV_axiom_from.Theorem)
  have d_pure_K:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?K"
    using pp_constant_ObjFalse_pure_in_core_extension[OF core]
    by (rule CEV_axiom_from.Theorem)
  have I_false_eq:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I ObjFalse) ObjFalse"
    using CEV_pp_identity_operator_apply_eq[OF typed_ObjFalse]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have K_false_eq:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?K ObjFalse) ObjFalse"
    using CEV_pp_constant_operator_apply_eq[
      OF typed_ObjFalse typed_ObjFalse]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have K_false_eq_sym:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ObjFalse (App ?K ObjFalse)"
    using K_false_type typed_ObjFalse K_false_eq
    by (rule CEV_axiom_from_eq_sym)
  have same_at_false:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I ObjFalse) (App ?K ObjFalse)"
    using I_false_type typed_ObjFalse K_false_type
      I_false_eq K_false_eq_sym
    by (rule CEV_axiom_from_eq_trans)
  have I_eq_K:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?I ?K"
    using typed_ObjFalse I_type K_type d_fun d_pure_I d_pure_K
      same_at_false
    by (rule CEV_axiom_from_fun_prime)
  have I_true_eq_K_true:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I ObjTrue) (App ?K ObjTrue)"
    using I_type K_type typed_ObjTrue I_eq_K
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have I_true_eq_true:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I ObjTrue) ObjTrue"
    using CEV_pp_identity_operator_apply_eq[OF typed_ObjTrue]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have true_eq_I_true:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ObjTrue (App ?I ObjTrue)"
    using I_true_type typed_ObjTrue I_true_eq_true
    by (rule CEV_axiom_from_eq_sym)
  have d_true:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjTrue"
    using CEV_axiom_proves_ObjTrue by (rule CEV_axiom_from.Theorem)
  have d_I_true:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      App ?I ObjTrue"
    using typed_ObjTrue I_true_type d_true true_eq_I_true
    by (rule CEV_axiom_from_eq_prop_elim)
  have d_K_true:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      App ?K ObjTrue"
    using I_true_type K_true_type d_I_true I_true_eq_K_true
    by (rule CEV_axiom_from_eq_prop_elim)
  have K_true_eq_false:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?K ObjTrue) ObjFalse"
    using CEV_pp_constant_operator_apply_eq[
      OF typed_ObjFalse typed_ObjTrue]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_false:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using K_true_type typed_ObjFalse d_K_true K_true_eq_false
    by (rule CEV_axiom_from_eq_prop_elim)
  have A_imp_false:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?A ObjFalse"
    using A_type d_false by (rule CEV_axiom_from_singleton_imp)
  have imp_to_neg:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp ?A ObjFalse) (Neg ?A)"
    using CEV_proves_imp_false_to_neg[OF A_type]
    by (rule CEV_axiom_proves.Base)
  show ?thesis
    using A_imp_false imp_to_neg by (rule CEV_axiom_proves.MP)
qed

subsection \<open>Consequences for a \<open>fun\<acute>\<close> proposition\<close>

theorem CEV_fun_prime_neq_ObjTrue:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime p)
      (Neg (Eq Prop p ObjTrue))"
proof -
  let ?F = "pp_fun_prime p"
  let ?E = "Eq Prop p ObjTrue"
  let ?FT = "pp_fun_prime ObjTrue"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using p_type by (rule typed_pp_fun_prime)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using p_type typed_ObjTrue by (rule has_type.Eq)
  have FT_type: "\<Gamma> \<turnstile> ?FT : Prop"
    using typed_ObjTrue by (rule typed_pp_fun_prime)
  have d_F:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_E:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using E_type by (intro CEV_axiom_from.Assumption) simp
  have transport:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?E (Imp ?F ?FT)"
    using CEV_axiom_fun_prime_eq_transport[
      OF p_type typed_ObjTrue, where T = T]
    by (rule CEV_axiom_from.Theorem)
  have F_imp_FT:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F ?FT"
    using d_E transport by (rule CEV_axiom_from.MP)
  have d_FT:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?FT"
    using d_F F_imp_FT by (rule CEV_axiom_from.MP)
  have d_not_FT:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?FT"
    using CEV_not_fun_prime_ObjTrue[OF core]
    by (rule CEV_axiom_from.Theorem)
  have d_false:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_FT d_not_FT by (rule CEV_axiom_from_contradiction)
  have E_imp_false:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?E ObjFalse"
    using E_type d_false by (rule CEV_axiom_from_deduction)
  have imp_to_neg:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?E ObjFalse) (Neg ?E)"
    using CEV_proves_imp_false_to_neg[OF E_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_not_E:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?E"
    using E_imp_false imp_to_neg by (rule CEV_axiom_from.MP)
  show ?thesis
    using F_type d_not_E by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_fun_prime_neq_ObjFalse:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime p)
      (Neg (Eq Prop p ObjFalse))"
proof -
  let ?F = "pp_fun_prime p"
  let ?E = "Eq Prop p ObjFalse"
  let ?FF = "pp_fun_prime ObjFalse"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using p_type by (rule typed_pp_fun_prime)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using p_type typed_ObjFalse by (rule has_type.Eq)
  have FF_type: "\<Gamma> \<turnstile> ?FF : Prop"
    using typed_ObjFalse by (rule typed_pp_fun_prime)
  have d_F:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_E:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using E_type by (intro CEV_axiom_from.Assumption) simp
  have transport:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?E (Imp ?F ?FF)"
    using CEV_axiom_fun_prime_eq_transport[
      OF p_type typed_ObjFalse, where T = T]
    by (rule CEV_axiom_from.Theorem)
  have F_imp_FF:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F ?FF"
    using d_E transport by (rule CEV_axiom_from.MP)
  have d_FF:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?FF"
    using d_F F_imp_FF by (rule CEV_axiom_from.MP)
  have d_not_FF:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?FF"
    using CEV_not_fun_prime_ObjFalse[OF core]
    by (rule CEV_axiom_from.Theorem)
  have d_false:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_FF d_not_FF by (rule CEV_axiom_from_contradiction)
  have E_imp_false:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?E ObjFalse"
    using E_type d_false by (rule CEV_axiom_from_deduction)
  have imp_to_neg:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?E ObjFalse) (Neg ?E)"
    using CEV_proves_imp_false_to_neg[OF E_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_not_E:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?E"
    using E_imp_false imp_to_neg by (rule CEV_axiom_from.MP)
  show ?thesis
    using F_type d_not_E by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_bare_no_proposition_identical_to_its_negation:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Neg (Eq Prop p (Neg p))"
proof -
  let ?E = "Eq Prop p (Neg p)"
  let ?B = "p \<longleftrightarrow>\<^sub>o Neg p"
  have neg_p_type: "\<Gamma> \<turnstile> Neg p : Prop"
    using p_type by (rule has_type.Neg)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using p_type neg_p_type by (rule has_type.Eq)
  have B_type: "\<Gamma> \<turnstile> ?B : Prop"
    using p_type neg_p_type by auto
  have eq_to_bicond:
    "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E ?B"
    using p_type neg_p_type by (rule CEV_eq_prop_biconditional_imp)
  have impossible:
    "\<Gamma> \<turnstile>\<^sub>CEV Imp ?B ObjFalse"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma> (Imp ?B ObjFalse)"
      unfolding prop_tautology_def
      using B_type typed_ObjFalse by auto
  qed
  have E_imp_false:
    "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E ObjFalse"
    using E_type B_type typed_ObjFalse eq_to_bicond impossible
    by (rule CEV_imp_trans)
  have imp_to_neg:
    "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp ?E ObjFalse) (Neg ?E)"
    using E_type by (rule CEV_proves_imp_false_to_neg)
  show ?thesis
    using E_imp_false imp_to_neg by (rule CEV_proves.MP)
qed

theorem CEV_no_proposition_identical_to_its_negation:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Neg (Eq Prop p (Neg p))"
  using CEV_bare_no_proposition_identical_to_its_negation[OF p_type]
  by (rule CEV_axiom_proves.Base)

definition pp_T2b_nontriviality :: "oterm \<Rightarrow> oterm" where
  "pp_T2b_nontriviality p =
    Conj
      (Neg (Eq Prop p ObjTrue))
      (Conj
        (Neg (Eq Prop p ObjFalse))
        (Neg (Eq Prop p (Neg p))))"

lemma typed_pp_T2b_nontriviality:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile> pp_T2b_nontriviality p : Prop"
  unfolding pp_T2b_nontriviality_def
  using p_type typed_ObjTrue typed_ObjFalse
  by (intro has_type.Conj has_type.Neg has_type.Eq)

theorem CEV_Goodman_T2b:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime p)
      (pp_T2b_nontriviality p)"
proof -
  let ?F = "pp_fun_prime p"
  let ?NT = "Neg (Eq Prop p ObjTrue)"
  let ?NF = "Neg (Eq Prop p ObjFalse)"
  let ?NN = "Neg (Eq Prop p (Neg p))"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using p_type by (rule typed_pp_fun_prime)
  have NT_type: "\<Gamma> \<turnstile> ?NT : Prop"
    using p_type typed_ObjTrue by auto
  have NF_type: "\<Gamma> \<turnstile> ?NF : Prop"
    using p_type typed_ObjFalse by auto
  have NN_type: "\<Gamma> \<turnstile> ?NN : Prop"
    using p_type by auto
  have d_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have imp_NT:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?F ?NT"
    using CEV_fun_prime_neq_ObjTrue[OF core p_type]
    by (rule CEV_axiom_from.Theorem)
  have imp_NF:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?F ?NF"
    using CEV_fun_prime_neq_ObjFalse[OF core p_type]
    by (rule CEV_axiom_from.Theorem)
  have d_NT:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?NT"
    using d_F imp_NT by (rule CEV_axiom_from.MP)
  have d_NF:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?NF"
    using d_F imp_NF by (rule CEV_axiom_from.MP)
  have d_NN:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?NN"
    using CEV_no_proposition_identical_to_its_negation[OF p_type]
    by (rule CEV_axiom_from.Theorem)
  have d_tail:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj ?NF ?NN"
    using d_NF d_NN by (rule CEV_axiom_from_conj_intro)
  have d_all:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T2b_nontriviality p"
    unfolding pp_T2b_nontriviality_def
    using d_NT d_tail by (rule CEV_axiom_from_conj_intro)
  show ?thesis
    using F_type d_all by (rule CEV_axiom_from_singleton_imp)
qed

end
