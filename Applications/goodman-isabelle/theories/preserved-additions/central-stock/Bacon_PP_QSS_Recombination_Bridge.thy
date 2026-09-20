theory Bacon_PP_QSS_Recombination_Bridge
  imports
    
    "Goodman_Legacy_06.Bacon_PP_Goodman_T6_RS"
    "Goodman_Legacy_04.Bacon_PP_Goodman_Heredity_Exhaustion"
begin

section \<open>The Recombination--QSS bridge\<close>

text \<open>
  Bacon's printed QSS argument first uses unary Recombination to pass from
  necessary agreement at a fundamental proposition to pointwise agreement.
  It then applies zeroary QLN to the resulting constant-free universal
  proposition.  In the split used by this development, that second step is
  zeroary Exhaustion.  The present theory separates the Recombination-only
  modal core from the Exhaustion repair.
\<close>

subsection \<open>Closed pointwise-identity builders\<close>

definition pp_pointwise_identity_operator_builder :: oterm where
  "pp_pointwise_identity_operator_builder =
    Lam pp_unary_ty
      (Lam pp_unary_ty
        (Lam Prop
          (Eq Prop
            (App (Var 2) (Var 0))
            (App (Var 1) (Var 0)))))"

definition pp_pointwise_identity_operator_instance ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_pointwise_identity_operator_instance X Y =
    App (App pp_pointwise_identity_operator_builder X) Y"

definition pp_pointwise_identity_operator ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_pointwise_identity_operator X Y =
    Lam Prop
      (Eq Prop
        (App (shift X) (Var 0))
        (App (shift Y) (Var 0)))"

definition pp_pointwise_identity_sentence_builder :: oterm where
  "pp_pointwise_identity_sentence_builder =
    Lam pp_unary_ty
      (Lam pp_unary_ty
        (Forall Prop
          (Eq Prop
            (App (Var 2) (Var 0))
            (App (Var 1) (Var 0)))))"

definition pp_pointwise_identity_sentence_instance ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_pointwise_identity_sentence_instance X Y =
    App (App pp_pointwise_identity_sentence_builder X) Y"

definition pp_pointwise_necessary_identity ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_pointwise_necessary_identity X Y =
    Forall Prop
      (\<box>\<^sub>o
        (Eq Prop
          (App (shift X) (Var 0))
          (App (shift Y) (Var 0))))"

lemma typed_pp_pointwise_identity_operator_builder:
  "\<Gamma> \<turnstile> pp_pointwise_identity_operator_builder :
    pp_unary_ty \<rightarrow>\<^sub>o
      (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty)"
  by (rule infer_type_sound)
    (simp add: pp_pointwise_identity_operator_builder_def
      pp_unary_ty_def lookup_def)

lemma typed_pp_pointwise_identity_operator_instance:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_pointwise_identity_operator_instance X Y :
    pp_unary_ty"
  unfolding pp_pointwise_identity_operator_instance_def
  using typed_pp_pointwise_identity_operator_builder X_type Y_type
  by (meson has_type.App)

lemma typed_pp_pointwise_identity_operator:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_pointwise_identity_operator X Y : pp_unary_ty"
  unfolding pp_pointwise_identity_operator_def pp_unary_ty_def
  using typed_shift_app[OF X_type[unfolded pp_unary_ty_def]]
    typed_shift_app[OF Y_type[unfolded pp_unary_ty_def]]
  by (intro has_type.Lam has_type.Eq)

lemma typed_pp_pointwise_identity_sentence_builder:
  "\<Gamma> \<turnstile> pp_pointwise_identity_sentence_builder :
    pp_unary_ty \<rightarrow>\<^sub>o
      (pp_unary_ty \<rightarrow>\<^sub>o Prop)"
  by (rule infer_type_sound)
    (simp add: pp_pointwise_identity_sentence_builder_def
      pp_unary_ty_def lookup_def)

lemma typed_pp_pointwise_identity_sentence_instance:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_pointwise_identity_sentence_instance X Y : Prop"
  unfolding pp_pointwise_identity_sentence_instance_def
  using typed_pp_pointwise_identity_sentence_builder X_type Y_type
  by (meson has_type.App)

lemma typed_pp_pointwise_necessary_identity:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_pointwise_necessary_identity X Y : Prop"
  unfolding pp_pointwise_necessary_identity_def
  using typed_shift_app[OF X_type[unfolded pp_unary_ty_def]]
    typed_shift_app[OF Y_type[unfolded pp_unary_ty_def]]
  by (intro has_type.Forall typed_ObjBox has_type.Eq)

lemma pp_pointwise_identity_operator_builder_constant_free:
  "consts_of pp_pointwise_identity_operator_builder = {}"
  by (simp add: pp_pointwise_identity_operator_builder_def)

lemma pp_pointwise_identity_sentence_builder_constant_free:
  "consts_of pp_pointwise_identity_sentence_builder = {}"
  by (simp add: pp_pointwise_identity_sentence_builder_def)

lemma pp_pointwise_identity_operator_builder_purity_axiom:
  "pp_pure
      (pp_unary_ty \<rightarrow>\<^sub>o
        (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty))
      pp_pointwise_identity_operator_builder
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_pointwise_identity_operator_builder :
      pp_unary_ty \<rightarrow>\<^sub>o
        (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty)"
    by (rule typed_pp_pointwise_identity_operator_builder)
  show "consts_of pp_pointwise_identity_operator_builder = {}"
    by (rule pp_pointwise_identity_operator_builder_constant_free)
  show "pp_pure
      (pp_unary_ty \<rightarrow>\<^sub>o
        (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty))
      pp_pointwise_identity_operator_builder =
    pp_pure
      (pp_unary_ty \<rightarrow>\<^sub>o
        (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty))
      pp_pointwise_identity_operator_builder"
    by simp
qed

lemma pp_pointwise_identity_sentence_builder_purity_axiom:
  "pp_pure
      (pp_unary_ty \<rightarrow>\<^sub>o
        (pp_unary_ty \<rightarrow>\<^sub>o Prop))
      pp_pointwise_identity_sentence_builder
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_pointwise_identity_sentence_builder :
      pp_unary_ty \<rightarrow>\<^sub>o
        (pp_unary_ty \<rightarrow>\<^sub>o Prop)"
    by (rule typed_pp_pointwise_identity_sentence_builder)
  show "consts_of pp_pointwise_identity_sentence_builder = {}"
    by (rule pp_pointwise_identity_sentence_builder_constant_free)
  show "pp_pure
      (pp_unary_ty \<rightarrow>\<^sub>o
        (pp_unary_ty \<rightarrow>\<^sub>o Prop))
      pp_pointwise_identity_sentence_builder =
    pp_pure
      (pp_unary_ty \<rightarrow>\<^sub>o
        (pp_unary_ty \<rightarrow>\<^sub>o Prop))
      pp_pointwise_identity_sentence_builder"
    by simp
qed

subsection \<open>Beta conversion certificates\<close>

lemma pp_pointwise_identity_operator_instance_first_beta:
  "compatible_step beta_contract
    (pp_pointwise_identity_operator_instance X Y)
    (App
      (Lam pp_unary_ty
        (pp_pointwise_identity_operator (shift X) (Var 0)))
      Y)"
  unfolding pp_pointwise_identity_operator_instance_def
proof (rule compatible_step.App_left, rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty
          (Lam pp_unary_ty
            (Lam Prop
              (Eq Prop
                (App (Var 2) (Var 0))
                (App (Var 1) (Var 0))))))
        X)
      (subst0 X
        (Lam pp_unary_ty
          (Lam Prop
            (Eq Prop
              (App (Var 2) (Var 0))
              (App (Var 1) (Var 0))))))"
    by (rule beta_contract.beta)
  show "beta_contract
      (App pp_pointwise_identity_operator_builder X)
      (Lam pp_unary_ty
        (pp_pointwise_identity_operator (shift X) (Var 0)))"
    using step
    by (simp add: pp_pointwise_identity_operator_builder_def
      pp_pointwise_identity_operator_def subst0_def shift_def)
qed

lemma pp_pointwise_identity_operator_instance_second_beta:
  "compatible_step beta_contract
    (App
      (Lam pp_unary_ty
        (pp_pointwise_identity_operator (shift X) (Var 0)))
      Y)
    (pp_pointwise_identity_operator X Y)"
proof -
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty
          (pp_pointwise_identity_operator (shift X) (Var 0)))
        Y)
      (subst0 Y
        (pp_pointwise_identity_operator (shift X) (Var 0)))"
    by (rule beta_contract.beta)
  have nested_X:
    "subst (lift_subst (case_nat Y Var)) (shift (shift X)) = shift X"
    using subst_lift_shift[of "case_nat Y Var" "shift X"]
    by (simp add: subst0_def)
  have beta:
    "beta_contract
      (App
        (Lam pp_unary_ty
          (pp_pointwise_identity_operator (shift X) (Var 0)))
        Y)
      (pp_pointwise_identity_operator X Y)"
    using step nested_X
    by (simp add: pp_pointwise_identity_operator_def
      subst0_def shift_def)
  show ?thesis
    by (rule compatible_step.root, rule beta)
qed

lemma pp_pointwise_identity_operator_apply_beta:
  "compatible_step beta_contract
    (App (pp_pointwise_identity_operator X Y) p)
    (Eq Prop (App X p) (App Y p))"
proof -
  have step:
    "beta_contract
      (App
        (Lam Prop
          (Eq Prop
            (App (shift X) (Var 0))
            (App (shift Y) (Var 0))))
        p)
      (subst0 p
        (Eq Prop
          (App (shift X) (Var 0))
          (App (shift Y) (Var 0))))"
    by (rule beta_contract.beta)
  have rhs:
    "subst0 p
        (Eq Prop
          (App (shift X) (Var 0))
          (App (shift Y) (Var 0))) =
      Eq Prop (App X p) (App Y p)"
  proof -
    have X_inv:
      "subst (case_nat p Var) (rename Suc X) = X"
      using subst0_shift[of p X]
      by (simp add: subst0_def shift_def)
    have Y_inv:
      "subst (case_nat p Var) (rename Suc Y) = Y"
      using subst0_shift[of p Y]
      by (simp add: subst0_def shift_def)
    show ?thesis
      by (simp add: subst0_def shift_def X_inv Y_inv)
  qed
  have beta:
    "beta_contract
      (App (pp_pointwise_identity_operator X Y) p)
      (Eq Prop (App X p) (App Y p))"
    using step rhs
    by (simp add: pp_pointwise_identity_operator_def)
  show ?thesis
    by (rule compatible_step.root, rule beta)
qed

lemma shift_pp_pointwise_identity_operator_instance[simp]:
  "shift (pp_pointwise_identity_operator_instance X Y) =
    pp_pointwise_identity_operator_instance (shift X) (shift Y)"
  by (simp add: shift_def pp_pointwise_identity_operator_instance_def
    pp_pointwise_identity_operator_builder_def)

lemma CEV_pp_pointwise_identity_operator_instance_apply:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    (App (pp_pointwise_identity_operator_instance X Y) p
      \<longleftrightarrow>\<^sub>o
     Eq Prop (App X p) (App Y p))"
proof -
  let ?I = "pp_pointwise_identity_operator_instance X Y"
  let ?M =
    "App
      (Lam pp_unary_ty
        (pp_pointwise_identity_operator (shift X) (Var 0)))
      Y"
  let ?F = "pp_pointwise_identity_operator X Y"
  let ?A = "App ?I p"
  let ?B = "App ?M p"
  let ?C = "App ?F p"
  let ?E = "Eq Prop (App X p) (App Y p)"
  have I_type: "\<Gamma> \<turnstile> ?I : pp_unary_ty"
    using X_type Y_type by (rule typed_pp_pointwise_identity_operator_instance)
  have X_shift: "pp_unary_ty # \<Gamma> \<turnstile> shift X : pp_unary_ty"
    using X_type by (rule typed_shift_ctx)
  have v_type: "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
    by (rule typed_var0)
  have body_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      pp_pointwise_identity_operator (shift X) (Var 0) : pp_unary_ty"
    using X_shift v_type by (rule typed_pp_pointwise_identity_operator)
  have M_type: "\<Gamma> \<turnstile> ?M : pp_unary_ty"
    using has_type.Lam[OF body_type] Y_type by (rule has_type.App)
  have F_type: "\<Gamma> \<turnstile> ?F : pp_unary_ty"
    using X_type Y_type by (rule typed_pp_pointwise_identity_operator)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using I_type p_type unfolding pp_unary_ty_def by (rule has_type.App)
  have B_type: "\<Gamma> \<turnstile> ?B : Prop"
    using M_type p_type unfolding pp_unary_ty_def by (rule has_type.App)
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using F_type p_type unfolding pp_unary_ty_def by (rule has_type.App)
  have Xp_type: "\<Gamma> \<turnstile> App X p : Prop"
    using X_type p_type unfolding pp_unary_ty_def by (rule has_type.App)
  have Yp_type: "\<Gamma> \<turnstile> App Y p : Prop"
    using Y_type p_type unfolding pp_unary_ty_def by (rule has_type.App)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using Xp_type Yp_type by (rule has_type.Eq)
  have first: "\<Gamma> \<turnstile>\<^sub>CEV (?A \<longleftrightarrow>\<^sub>o ?B)"
    using A_type B_type
      compatible_step.App_left[
        OF pp_pointwise_identity_operator_instance_first_beta]
    by (rule CEV_beta_step)
  have second: "\<Gamma> \<turnstile>\<^sub>CEV (?B \<longleftrightarrow>\<^sub>o ?C)"
    using B_type C_type
      compatible_step.App_left[
        OF pp_pointwise_identity_operator_instance_second_beta]
    by (rule CEV_beta_step)
  have third: "\<Gamma> \<turnstile>\<^sub>CEV (?C \<longleftrightarrow>\<^sub>o ?E)"
    using C_type E_type
      pp_pointwise_identity_operator_apply_beta
    by (rule CEV_beta_step)
  have first_two: "\<Gamma> \<turnstile>\<^sub>CEV (?A \<longleftrightarrow>\<^sub>o ?C)"
    using A_type B_type C_type first second
    by (rule CEV_biconditional_trans)
  show ?thesis
    using A_type C_type E_type first_two third
    by (rule CEV_biconditional_trans)
qed

lemma pp_pointwise_identity_sentence_instance_first_beta:
  "compatible_step beta_contract
    (pp_pointwise_identity_sentence_instance X Y)
    (App (Lam pp_unary_ty (mf_condition Prop (shift X) (Var 0))) Y)"
  unfolding pp_pointwise_identity_sentence_instance_def
proof (rule compatible_step.App_left, rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty
          (Lam pp_unary_ty
            (Forall Prop
              (Eq Prop
                (App (Var 2) (Var 0))
                (App (Var 1) (Var 0))))))
        X)
      (subst0 X
        (Lam pp_unary_ty
          (Forall Prop
            (Eq Prop
              (App (Var 2) (Var 0))
              (App (Var 1) (Var 0))))))"
    by (rule beta_contract.beta)
  show "beta_contract
      (App pp_pointwise_identity_sentence_builder X)
      (Lam pp_unary_ty (mf_condition Prop (shift X) (Var 0)))"
    using step
    by (simp add: pp_pointwise_identity_sentence_builder_def
      mf_condition_def subst0_def shift_def)
qed

lemma pp_pointwise_identity_sentence_instance_second_beta:
  "compatible_step beta_contract
    (App (Lam pp_unary_ty (mf_condition Prop (shift X) (Var 0))) Y)
    (mf_condition Prop X Y)"
proof -
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty (mf_condition Prop (shift X) (Var 0)))
        Y)
      (subst0 Y (mf_condition Prop (shift X) (Var 0)))"
    by (rule beta_contract.beta)
  have nested_X:
    "subst (lift_subst (case_nat Y Var)) (shift (shift X)) = shift X"
    using subst_lift_shift[of "case_nat Y Var" "shift X"]
    by (simp add: subst0_def)
  have beta:
    "beta_contract
      (App (Lam pp_unary_ty (mf_condition Prop (shift X) (Var 0))) Y)
      (mf_condition Prop X Y)"
    using step nested_X
    by (simp add: mf_condition_def subst0_def shift_def)
  show ?thesis
    by (rule compatible_step.root, rule beta)
qed

lemma CEV_pp_pointwise_identity_sentence_instance_eq:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop
      (pp_pointwise_identity_sentence_instance X Y)
      (mf_condition Prop X Y)"
proof -
  let ?I = "pp_pointwise_identity_sentence_instance X Y"
  let ?M =
    "App (Lam pp_unary_ty (mf_condition Prop (shift X) (Var 0))) Y"
  let ?E = "mf_condition Prop X Y"
  have I_type: "\<Gamma> \<turnstile> ?I : Prop"
    using X_type Y_type by (rule typed_pp_pointwise_identity_sentence_instance)
  have X_shift: "pp_unary_ty # \<Gamma> \<turnstile> shift X : pp_unary_ty"
    using X_type by (rule typed_shift_ctx)
  have v_type: "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
    by (rule typed_var0)
  have body_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      mf_condition Prop (shift X) (Var 0) : Prop"
    using X_shift v_type
    unfolding pp_unary_ty_def
    by (rule typed_mf_condition)
  have M_type: "\<Gamma> \<turnstile> ?M : Prop"
    using has_type.Lam[OF body_type] Y_type by (rule has_type.App)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using X_type Y_type
    unfolding pp_unary_ty_def
    by (rule typed_mf_condition)
  have first: "\<Gamma> \<turnstile>\<^sub>CEV (?I \<longleftrightarrow>\<^sub>o ?M)"
    using I_type M_type
      pp_pointwise_identity_sentence_instance_first_beta
    by (rule CEV_beta_step)
  have second: "\<Gamma> \<turnstile>\<^sub>CEV (?M \<longleftrightarrow>\<^sub>o ?E)"
    using M_type E_type
      pp_pointwise_identity_sentence_instance_second_beta
    by (rule CEV_beta_step)
  have both: "\<Gamma> \<turnstile>\<^sub>CEV (?I \<longleftrightarrow>\<^sub>o ?E)"
    using I_type M_type E_type first second
    by (rule CEV_biconditional_trans)
  show ?thesis
    using I_type E_type both by (rule CEV_zeroary_equivalence)
qed

lemma CEV_pp_pointwise_identity_operator_instance_forall:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    (Forall Prop
      (App
        (shift (pp_pointwise_identity_operator_instance X Y))
        (Var 0))
      \<longleftrightarrow>\<^sub>o
     mf_condition Prop X Y)"
proof -
  let ?I = "pp_pointwise_identity_operator_instance X Y"
  let ?M =
    "App
      (Lam pp_unary_ty
        (pp_pointwise_identity_operator (shift (shift X)) (Var 0)))
      (shift Y)"
  let ?F = "pp_pointwise_identity_operator (shift X) (shift Y)"
  let ?A = "Forall Prop (App (shift ?I) (Var 0))"
  let ?B = "Forall Prop (App ?M (Var 0))"
  let ?C = "Forall Prop (App ?F (Var 0))"
  let ?E = "mf_condition Prop X Y"
  have X_shift: "Prop # \<Gamma> \<turnstile> shift X : pp_unary_ty"
    using X_type by (rule typed_shift_ctx)
  have Y_shift: "Prop # \<Gamma> \<turnstile> shift Y : pp_unary_ty"
    using Y_type by (rule typed_shift_ctx)
  have I_shift:
    "Prop # \<Gamma> \<turnstile> shift ?I : pp_unary_ty"
    using typed_pp_pointwise_identity_operator_instance[OF X_type Y_type]
    by (rule typed_shift_ctx)
  have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using I_shift v_type unfolding pp_unary_ty_def
    by (intro has_type.Forall has_type.App)
  have X_shift2:
    "pp_unary_ty # Prop # \<Gamma> \<turnstile> shift (shift X) : pp_unary_ty"
    using X_shift by (rule typed_shift_ctx)
  have op_v:
    "pp_unary_ty # Prop # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
    by (rule typed_var0)
  have M_type: "Prop # \<Gamma> \<turnstile> ?M : pp_unary_ty"
    using has_type.Lam[
        OF typed_pp_pointwise_identity_operator[OF X_shift2 op_v]]
      Y_shift
    by (rule has_type.App)
  have B_body: "Prop # \<Gamma> \<turnstile> App ?M (Var 0) : Prop"
    using M_type v_type
    unfolding pp_unary_ty_def
    by (rule has_type.App)
  have B_type: "\<Gamma> \<turnstile> ?B : Prop"
    using B_body by (rule has_type.Forall)
  have F_type: "Prop # \<Gamma> \<turnstile> ?F : pp_unary_ty"
    using X_shift Y_shift by (rule typed_pp_pointwise_identity_operator)
  have C_body: "Prop # \<Gamma> \<turnstile> App ?F (Var 0) : Prop"
    using F_type v_type
    unfolding pp_unary_ty_def
    by (rule has_type.App)
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using C_body by (rule has_type.Forall)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using X_type Y_type unfolding pp_unary_ty_def
    by (rule typed_mf_condition)
  have first_step:
    "compatible_step beta_contract ?A ?B"
    using compatible_step.Forall_body[
        OF compatible_step.App_left[
          OF pp_pointwise_identity_operator_instance_first_beta[
            of "shift X" "shift Y"]]]
    by simp
  have first: "\<Gamma> \<turnstile>\<^sub>CEV (?A \<longleftrightarrow>\<^sub>o ?B)"
    using A_type B_type first_step
    by (rule CEV_beta_step)
  have second_step:
    "compatible_step beta_contract ?B ?C"
    using compatible_step.Forall_body[
        OF compatible_step.App_left[
          OF pp_pointwise_identity_operator_instance_second_beta[
            of "shift X" "shift Y"]]]
    by simp
  have second: "\<Gamma> \<turnstile>\<^sub>CEV (?B \<longleftrightarrow>\<^sub>o ?C)"
    using B_type C_type second_step
    by (rule CEV_beta_step)
  have third: "\<Gamma> \<turnstile>\<^sub>CEV (?C \<longleftrightarrow>\<^sub>o ?E)"
  proof -
    have step:
      "compatible_step beta_contract
        ?C
        (Forall Prop
          (Eq Prop
            (App (shift X) (Var 0))
            (App (shift Y) (Var 0))))"
      by (intro compatible_step.Forall_body
          pp_pointwise_identity_operator_apply_beta)
    show ?thesis
      using C_type E_type step
      by (simp add: mf_condition_def CEV_beta_step)
  qed
  have first_two: "\<Gamma> \<turnstile>\<^sub>CEV (?A \<longleftrightarrow>\<^sub>o ?C)"
    using A_type B_type C_type first second
    by (rule CEV_biconditional_trans)
  show ?thesis
    using A_type C_type E_type first_two third
    by (rule CEV_biconditional_trans)
qed

subsection \<open>Unary Recombination in an arbitrary axiom extension\<close>

lemma CEV_axiom_unary_recombination_instance:
  assumes recombination: "pp_unary_recombination \<in> T"
    and F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure pp_unary_ty F)
        (pp_fun Prop r))
      (Imp
        (\<box>\<^sub>o (App F r))
        (Forall Prop (App (shift F) (Var 0))))"
proof -
  have qln_type: "\<Gamma> \<turnstile> pp_unary_recombination : Prop"
    by (rule infer_type_sound)
      (simp add: pp_unary_recombination_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)
  have d_qln: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_unary_recombination"
    using recombination qln_type by (rule CEV_axiom_proves.Axiom)
  have F_raw: "\<Gamma> \<turnstile> F : Prop \<rightarrow>\<^sub>o Prop"
    using F_type unfolding pp_unary_ty_def .
  have d_outer_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 F
        (Forall Prop
          (Imp
            (Conj
              (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
              (pp_fun Prop (Var 0)))
            (Imp
              (\<box>\<^sub>o (App (Var 1) (Var 0)))
              (Forall Prop (App (Var 2) (Var 0))))))"
    using qln_type F_raw d_qln
    unfolding pp_unary_recombination_def
    by (rule CEV_axiom_UI_typed)
  have d_outer:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift F))
            (pp_fun Prop (Var 0)))
          (Imp
            (\<box>\<^sub>o (App (shift F) (Var 0)))
            (Forall Prop (App (shift (shift F)) (Var 0)))))"
    using d_outer_raw
    by (simp add: pp_unary_ty_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def
        subst0_def shift_def)
  have outer_type:
    "\<Gamma> \<turnstile>
      Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift F))
            (pp_fun Prop (Var 0)))
          (Imp
            (\<box>\<^sub>o (App (shift F) (Var 0)))
            (Forall Prop (App (shift (shift F)) (Var 0))))) : Prop"
    using d_outer by (rule CEV_axiom_proves_formula)
  have d_inner_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 r
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift F))
            (pp_fun Prop (Var 0)))
          (Imp
            (\<box>\<^sub>o (App (shift F) (Var 0)))
            (Forall Prop (App (shift (shift F)) (Var 0)))))"
    using outer_type r_type d_outer by (rule CEV_axiom_UI_typed)
  have cancel_F:
    "subst (case_nat r Var) (shift F) = F"
    using subst0_shift[of r F]
    unfolding subst0_def .
  have cancel_F2:
    "subst (lift_subst (case_nat r Var)) (shift (shift F)) = shift F"
    using subst_lift_shift[of "case_nat r Var" "shift F"] cancel_F
    by (simp add: subst0_def)
  show ?thesis
    using d_inner_raw
    by (simp add: pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def
        ObjBox_def ObjTrue_def subst0_def cancel_F cancel_F2)
qed

subsection \<open>Purity of the pointwise-identity constructions\<close>

lemma CEV_axiom_from_pure_pointwise_identity_operator_instance:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and pure_X:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty X"
    and pure_Y:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Y"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_unary_ty
      (pp_pointwise_identity_operator_instance X Y)"
proof -
  let ?bty =
    "pp_unary_ty \<rightarrow>\<^sub>o
      (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty)"
  let ?ity = "pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
  have builder_in:
    "pp_pure ?bty pp_pointwise_identity_operator_builder \<in> T"
    using pp_pointwise_identity_operator_builder_purity_axiom core
    unfolding pp_T6_core_PP_axioms_def by blast
  have builder_type:
    "\<Gamma> \<turnstile> pp_pointwise_identity_operator_builder : ?bty"
    by (rule typed_pp_pointwise_identity_operator_builder)
  have builder_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure ?bty pp_pointwise_identity_operator_builder"
    using builder_in typed_pp_pure[OF builder_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  have closure1: "pp_application_closure pp_unary_ty ?ity \<in> T"
    using pp_T6_application_closure_axiom core by blast
  have first_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure ?ity
        (App pp_pointwise_identity_operator_builder X)"
    using closure1 builder_type X_type builder_pure pure_X
    by (rule pp_axiom_application_closed_from)
  have first_type:
    "\<Gamma> \<turnstile>
      App pp_pointwise_identity_operator_builder X : ?ity"
    using builder_type X_type by (rule has_type.App)
  have closure2:
    "pp_application_closure pp_unary_ty pp_unary_ty \<in> T"
    using pp_T6_application_closure_axiom core by blast
  show ?thesis
    unfolding pp_pointwise_identity_operator_instance_def
    using closure2 first_type Y_type first_pure pure_Y
    by (rule pp_axiom_application_closed_from)
qed

lemma CEV_axiom_from_pure_mf_condition:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and pure_X:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty X"
    and pure_Y:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Y"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure Prop (mf_condition Prop X Y)"
proof -
  let ?bty =
    "pp_unary_ty \<rightarrow>\<^sub>o
      (pp_unary_ty \<rightarrow>\<^sub>o Prop)"
  let ?ity = "pp_unary_ty \<rightarrow>\<^sub>o Prop"
  let ?I = "pp_pointwise_identity_sentence_instance X Y"
  let ?E = "mf_condition Prop X Y"
  have builder_in:
    "pp_pure ?bty pp_pointwise_identity_sentence_builder \<in> T"
    using pp_pointwise_identity_sentence_builder_purity_axiom core
    unfolding pp_T6_core_PP_axioms_def by blast
  have builder_type:
    "\<Gamma> \<turnstile> pp_pointwise_identity_sentence_builder : ?bty"
    by (rule typed_pp_pointwise_identity_sentence_builder)
  have builder_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure ?bty pp_pointwise_identity_sentence_builder"
    using builder_in typed_pp_pure[OF builder_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  have closure1: "pp_application_closure pp_unary_ty ?ity \<in> T"
    using pp_T6_application_closure_axiom core by blast
  have first_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure ?ity
        (App pp_pointwise_identity_sentence_builder X)"
    using closure1 builder_type X_type builder_pure pure_X
    by (rule pp_axiom_application_closed_from)
  have first_type:
    "\<Gamma> \<turnstile>
      App pp_pointwise_identity_sentence_builder X : ?ity"
    using builder_type X_type by (rule has_type.App)
  have closure2: "pp_application_closure pp_unary_ty Prop \<in> T"
    using pp_T6_application_closure_axiom core by blast
  have instance_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop ?I"
    unfolding pp_pointwise_identity_sentence_instance_def
    using closure2 first_type Y_type first_pure pure_Y
    by (rule pp_axiom_application_closed_from)
  have I_type: "\<Gamma> \<turnstile> ?I : Prop"
    using X_type Y_type by
      (rule typed_pp_pointwise_identity_sentence_instance)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using X_type Y_type unfolding pp_unary_ty_def
    by (rule typed_mf_condition)
  have instance_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?I ?E"
    using CEV_pp_pointwise_identity_sentence_instance_eq[
        OF X_type Y_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using I_type E_type instance_pure instance_eq
    by (rule CEV_axiom_from_pure_eq_transport)
qed

subsection \<open>The strongest Recombination-only consequence\<close>

lemma CEV_mf_condition_implies_pointwise_necessary_identity:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp
      (mf_condition Prop X Y)
      (pp_pointwise_necessary_identity X Y)"
proof -
  let ?E = "mf_condition Prop X Y"
  let ?A = "App (shift X) (Var 0)"
  let ?B = "App (shift Y) (Var 0)"
  let ?Q = "\<box>\<^sub>o (Eq Prop ?A ?B)"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using X_type Y_type unfolding pp_unary_ty_def
    by (rule typed_mf_condition)
  have X_shift: "Prop # \<Gamma> \<turnstile> shift X : pp_unary_ty"
    using X_type by (rule typed_shift_ctx)
  have Y_shift: "Prop # \<Gamma> \<turnstile> shift Y : pp_unary_ty"
    using Y_type by (rule typed_shift_ctx)
  have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have A_type: "Prop # \<Gamma> \<turnstile> ?A : Prop"
    using X_shift v_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have B_type: "Prop # \<Gamma> \<turnstile> ?B : Prop"
    using Y_shift v_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have eq_type:
    "Prop # \<Gamma> \<turnstile> Eq Prop ?A ?B : Prop"
    using A_type B_type by (rule has_type.Eq)
  have Q_type: "Prop # \<Gamma> \<turnstile> ?Q : Prop"
    using eq_type by (rule typed_ObjBox)
  have ui:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?E) (Eq Prop ?A ?B)"
    using X_type[unfolded pp_unary_ty_def]
      Y_type[unfolded pp_unary_ty_def]
    by (rule CEV_mf_condition_UI)
  have rigid:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Eq Prop ?A ?B) ?Q"
    using CEV_eq_truth_of_eq[OF A_type B_type]
    by (simp add: ObjBox_def)
  have lifted:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV Imp (shift ?E) ?Q"
    using typed_shift_ctx[OF E_type] eq_type Q_type ui rigid
    by (rule CEV_imp_trans)
  have result:
    "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E (Forall Prop ?Q)"
    using E_type Q_type lifted by (rule CEV_proves.Gen)
  show ?thesis
    using result unfolding pp_pointwise_necessary_identity_def .
qed

theorem CEV_QSS_modal_core_from_recombination:
  assumes recombination_stock: "pp_recombination_PP_axioms \<subseteq> T"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure pp_unary_ty X)
        (Conj
          (pp_pure pp_unary_ty Y)
          (pp_fun Prop r)))
      (Imp
        (Eq Prop (App X r) (App Y r))
        (Conj
          (mf_condition Prop X Y)
          (pp_pointwise_necessary_identity X Y)))"
proof -
  let ?I = "pp_pointwise_identity_operator_instance X Y"
  let ?A =
    "Conj
      (pp_pure pp_unary_ty X)
      (Conj
        (pp_pure pp_unary_ty Y)
        (pp_fun Prop r))"
  let ?E = "Eq Prop (App X r) (App Y r)"
  let ?M = "mf_condition Prop X Y"
  let ?N = "pp_pointwise_necessary_identity X Y"
  let ?U = "Forall Prop (App (shift ?I) (Var 0))"
  have core: "pp_T6_core_PP_axioms \<subseteq> T"
    using recombination_stock
    unfolding pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def
      pp_T6_core_PP_axioms_def
    by blast
  have recombination: "pp_unary_recombination \<in> T"
    using recombination_stock pp_unary_recombination_in_recombination
    by blast
  have I_type: "\<Gamma> \<turnstile> ?I : pp_unary_ty"
    using X_type Y_type
    by (rule typed_pp_pointwise_identity_operator_instance)
  have app_X_type: "\<Gamma> \<turnstile> App X r : Prop"
    using X_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have app_Y_type: "\<Gamma> \<turnstile> App Y r : Prop"
    using Y_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using app_X_type app_Y_type by (rule has_type.Eq)
  have M_type: "\<Gamma> \<turnstile> ?M : Prop"
    using X_type Y_type unfolding pp_unary_ty_def
    by (rule typed_mf_condition)
  have N_type: "\<Gamma> \<turnstile> ?N : Prop"
    using X_type Y_type by
      (rule typed_pp_pointwise_necessary_identity)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using typed_pp_pure[OF X_type] typed_pp_pure[OF Y_type]
      typed_pp_fun[OF r_type]
    by (intro has_type.Conj)
  have d_A:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
  proof (rule CEV_axiom_from.Assumption)
    show "?A \<in> insert ?E {?A}" by simp
    show "\<Gamma> \<turnstile> ?A : Prop" by (rule A_type)
  qed
  have pure_X:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty X"
    using d_A by (rule CEV_axiom_from_conj_left)
  have tail:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_pure pp_unary_ty Y) (pp_fun Prop r)"
    using d_A by (rule CEV_axiom_from_conj_right)
  have pure_Y:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty Y"
    using tail by (rule CEV_axiom_from_conj_left)
  have fun_r:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun Prop r"
    using tail by (rule CEV_axiom_from_conj_right)
  have pure_I:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?I"
    using core X_type Y_type pure_X pure_Y
    by (rule CEV_axiom_from_pure_pointwise_identity_operator_instance)
  have d_E:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
  proof (rule CEV_axiom_from.Assumption)
    show "?E \<in> insert ?E {?A}" by simp
    show "\<Gamma> \<turnstile> ?E : Prop" by (rule E_type)
  qed
  have box_E:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o ?E"
    using app_X_type app_Y_type d_E by (rule CEV_axiom_from_box_of_eq)
  have Ir_type: "\<Gamma> \<turnstile> App ?I r : Prop"
    using I_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have E_imp_Ir_base: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?E (App ?I r)"
    using Ir_type E_type
      CEV_pp_pointwise_identity_operator_instance_apply[
        OF X_type Y_type r_type]
    by (rule CEV_beta_right_imp)
  have E_imp_Ir:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?E (App ?I r)"
    using E_imp_Ir_base by (rule CEV_axiom_proves.Base)
  have box_imp:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (Imp ?E (App ?I r))"
    using CEV_axiom_necessitation[OF E_imp_Ir]
    by (rule CEV_axiom_from.Theorem)
  have box_Ir:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (App ?I r)"
    using E_type Ir_type box_imp box_E
    by (rule CEV_axiom_from_box_MP)
  have pair:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_pure pp_unary_ty ?I) (pp_fun Prop r)"
    using pure_I fun_r by (rule CEV_axiom_from_conj_intro)
  have rec_rule:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj (pp_pure pp_unary_ty ?I) (pp_fun Prop r))
        (Imp (\<box>\<^sub>o (App ?I r)) ?U)"
    using CEV_axiom_unary_recombination_instance[
        OF recombination I_type r_type]
    by (rule CEV_axiom_from.Theorem)
  have rec_tail:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (\<box>\<^sub>o (App ?I r)) ?U"
    using pair rec_rule by (rule CEV_axiom_from.MP)
  have d_U:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?U"
    using box_Ir rec_tail by (rule CEV_axiom_from.MP)
  have U_type: "\<Gamma> \<turnstile> ?U : Prop"
    using CEV_axiom_from_formula[OF d_U] .
  have U_imp_M_base: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?U ?M"
    using U_type M_type
      CEV_pp_pointwise_identity_operator_instance_forall[
        OF X_type Y_type]
    by (rule CEV_beta_left_imp)
  have d_M:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?M"
    using d_U
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[OF U_imp_M_base]]
    by (rule CEV_axiom_from.MP)
  have d_N:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?N"
    using d_M
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[
          OF CEV_mf_condition_implies_pointwise_necessary_identity[
            OF X_type Y_type]]]
    by (rule CEV_axiom_from.MP)
  have result:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj ?M ?N"
    using d_M d_N by (rule CEV_axiom_from_conj_intro)
  have under_A:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?E (Conj ?M ?N)"
    using E_type result by (rule CEV_axiom_from_deduction)
  show ?thesis
    using A_type under_A by (rule CEV_axiom_from_singleton_imp)
qed

subsection \<open>Zeroary Exhaustion repairs the QSS bridge\<close>

definition pp_recombination_zeroary_exhaustion_axioms :: "oterm set" where
  "pp_recombination_zeroary_exhaustion_axioms =
    insert pp_zeroary_exhaustion pp_recombination_PP_axioms"

lemma pp_recombination_zeroary_exhaustion_axioms_typed:
  assumes "A \<in> pp_recombination_zeroary_exhaustion_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_recombination_PP_axioms_typed
    typed_pp_zeroary_exhaustion
  unfolding pp_recombination_zeroary_exhaustion_axioms_def
  by blast

theorem CEV_QSS_from_recombination_with_zeroary_exhaustion_parameter:
  assumes repaired:
      "pp_recombination_zeroary_exhaustion_axioms \<subseteq> T"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_QSS_instance X Y r"
proof -
  let ?A =
    "Conj
      (pp_pure pp_unary_ty X)
      (Conj
        (pp_pure pp_unary_ty Y)
        (pp_fun Prop r))"
  let ?E = "Eq Prop (App X r) (App Y r)"
  let ?M = "mf_condition Prop X Y"
  let ?XY = "Eq pp_unary_ty X Y"
  have rec_stock: "pp_recombination_PP_axioms \<subseteq> T"
    using repaired
    unfolding pp_recombination_zeroary_exhaustion_axioms_def
    by blast
  have exhaustion: "pp_zeroary_exhaustion \<in> T"
    using repaired
    unfolding pp_recombination_zeroary_exhaustion_axioms_def
    by blast
  have core: "pp_T6_core_PP_axioms \<subseteq> T"
    using rec_stock
    unfolding pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def
      pp_T6_core_PP_axioms_def
    by blast
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using typed_pp_pure[OF X_type] typed_pp_pure[OF Y_type]
      typed_pp_fun[OF r_type]
    by (intro has_type.Conj)
  have app_X_type: "\<Gamma> \<turnstile> App X r : Prop"
    using X_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have app_Y_type: "\<Gamma> \<turnstile> App Y r : Prop"
    using Y_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using app_X_type app_Y_type by (rule has_type.Eq)
  have M_type: "\<Gamma> \<turnstile> ?M : Prop"
    using X_type Y_type unfolding pp_unary_ty_def
    by (rule typed_mf_condition)
  have d_A:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
  proof (rule CEV_axiom_from.Assumption)
    show "?A \<in> insert ?E {?A}" by simp
    show "\<Gamma> \<turnstile> ?A : Prop" by (rule A_type)
  qed
  have pure_X:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty X"
    using d_A by (rule CEV_axiom_from_conj_left)
  have tail:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_pure pp_unary_ty Y) (pp_fun Prop r)"
    using d_A by (rule CEV_axiom_from_conj_right)
  have pure_Y:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty Y"
    using tail by (rule CEV_axiom_from_conj_left)
  have d_E:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
  proof (rule CEV_axiom_from.Assumption)
    show "?E \<in> insert ?E {?A}" by simp
    show "\<Gamma> \<turnstile> ?E : Prop" by (rule E_type)
  qed
  have modal_core_rule:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?A (Imp ?E
        (Conj ?M (pp_pointwise_necessary_identity X Y)))"
    using CEV_QSS_modal_core_from_recombination[
        OF rec_stock X_type Y_type r_type]
    by (rule CEV_axiom_from.Theorem)
  have modal_tail:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?E (Conj ?M (pp_pointwise_necessary_identity X Y))"
    using d_A modal_core_rule by (rule CEV_axiom_from.MP)
  have modal_pair:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj ?M (pp_pointwise_necessary_identity X Y)"
    using d_E modal_tail by (rule CEV_axiom_from.MP)
  have d_M:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?M"
    using modal_pair by (rule CEV_axiom_from_conj_left)
  have pure_M:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ?M"
    using core X_type Y_type pure_X pure_Y
    by (rule CEV_axiom_from_pure_mf_condition)
  have exhaustion_rule:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_pure Prop ?M) (Imp ?M (\<box>\<^sub>o ?M))"
    using pp_axiom_zeroary_exhaustion_imp[OF exhaustion M_type]
    by (rule CEV_axiom_from.Theorem)
  have exhaustion_tail:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?M (\<box>\<^sub>o ?M)"
    using pure_M exhaustion_rule by (rule CEV_axiom_from.MP)
  have box_M:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o ?M"
    using d_M exhaustion_tail by (rule CEV_axiom_from.MP)
  have mf_rule:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (\<box>\<^sub>o ?M) ?XY"
  proof -
    have raw:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (\<box>\<^sub>o ?M)
          (Eq (Prop \<rightarrow>\<^sub>o Prop) X Y)"
      using X_type[unfolded pp_unary_ty_def]
        Y_type[unfolded pp_unary_ty_def]
      by (rule CEV_unary_modalized_functionality)
    have raw_alias:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp (\<box>\<^sub>o ?M) ?XY"
      using raw by (simp add: pp_unary_ty_def)
    have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (\<box>\<^sub>o ?M) ?XY"
      using raw_alias by (rule CEV_axiom_proves.Base)
    then show ?thesis by (rule CEV_axiom_from.Theorem)
  qed
  have d_XY:
    "\<Gamma> ; T ; insert ?E {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?XY"
    using box_M mf_rule by (rule CEV_axiom_from.MP)
  have under_A:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?E ?XY"
    using E_type d_XY by (rule CEV_axiom_from_deduction)
  have result:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?A (Imp ?E ?XY)"
    using A_type under_A by (rule CEV_axiom_from_singleton_imp)
  show ?thesis
    using result unfolding pp_QSS_instance_def .
qed

lemma CEV_axiom_generalize_theorem:
  assumes A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and dA: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall \<sigma> A"
proof -
  have d_imp:
    "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ObjTrue) A"
  proof -
    have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ObjTrue A"
      using typed_ObjTrue dA by (rule CEV_axiom_imp_of_right)
    then show ?thesis by (simp add: ObjTrue_def shift_def)
  qed
  have d_gen:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue (Forall \<sigma> A)"
    using typed_ObjTrue A_type d_imp by (rule CEV_axiom_proves.Gen)
  show ?thesis
    using CEV_axiom_proves_ObjTrue d_gen by (rule CEV_axiom_proves.MP)
qed

theorem CEV_QSS_from_recombination_with_zeroary_exhaustion:
  "\<Gamma> ; pp_recombination_zeroary_exhaustion_axioms
    \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS"
proof -
  let ?op = pp_unary_ty
  let ?X = "Var 2 :: oterm"
  let ?Y = "Var 1 :: oterm"
  let ?r = "Var 0 :: oterm"
  let ?body = "pp_QSS_instance ?X ?Y ?r"
  have X_type: "Prop # ?op # ?op # \<Gamma> \<turnstile> ?X : ?op"
    by (rule has_type.Var) (simp add: lookup_def)
  have Y_type: "Prop # ?op # ?op # \<Gamma> \<turnstile> ?Y : ?op"
    by (rule has_type.Var) (simp add: lookup_def)
  have r_type: "Prop # ?op # ?op # \<Gamma> \<turnstile> ?r : Prop"
    by (rule has_type.Var) (simp add: lookup_def)
  have body_type: "Prop # ?op # ?op # \<Gamma> \<turnstile> ?body : Prop"
    using X_type Y_type r_type by (rule typed_pp_QSS_instance)
  have d_body:
    "Prop # ?op # ?op # \<Gamma> ;
      pp_recombination_zeroary_exhaustion_axioms
      \<turnstile>\<^sub>CEV\<^sup>+ ?body"
    using subset_refl X_type Y_type r_type
    by (rule CEV_QSS_from_recombination_with_zeroary_exhaustion_parameter)
  have d_r:
    "?op # ?op # \<Gamma> ; pp_recombination_zeroary_exhaustion_axioms
      \<turnstile>\<^sub>CEV\<^sup>+ Forall Prop ?body"
    using body_type d_body by (rule CEV_axiom_generalize_theorem)
  have r_forall_type:
    "?op # ?op # \<Gamma> \<turnstile> Forall Prop ?body : Prop"
    using body_type by (rule has_type.Forall)
  have d_Y:
    "?op # \<Gamma> ; pp_recombination_zeroary_exhaustion_axioms
      \<turnstile>\<^sub>CEV\<^sup>+ Forall ?op (Forall Prop ?body)"
    using r_forall_type d_r by (rule CEV_axiom_generalize_theorem)
  have Y_forall_type:
    "?op # \<Gamma> \<turnstile> Forall ?op (Forall Prop ?body) : Prop"
    using r_forall_type by (rule has_type.Forall)
  have d_X:
    "\<Gamma> ; pp_recombination_zeroary_exhaustion_axioms
      \<turnstile>\<^sub>CEV\<^sup>+
        Forall ?op (Forall ?op (Forall Prop ?body))"
    using Y_forall_type d_Y by (rule CEV_axiom_generalize_theorem)
  show ?thesis
    using d_X
    by (simp add: pp_QSS_def pp_QSS_instance_def)
qed

subsection \<open>QSS and unique fundamentality yield \<open>\<exists>fun\<acute>\<close>\<close>

lemma CEV_axiom_QSS_instance_of_contextual_proof:
  assumes qss: "\<And>\<Delta>. \<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS_instance X Y r"
proof -
  have inserted:
    "\<Gamma> ; insert pp_QSS T \<turnstile>\<^sub>CEV\<^sup>+
      pp_QSS_instance X Y r"
    using X_type Y_type r_type
    by (intro pp_axiom_QSS_instance) simp
  show ?thesis
  proof (rule CEV_axiom_proves_translate[OF inserted])
    fix \<Delta> B
    assume B_in: "B \<in> insert pp_QSS T"
      and B_type: "\<Delta> \<turnstile> B : Prop"
    show "\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
    proof (cases "B = pp_QSS")
      case True
      show ?thesis using qss[of \<Delta>] True by simp
    next
      case False
      have "B \<in> T" using B_in False by simp
      then show ?thesis
        using B_type by (rule CEV_axiom_proves.Axiom)
    qed
  qed
qed

lemma CEV_fun_prime_from_contextual_QSS:
  assumes qss: "\<And>\<Delta>. \<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun Prop p) (pp_fun_prime p)"
proof -
  let ?op = pp_unary_ty
  let ?X = "Var 1 :: oterm"
  let ?Y = "Var 0 :: oterm"
  let ?p2 = "shift_by 2 p"
  let ?PX = "pp_pure ?op ?X"
  let ?PY = "pp_pure ?op ?Y"
  let ?F = "pp_fun Prop ?p2"
  let ?E = "Eq Prop (App ?X ?p2) (App ?Y ?p2)"
  let ?XY = "Eq ?op ?X ?Y"
  let ?body = "Imp (Conj ?PX ?PY) (Imp ?E ?XY)"
  let ?QI = "pp_QSS_instance ?X ?Y ?p2"
  have p2_type: "?op # ?op # \<Gamma> \<turnstile> ?p2 : Prop"
  proof -
    have "[?op, ?op] @ \<Gamma> \<turnstile>
        shift_by (length [?op, ?op]) p : Prop"
      using p_type by (rule shift_by_preserves_typing)
    then show ?thesis by (simp add: numeral_2_eq_2)
  qed
  have X_type: "?op # ?op # \<Gamma> \<turnstile> ?X : ?op"
    by (rule has_type.Var) (simp add: lookup_def)
  have Y_type: "?op # ?op # \<Gamma> \<turnstile> ?Y : ?op"
    by (rule typed_var0)
  have PX_type: "?op # ?op # \<Gamma> \<turnstile> ?PX : Prop"
    using X_type by (rule typed_pp_pure)
  have PY_type: "?op # ?op # \<Gamma> \<turnstile> ?PY : Prop"
    using Y_type by (rule typed_pp_pure)
  have F_type: "?op # ?op # \<Gamma> \<turnstile> ?F : Prop"
    using p2_type by (rule typed_pp_fun)
  have Xp_type: "?op # ?op # \<Gamma> \<turnstile> App ?X ?p2 : Prop"
    using X_type p2_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Yp_type: "?op # ?op # \<Gamma> \<turnstile> App ?Y ?p2 : Prop"
    using Y_type p2_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have E_type: "?op # ?op # \<Gamma> \<turnstile> ?E : Prop"
    using Xp_type Yp_type by (rule has_type.Eq)
  have XY_type: "?op # ?op # \<Gamma> \<turnstile> ?XY : Prop"
    using X_type Y_type by (rule has_type.Eq)
  have body_type: "?op # ?op # \<Gamma> \<turnstile> ?body : Prop"
    using PX_type PY_type E_type XY_type
    by (intro has_type.Imp has_type.Conj)
  have QI_type: "?op # ?op # \<Gamma> \<turnstile> ?QI : Prop"
    using X_type Y_type p2_type by (rule typed_pp_QSS_instance)
  have d_QI:
    "?op # ?op # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ?QI"
    using qss X_type Y_type p2_type
    by (rule CEV_axiom_QSS_instance_of_contextual_proof)
  have rearrange:
    "?op # ?op # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?QI (Imp ?F ?body)"
  proof (rule CEV_prop_tautology)
    show "prop_tautology (?op # ?op # \<Gamma>)
      (Imp ?QI (Imp ?F ?body))"
      unfolding prop_tautology_def pp_QSS_instance_def
      using PX_type PY_type F_type E_type XY_type QI_type body_type
      by auto
  qed
  have d_rearrange:
    "?op # ?op # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?QI (Imp ?F ?body)"
    using rearrange by (rule CEV_axiom_proves.Base)
  have d_inner:
    "?op # ?op # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F ?body"
    using d_QI d_rearrange by (rule CEV_axiom_proves.MP)
  let ?P1 = "pp_fun Prop (shift p)"
  have P1_type: "?op # \<Gamma> \<turnstile> ?P1 : Prop"
    using typed_shift_ctx[OF p_type] by (rule typed_pp_fun)
  have shifted_P1: "shift ?P1 = ?F"
    using shift_shift_eq_shift_by_2[of p]
    by (simp add: pp_fun_def pp_Fun_def shift_def)
  have d_inner_alias:
    "?op # ?op # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?P1) ?body"
    using d_inner shifted_P1 by simp
  have d_Y:
    "?op # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P1 (Forall ?op ?body)"
    using P1_type body_type d_inner_alias
    by (rule CEV_axiom_proves.Gen)
  have forall_Y_type:
    "?op # \<Gamma> \<turnstile> Forall ?op ?body : Prop"
    using body_type by (rule has_type.Forall)
  have P0_type: "\<Gamma> \<turnstile> pp_fun Prop p : Prop"
    using p_type by (rule typed_pp_fun)
  have shifted_P0: "shift (pp_fun Prop p) = ?P1"
    by (simp add: pp_fun_def pp_Fun_def shift_def)
  have d_Y_alias:
    "?op # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (pp_fun Prop p)) (Forall ?op ?body)"
    using d_Y shifted_P0 by simp
  have d_X:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_fun Prop p) (Forall ?op (Forall ?op ?body))"
    using P0_type forall_Y_type d_Y_alias
    by (rule CEV_axiom_proves.Gen)
  show ?thesis
    using d_X
    by (simp add: pp_fun_prime_def)
qed

theorem CEV_exists_fun_prime_from_QSS_and_unique_fundamentality:
  assumes qss: "\<And>\<Delta>. \<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS"
    and unique: "pp_unique_fundamental Prop \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_exists_fun_prime"
proof -
  let ?H =
    "Conj
      (pp_fun Prop (Var 0))
      (Forall Prop
        (Imp
          (pp_fun Prop (Var 0))
          (Eq Prop (Var 0) (Var 1))))"
  have H_type: "Prop # \<Gamma> \<turnstile> ?H : Prop"
    by (rule infer_type_sound)
      (simp add: pp_fun_def pp_Fun_def lookup_def)
  have p_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have d_H:
    "Prop # \<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
  proof (rule CEV_axiom_from.Assumption)
    show "?H \<in> {?H}" by simp
    show "Prop # \<Gamma> \<turnstile> ?H : Prop" by (rule H_type)
  qed
  have d_fun:
    "Prop # \<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_fun Prop (Var 0)"
    using d_H by (rule CEV_axiom_from_conj_left)
  have fun_prime_rule:
    "Prop # \<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_fun Prop (Var 0)) (pp_fun_prime (Var 0))"
    using CEV_fun_prime_from_contextual_QSS[
        OF qss p_type]
    by (rule CEV_axiom_from.Theorem)
  have d_fun_prime:
    "Prop # \<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_fun_prime (Var 0)"
    using d_fun fun_prime_rule by (rule CEV_axiom_from.MP)
  have exists_type:
    "Prop # \<Gamma> \<turnstile> Exists Prop (pp_fun_prime (Var 0)) : Prop"
  proof (rule has_type.Exists)
    show "Prop # Prop # \<Gamma> \<turnstile>
        pp_fun_prime (Var 0) : Prop"
      by (rule typed_pp_fun_prime, rule typed_var0)
  qed
  have d_instance:
    "Prop # \<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 (Var 0) (pp_fun_prime (Var 0))"
    using d_fun_prime
    by (simp add: pp_fun_prime_def subst0_def shift_by_def
        shift_ren_def)
  have d_exists:
    "Prop # \<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_exists_fun_prime"
    unfolding pp_exists_fun_prime_def
    using exists_type p_type d_instance
    by (rule CEV_axiom_from_EG_typed_RS)
  have witness_imp_unshifted:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?H pp_exists_fun_prime"
    using H_type d_exists by (rule CEV_axiom_from_singleton_imp)
  have witness_imp:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?H (shift pp_exists_fun_prime)"
    using witness_imp_unshifted
    by (simp add: pp_exists_fun_prime_def pp_fun_prime_def
        shift_by_def shift_ren_def shift_def)
  have eliminate_unique:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_unique_fundamental Prop) pp_exists_fun_prime"
  proof (unfold pp_unique_fundamental_def,
      rule CEV_axiom_proves.Inst)
    show "Prop # \<Gamma> \<turnstile> ?H : Prop" by (rule H_type)
    show "\<Gamma> \<turnstile> pp_exists_fun_prime : Prop"
      unfolding pp_exists_fun_prime_def
      by (rule has_type.Exists, rule typed_pp_fun_prime, rule typed_var0)
    show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?H (shift pp_exists_fun_prime)"
      by (rule witness_imp)
  qed
  have unique_type: "\<Gamma> \<turnstile> pp_unique_fundamental Prop : Prop"
    by (rule infer_type_sound)
      (simp add: pp_unique_fundamental_def pp_fun_def pp_Fun_def
        lookup_def)
  have d_unique:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_unique_fundamental Prop"
    using unique unique_type by (rule CEV_axiom_proves.Axiom)
  show ?thesis
    using d_unique eliminate_unique by (rule CEV_axiom_proves.MP)
qed

corollary
  CEV_exists_fun_prime_from_recombination_with_zeroary_exhaustion:
  "\<Gamma> ; pp_recombination_zeroary_exhaustion_axioms
    \<turnstile>\<^sub>CEV\<^sup>+ pp_exists_fun_prime"
proof (rule CEV_exists_fun_prime_from_QSS_and_unique_fundamentality)
  show "\<And>\<Delta>. \<Delta> ; pp_recombination_zeroary_exhaustion_axioms
      \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS"
    by (rule CEV_QSS_from_recombination_with_zeroary_exhaustion)
  show "pp_unique_fundamental Prop
      \<in> pp_recombination_zeroary_exhaustion_axioms"
    unfolding pp_recombination_zeroary_exhaustion_axioms_def
    using pp_unique_fundamental_is_assumed_recombination
    by blast
qed

subsection \<open>T6 over the repaired central stock\<close>

definition pp_repaired_T6_Inv_axioms :: "oterm set" where
  "pp_repaired_T6_Inv_axioms =
    pp_recombination_zeroary_exhaustion_axioms \<union> {pp_L2, pp_Inv}"

definition pp_repaired_T6_TU_axioms :: "oterm set" where
  "pp_repaired_T6_TU_axioms =
    insert pp_TU
      (insert pp_L2 pp_recombination_zeroary_exhaustion_axioms)"

definition pp_repaired_T6_WI_axioms :: "oterm set" where
  "pp_repaired_T6_WI_axioms =
    insert pp_WI
      (insert pp_L2 pp_recombination_zeroary_exhaustion_axioms)"

definition pp_repaired_T6_RS_axioms :: "oterm set" where
  "pp_repaired_T6_RS_axioms =
    insert pp_RS
      (insert pp_strong_L2
        pp_recombination_zeroary_exhaustion_axioms)"

lemma pp_repaired_T6_Inv_axioms_typed:
  assumes "A \<in> pp_repaired_T6_Inv_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_recombination_zeroary_exhaustion_axioms_typed
    typed_pp_L2 typed_pp_Inv
  unfolding pp_repaired_T6_Inv_axioms_def by blast

lemma pp_repaired_T6_TU_axioms_typed:
  assumes "A \<in> pp_repaired_T6_TU_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_recombination_zeroary_exhaustion_axioms_typed
    typed_pp_L2 typed_pp_TU
  unfolding pp_repaired_T6_TU_axioms_def by blast

lemma pp_repaired_T6_WI_axioms_typed:
  assumes "A \<in> pp_repaired_T6_WI_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_recombination_zeroary_exhaustion_axioms_typed
    typed_pp_L2 typed_pp_WI
  unfolding pp_repaired_T6_WI_axioms_def by blast

lemma pp_repaired_T6_RS_axioms_typed:
  assumes "A \<in> pp_repaired_T6_RS_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_recombination_zeroary_exhaustion_axioms_typed
    typed_pp_strong_L2 typed_pp_RS
  unfolding pp_repaired_T6_RS_axioms_def by blast

lemma CEV_axiom_proves_replace_exists_fun_prime:
  assumes d: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ A"
    and bridge: "\<And>\<Delta>. \<Delta> ; V \<turnstile>\<^sub>CEV\<^sup>+ pp_exists_fun_prime"
    and carry: "U - {pp_exists_fun_prime} \<subseteq> V"
  shows "\<Gamma> ; V \<turnstile>\<^sub>CEV\<^sup>+ A"
proof (rule CEV_axiom_proves_translate[OF d])
  fix \<Delta> B
  assume B_in: "B \<in> U"
    and B_type: "\<Delta> \<turnstile> B : Prop"
  show "\<Delta> ; V \<turnstile>\<^sub>CEV\<^sup>+ B"
  proof (cases "B = pp_exists_fun_prime")
    case True
    show ?thesis using bridge[of \<Delta>] True by simp
  next
    case False
    have "B \<in> V" using B_in False carry by blast
    then show ?thesis
      using B_type by (rule CEV_axiom_proves.Axiom)
  qed
qed

theorem CEV_Goodman_T6_Inv_repaired_central_stock:
  "[] ; pp_repaired_T6_Inv_axioms
    \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof (rule CEV_axiom_proves_replace_exists_fun_prime[
    OF CEV_Goodman_T6_Inv])
  show "\<And>\<Delta>. \<Delta> ; pp_repaired_T6_Inv_axioms
      \<turnstile>\<^sub>CEV\<^sup>+ pp_exists_fun_prime"
    using CEV_exists_fun_prime_from_recombination_with_zeroary_exhaustion
    unfolding pp_repaired_T6_Inv_axioms_def
    by (meson CEV_axiom_proves_mono Un_upper1)
  show "pp_T6_Inv_axioms - {pp_exists_fun_prime}
      \<subseteq> pp_repaired_T6_Inv_axioms"
    unfolding pp_T6_Inv_axioms_def pp_T6_core_PP_axioms_def
      pp_repaired_T6_Inv_axioms_def
      pp_recombination_zeroary_exhaustion_axioms_def
      pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def
    by blast
qed

theorem CEV_Goodman_T6_TU_repaired_central_stock:
  "[] ; pp_repaired_T6_TU_axioms
    \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof (rule CEV_axiom_proves_replace_exists_fun_prime[
    OF CEV_Goodman_T6_TU])
  show "\<And>\<Delta>. \<Delta> ; pp_repaired_T6_TU_axioms
      \<turnstile>\<^sub>CEV\<^sup>+ pp_exists_fun_prime"
    using CEV_exists_fun_prime_from_recombination_with_zeroary_exhaustion
    unfolding pp_repaired_T6_TU_axioms_def
    by (meson CEV_axiom_proves_mono subset_insertI)
  show "pp_T6_TU_axioms - {pp_exists_fun_prime}
      \<subseteq> pp_repaired_T6_TU_axioms"
    unfolding pp_T6_TU_axioms_def pp_T6_core_PP_axioms_def
      pp_repaired_T6_TU_axioms_def
      pp_recombination_zeroary_exhaustion_axioms_def
      pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def
    by blast
qed

theorem CEV_Goodman_T6_WI_repaired_central_stock:
  "[] ; pp_repaired_T6_WI_axioms
    \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof (rule CEV_axiom_proves_replace_exists_fun_prime[
    OF CEV_Goodman_T6_WI])
  show "\<And>\<Delta>. \<Delta> ; pp_repaired_T6_WI_axioms
      \<turnstile>\<^sub>CEV\<^sup>+ pp_exists_fun_prime"
    using CEV_exists_fun_prime_from_recombination_with_zeroary_exhaustion
    unfolding pp_repaired_T6_WI_axioms_def
    by (meson CEV_axiom_proves_mono subset_insertI)
  show "pp_T6_WI_axioms - {pp_exists_fun_prime}
      \<subseteq> pp_repaired_T6_WI_axioms"
    unfolding pp_T6_WI_axioms_def pp_T6_core_PP_axioms_def
      pp_repaired_T6_WI_axioms_def
      pp_recombination_zeroary_exhaustion_axioms_def
      pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def
    by blast
qed

theorem CEV_Goodman_T6_RS_repaired_central_stock:
  "[] ; pp_repaired_T6_RS_axioms
    \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof -
  have subset:
    "pp_T6_RS_axioms \<subseteq> pp_repaired_T6_RS_axioms"
    unfolding pp_T6_RS_axioms_def pp_T6_core_PP_axioms_def
      pp_repaired_T6_RS_axioms_def
      pp_recombination_zeroary_exhaustion_axioms_def
      pp_recombination_PP_axioms_def
      pp_recombination_background_axioms_def pp_background_axioms_def
    by blast
  show ?thesis
    using CEV_Goodman_T6_RS subset by (rule CEV_axiom_proves_mono)
qed

end
