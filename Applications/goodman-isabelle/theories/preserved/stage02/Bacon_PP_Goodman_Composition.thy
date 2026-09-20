theory Bacon_PP_Goodman_Composition
  imports 
    "Goodman_Legacy_01.Bacon_PP_T6_Encoding"
begin

section \<open>Composition laws used in Goodman's object-language arguments\<close>

text \<open>
  Goodman's arguments repeatedly treat the pure proposition operators as a
  monoid under composition.  This theory verifies the required algebra in the
  object logic.  The proofs use only conversion and unary equivalence; no PP
  axiom is needed for the algebraic equalities.
\<close>

lemma rename_lift_Suc_after_shift:
  "rename (lift_ren Suc) (rename Suc M) =
    rename Suc (rename Suc M)"
proof (simp only: rename_comp)
  show "rename (lift_ren Suc \<circ> Suc) M =
      rename (Suc \<circ> Suc) M"
    by (rule rename_cong) simp
qed

lemma shift_pp_compose[simp]:
  "shift (pp_compose F G) = pp_compose (shift F) (shift G)"
  by (simp add: shift_def pp_compose_def rename_lift_Suc_after_shift)

lemma shift_pp_identity_operator[simp]:
  "shift pp_identity_operator = pp_identity_operator"
  by (simp add: shift_def pp_identity_operator_def)

lemma pp_compose_apply_beta:
  "compatible_step beta_contract
    (App (pp_compose F G) P)
    (App F (App G P))"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam Prop
          (App (shift F) (App (shift G) (Var 0))))
        P)
      (subst0 P
        (App (shift F) (App (shift G) (Var 0))))"
    by (rule beta_contract.beta)
  show "beta_contract
      (App (pp_compose F G) P)
      (App F (App G P))"
    using step
    by (simp add: pp_compose_def subst0_def)
qed

lemma CEV_pp_compose_apply:
  assumes F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and G_type: "\<Gamma> \<turnstile> G : pp_unary_ty"
    and P_type: "\<Gamma> \<turnstile> P : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    (App (pp_compose F G) P \<longleftrightarrow>\<^sub>o
      App F (App G P))"
proof -
  have left_type: "\<Gamma> \<turnstile> App (pp_compose F G) P : Prop"
    using typed_pp_compose[OF F_type G_type] P_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have GP_type: "\<Gamma> \<turnstile> App G P : Prop"
    using G_type P_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have right_type: "\<Gamma> \<turnstile> App F (App G P) : Prop"
    using F_type GP_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    using left_type right_type pp_compose_apply_beta
    by (rule CEV_beta_step)
qed

lemma pp_identity_apply_beta:
  "compatible_step beta_contract
    (App pp_identity_operator P)
    P"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App (Lam Prop (Var 0)) P)
      (subst0 P (Var 0))"
    by (rule beta_contract.beta)
  show "beta_contract (App pp_identity_operator P) P"
    using step
    by (simp add: pp_identity_operator_def subst0_def)
qed

lemma CEV_pp_identity_apply:
  assumes P_type: "\<Gamma> \<turnstile> P : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    (App pp_identity_operator P \<longleftrightarrow>\<^sub>o P)"
proof -
  have left_type: "\<Gamma> \<turnstile> App pp_identity_operator P : Prop"
    using typed_pp_identity_operator P_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  show ?thesis
    using left_type P_type pp_identity_apply_beta
    by (rule CEV_beta_step)
qed

lemma CEV_eq_app_right:
  assumes F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and B_type: "\<Gamma> \<turnstile> B : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp
      (Eq \<sigma> A B)
      (Eq \<tau> (App F A) (App F B))"
proof -
  let ?FA = "App F A"
  let ?FB = "App F B"
  let ?EAA = "Eq \<tau> ?FA ?FA"
  let ?EAB = "Eq \<tau> ?FA ?FB"
  let ?P =
    "Lam \<sigma>
      (Eq \<tau> (shift ?FA) (App (shift F) (Var 0)))"
  have FA_type: "\<Gamma> \<turnstile> ?FA : \<tau>"
    using F_type A_type by (rule has_type.App)
  have FB_type: "\<Gamma> \<turnstile> ?FB : \<tau>"
    using F_type B_type by (rule has_type.App)
  have P_type: "\<Gamma> \<turnstile> ?P : \<sigma> \<rightarrow>\<^sub>o Prop"
  proof (rule has_type.Lam)
    have shift_FA: "\<sigma> # \<Gamma> \<turnstile> shift ?FA : \<tau>"
      using FA_type by (rule typed_shift_ctx)
    have shift_F:
      "\<sigma> # \<Gamma> \<turnstile> shift F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
      using F_type by (rule typed_shift_ctx)
    have v: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
      by (rule typed_var0)
    have app: "\<sigma> # \<Gamma> \<turnstile> App (shift F) (Var 0) : \<tau>"
      using shift_F v by (rule has_type.App)
    show "\<sigma> # \<Gamma> \<turnstile>
      Eq \<tau> (shift ?FA) (App (shift F) (Var 0)) : Prop"
      using shift_FA app by (rule has_type.Eq)
  qed
  have PA_type: "\<Gamma> \<turnstile> App ?P A : Prop"
    using P_type A_type by (rule has_type.App)
  have PB_type: "\<Gamma> \<turnstile> App ?P B : Prop"
    using P_type B_type by (rule has_type.App)
  have EAA_type: "\<Gamma> \<turnstile> ?EAA : Prop"
    using FA_type FA_type by (rule has_type.Eq)
  have EAB_type: "\<Gamma> \<turnstile> ?EAB : Prop"
    using FA_type FB_type by (rule has_type.Eq)
  have ref: "\<Gamma> \<turnstile>\<^sub>CEV ?EAA"
    using FA_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.Ref)
  have beta_A: "\<Gamma> \<turnstile>\<^sub>CEV (App ?P A \<longleftrightarrow>\<^sub>o ?EAA)"
  proof -
    have step: "compatible_step beta_contract (App ?P A) ?EAA"
    proof -
      have "compatible_step beta_contract
          (App ?P A)
          (subst0 A
            (Eq \<tau> (shift ?FA) (App (shift F) (Var 0))))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis by (simp add: subst0_def)
    qed
    show ?thesis
      using PA_type EAA_type step by (rule CEV_beta_step)
  qed
  have PA: "\<Gamma> \<turnstile>\<^sub>CEV App ?P A"
  proof -
    have d_back: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?EAA (App ?P A)"
      using PA_type EAA_type beta_A by (rule CEV_beta_right_imp)
    show ?thesis using ref d_back by (rule CEV_proves.MP)
  qed
  have ll: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Eq \<sigma> A B) (Imp (App ?P A) (App ?P B))"
    using A_type B_type P_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have beta_B: "\<Gamma> \<turnstile>\<^sub>CEV (App ?P B \<longleftrightarrow>\<^sub>o ?EAB)"
  proof -
    have step: "compatible_step beta_contract (App ?P B) ?EAB"
    proof -
      have "compatible_step beta_contract
          (App ?P B)
          (subst0 B
            (Eq \<tau> (shift ?FA) (App (shift F) (Var 0))))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis by (simp add: subst0_def)
    qed
    show ?thesis
      using PB_type EAB_type step by (rule CEV_beta_step)
  qed
  have PB_EAB: "\<Gamma> \<turnstile>\<^sub>CEV Imp (App ?P B) ?EAB"
    using PB_type EAB_type beta_B by (rule CEV_beta_left_imp)
  have local:
    "CEV_from \<Gamma> (Eq \<sigma> A B) ?EAB"
  proof -
    have eq_type: "\<Gamma> \<turnstile> Eq \<sigma> A B : Prop"
      using A_type B_type by (rule has_type.Eq)
    have d_eq:
      "CEV_from \<Gamma> (Eq \<sigma> A B) (Eq \<sigma> A B)"
      using eq_type by (rule CEV_from.Assumption)
    have d_ll:
      "CEV_from \<Gamma> (Eq \<sigma> A B)
        (Imp (Eq \<sigma> A B) (Imp (App ?P A) (App ?P B)))"
      using ll by (rule CEV_from.Theorem)
    have d_step:
      "CEV_from \<Gamma> (Eq \<sigma> A B)
        (Imp (App ?P A) (App ?P B))"
      using d_eq d_ll by (rule CEV_from.MP)
    have d_PA:
      "CEV_from \<Gamma> (Eq \<sigma> A B) (App ?P A)"
      using PA by (rule CEV_from.Theorem)
    have d_PB:
      "CEV_from \<Gamma> (Eq \<sigma> A B) (App ?P B)"
      using d_PA d_step by (rule CEV_from.MP)
    have d_last:
      "CEV_from \<Gamma> (Eq \<sigma> A B) (Imp (App ?P B) ?EAB)"
      using PB_EAB by (rule CEV_from.Theorem)
    show ?thesis
      using d_PB d_last by (rule CEV_from.MP)
  qed
  have eq_type: "\<Gamma> \<turnstile> Eq \<sigma> A B : Prop"
    using A_type B_type by (rule has_type.Eq)
  show ?thesis
    using local eq_type by (rule CEV_from_deduction)
qed

theorem CEV_pp_compose_left_identity:
  assumes F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (pp_compose pp_identity_operator F)
      F"
proof -
  have op_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Eq (Prop \<rightarrow>\<^sub>o Prop)
        (pp_compose pp_identity_operator F)
        F"
  proof (rule CEV_unary_equivalence)
    show "\<Gamma> \<turnstile>
        pp_compose pp_identity_operator F : Prop \<rightarrow>\<^sub>o Prop"
      using typed_pp_compose[OF typed_pp_identity_operator F_type]
      by (simp add: pp_unary_ty_def)
  next
    show "\<Gamma> \<turnstile> F : Prop \<rightarrow>\<^sub>o Prop"
      using F_type by (simp add: pp_unary_ty_def)
  next
    let ?P = "App (shift F) (Var 0)"
    have F_shift: "Prop # \<Gamma> \<turnstile> shift F : pp_unary_ty"
      using F_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    have P_type: "Prop # \<Gamma> \<turnstile> ?P : Prop"
      using F_shift v_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have first:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App
          (pp_compose pp_identity_operator (shift F))
          (Var 0)
        \<longleftrightarrow>\<^sub>o
          App pp_identity_operator ?P)"
      using typed_pp_identity_operator F_shift v_type
      by (rule CEV_pp_compose_apply)
    have second:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App pp_identity_operator ?P \<longleftrightarrow>\<^sub>o ?P)"
      using P_type by (rule CEV_pp_identity_apply)
    have left_type:
      "Prop # \<Gamma> \<turnstile>
        App
          (pp_compose pp_identity_operator (shift F))
          (Var 0) : Prop"
      using typed_pp_compose[OF typed_pp_identity_operator F_shift] v_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have middle_type:
      "Prop # \<Gamma> \<turnstile> App pp_identity_operator ?P : Prop"
      using typed_pp_identity_operator P_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have chained:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App
          (pp_compose pp_identity_operator (shift F))
          (Var 0)
        \<longleftrightarrow>\<^sub>o ?P)"
      using left_type middle_type P_type first second
      by (rule CEV_biconditional_trans)
    show "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (shift (pp_compose pp_identity_operator F)) (Var 0)
        \<longleftrightarrow>\<^sub>o App (shift F) (Var 0))"
      using chained
      by simp
  qed
  show ?thesis
    using op_eq by (simp add: pp_unary_ty_def)
qed

theorem CEV_pp_compose_right_identity:
  assumes F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (pp_compose F pp_identity_operator)
      F"
proof -
  have op_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Eq (Prop \<rightarrow>\<^sub>o Prop)
        (pp_compose F pp_identity_operator)
        F"
  proof (rule CEV_unary_equivalence)
    show "\<Gamma> \<turnstile>
        pp_compose F pp_identity_operator : Prop \<rightarrow>\<^sub>o Prop"
      using typed_pp_compose[OF F_type typed_pp_identity_operator]
      by (simp add: pp_unary_ty_def)
  next
    show "\<Gamma> \<turnstile> F : Prop \<rightarrow>\<^sub>o Prop"
      using F_type by (simp add: pp_unary_ty_def)
  next
    let ?I = "App pp_identity_operator (Var 0)"
    let ?A = "App (shift F) ?I"
    let ?B = "App (shift F) (Var 0)"
    have F_shift: "Prop # \<Gamma> \<turnstile> shift F : pp_unary_ty"
      using F_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    have I_type: "Prop # \<Gamma> \<turnstile> ?I : Prop"
      using typed_pp_identity_operator v_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have A_type: "Prop # \<Gamma> \<turnstile> ?A : Prop"
      using F_shift I_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have B_type: "Prop # \<Gamma> \<turnstile> ?B : Prop"
      using F_shift v_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have first:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App
          (pp_compose (shift F) pp_identity_operator)
          (Var 0)
        \<longleftrightarrow>\<^sub>o ?A)"
      using F_shift typed_pp_identity_operator v_type
      by (rule CEV_pp_compose_apply)
    have inner_step:
      "compatible_step beta_contract ?A ?B"
      by (intro compatible_step.App_right pp_identity_apply_beta)
    have second:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?A \<longleftrightarrow>\<^sub>o ?B)"
      using A_type B_type inner_step by (rule CEV_beta_step)
    have left_type:
      "Prop # \<Gamma> \<turnstile>
        App
          (pp_compose (shift F) pp_identity_operator)
          (Var 0) : Prop"
      using typed_pp_compose[OF F_shift typed_pp_identity_operator] v_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have chained:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App
          (pp_compose (shift F) pp_identity_operator)
          (Var 0)
        \<longleftrightarrow>\<^sub>o ?B)"
      using left_type A_type B_type first second
      by (rule CEV_biconditional_trans)
    show "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (shift (pp_compose F pp_identity_operator)) (Var 0)
        \<longleftrightarrow>\<^sub>o App (shift F) (Var 0))"
      using chained
      by simp
  qed
  show ?thesis
    using op_eq by (simp add: pp_unary_ty_def)
qed

theorem CEV_pp_compose_associative:
  assumes F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and G_type: "\<Gamma> \<turnstile> G : pp_unary_ty"
    and H_type: "\<Gamma> \<turnstile> H : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (pp_compose (pp_compose F G) H)
      (pp_compose F (pp_compose G H))"
proof -
  have op_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Eq (Prop \<rightarrow>\<^sub>o Prop)
        (pp_compose (pp_compose F G) H)
        (pp_compose F (pp_compose G H))"
  proof (rule CEV_unary_equivalence)
    show "\<Gamma> \<turnstile>
        pp_compose (pp_compose F G) H : Prop \<rightarrow>\<^sub>o Prop"
      using typed_pp_compose[OF typed_pp_compose[OF F_type G_type] H_type]
      by (simp add: pp_unary_ty_def)
  next
    show "\<Gamma> \<turnstile>
        pp_compose F (pp_compose G H) : Prop \<rightarrow>\<^sub>o Prop"
      using typed_pp_compose[OF F_type typed_pp_compose[OF G_type H_type]]
      by (simp add: pp_unary_ty_def)
  next
    let ?Fp = "shift F"
    let ?Gp = "shift G"
    let ?Hp = "shift H"
    let ?v = "Var 0"
    let ?Hv = "App ?Hp ?v"
    let ?GHv = "App ?Gp ?Hv"
    let ?N = "App ?Fp ?GHv"
    let ?A0 =
      "App (pp_compose (pp_compose ?Fp ?Gp) ?Hp) ?v"
    let ?A1 =
      "App (pp_compose ?Fp ?Gp) ?Hv"
    let ?B0 =
      "App (pp_compose ?Fp (pp_compose ?Gp ?Hp)) ?v"
    let ?B1 =
      "App ?Fp (App (pp_compose ?Gp ?Hp) ?v)"
    have Fp_type: "Prop # \<Gamma> \<turnstile> ?Fp : pp_unary_ty"
      using F_type by (rule typed_shift_ctx)
    have Gp_type: "Prop # \<Gamma> \<turnstile> ?Gp : pp_unary_ty"
      using G_type by (rule typed_shift_ctx)
    have Hp_type: "Prop # \<Gamma> \<turnstile> ?Hp : pp_unary_ty"
      using H_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> ?v : Prop"
      by (rule typed_var0)
    have Hv_type: "Prop # \<Gamma> \<turnstile> ?Hv : Prop"
      using Hp_type v_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have GHv_type: "Prop # \<Gamma> \<turnstile> ?GHv : Prop"
      using Gp_type Hv_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have N_type: "Prop # \<Gamma> \<turnstile> ?N : Prop"
      using Fp_type GHv_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have A0_type: "Prop # \<Gamma> \<turnstile> ?A0 : Prop"
      using typed_pp_compose[
          OF typed_pp_compose[OF Fp_type Gp_type] Hp_type]
        v_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have A1_type: "Prop # \<Gamma> \<turnstile> ?A1 : Prop"
      using typed_pp_compose[OF Fp_type Gp_type] Hv_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have B0_type: "Prop # \<Gamma> \<turnstile> ?B0 : Prop"
      using typed_pp_compose[
          OF Fp_type typed_pp_compose[OF Gp_type Hp_type]]
        v_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have inner_type:
      "Prop # \<Gamma> \<turnstile> App (pp_compose ?Gp ?Hp) ?v : Prop"
      using typed_pp_compose[OF Gp_type Hp_type] v_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have B1_type: "Prop # \<Gamma> \<turnstile> ?B1 : Prop"
      using Fp_type inner_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have A0_A1:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?A0 \<longleftrightarrow>\<^sub>o ?A1)"
      using typed_pp_compose[OF Fp_type Gp_type] Hp_type v_type
      by (rule CEV_pp_compose_apply)
    have A1_N:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?A1 \<longleftrightarrow>\<^sub>o ?N)"
      using Fp_type Gp_type Hv_type by (rule CEV_pp_compose_apply)
    have A0_N:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?A0 \<longleftrightarrow>\<^sub>o ?N)"
      using A0_type A1_type N_type A0_A1 A1_N
      by (rule CEV_biconditional_trans)
    have B0_B1:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?B0 \<longleftrightarrow>\<^sub>o ?B1)"
      using Fp_type typed_pp_compose[OF Gp_type Hp_type] v_type
      by (rule CEV_pp_compose_apply)
    have inner_step:
      "compatible_step beta_contract ?B1 ?N"
      by (intro compatible_step.App_right pp_compose_apply_beta)
    have B1_N:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?B1 \<longleftrightarrow>\<^sub>o ?N)"
      using B1_type N_type inner_step by (rule CEV_beta_step)
    have B0_N:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?B0 \<longleftrightarrow>\<^sub>o ?N)"
      using B0_type B1_type N_type B0_B1 B1_N
      by (rule CEV_biconditional_trans)
    have N_B0:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?N \<longleftrightarrow>\<^sub>o ?B0)"
      using B0_type N_type B0_N by (rule CEV_biconditional_sym)
    have A0_B0:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?A0 \<longleftrightarrow>\<^sub>o ?B0)"
      using A0_type N_type B0_type A0_N N_B0
      by (rule CEV_biconditional_trans)
    show "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (shift (pp_compose (pp_compose F G) H)) (Var 0)
        \<longleftrightarrow>\<^sub>o
       App (shift (pp_compose F (pp_compose G H))) (Var 0))"
      using A0_B0 by simp
  qed
  show ?thesis
    using op_eq by (simp add: pp_unary_ty_def)
qed

subsection \<open>Purity of composition from the exact PP core\<close>

definition pp_composition_builder :: oterm where
  "pp_composition_builder =
    Lam pp_unary_ty
      (Lam pp_unary_ty
        (pp_compose (Var 1) (Var 0)))"

definition pp_composition_instance :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_composition_instance F G =
    App (App pp_composition_builder F) G"

lemma typed_pp_composition_builder:
  "\<Gamma> \<turnstile> pp_composition_builder :
    pp_unary_ty \<rightarrow>\<^sub>o
      (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty)"
  by (rule infer_type_sound)
    (simp add: pp_composition_builder_def pp_compose_def
      pp_unary_ty_def lookup_def shift_def)

lemma pp_composition_builder_constant_free:
  "consts_of pp_composition_builder = {}"
  by (simp add: pp_composition_builder_def pp_compose_def shift_def)

lemma typed_pp_composition_instance:
  assumes F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and G_type: "\<Gamma> \<turnstile> G : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_composition_instance F G : pp_unary_ty"
  unfolding pp_composition_instance_def
  using typed_pp_composition_builder F_type G_type
  by (meson has_type.App pp_unary_ty_def)

lemma pp_composition_instance_first_beta:
  "compatible_step beta_contract
    (pp_composition_instance F G)
    (App
      (Lam pp_unary_ty
        (pp_compose (shift F) (Var 0)))
      G)"
  unfolding pp_composition_instance_def
proof (rule compatible_step.App_left, rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty
          (Lam pp_unary_ty
            (pp_compose (Var 1) (Var 0))))
        F)
      (subst0 F
        (Lam pp_unary_ty
          (pp_compose (Var 1) (Var 0))))"
    by (rule beta_contract.beta)
  show "beta_contract
      (App pp_composition_builder F)
      (Lam pp_unary_ty
        (pp_compose (shift F) (Var 0)))"
    using step
    by (simp add: pp_composition_builder_def pp_compose_def
      subst0_def subst_lift_shift shift_def)
qed

lemma pp_composition_instance_second_beta:
  "compatible_step beta_contract
    (App
      (Lam pp_unary_ty
        (pp_compose (shift F) (Var 0)))
      G)
    (pp_compose F G)"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty
          (pp_compose (shift F) (Var 0)))
        G)
      (subst0 G
        (pp_compose (shift F) (Var 0)))"
    by (rule beta_contract.beta)
  show "beta_contract
      (App
        (Lam pp_unary_ty
          (pp_compose (shift F) (Var 0)))
        G)
      (pp_compose F G)"
    using step
    by (simp add: pp_compose_def subst0_def subst_lift_shift)
qed

theorem CEV_pp_composition_instance_eq:
  assumes F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and G_type: "\<Gamma> \<turnstile> G : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (pp_composition_instance F G)
      (pp_compose F G)"
proof -
  let ?I = "pp_composition_instance F G"
  let ?M =
    "App
      (Lam pp_unary_ty
        (pp_compose (shift F) (Var 0)))
      G"
  let ?C = "pp_compose F G"
  have I_type: "\<Gamma> \<turnstile> ?I : pp_unary_ty"
    using F_type G_type by (rule typed_pp_composition_instance)
  have M_type: "\<Gamma> \<turnstile> ?M : pp_unary_ty"
  proof -
    have F_shift:
      "pp_unary_ty # \<Gamma> \<turnstile> shift F : pp_unary_ty"
      using F_type by (rule typed_shift_ctx)
    have v_type:
      "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
      by (rule typed_var0)
    have body_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_compose (shift F) (Var 0) : pp_unary_ty"
      using F_shift v_type by (rule typed_pp_compose)
    have lam_type:
      "\<Gamma> \<turnstile>
        Lam pp_unary_ty
          (pp_compose (shift F) (Var 0)) :
        pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
      using body_type by (rule has_type.Lam)
    show ?thesis
      using lam_type G_type by (rule has_type.App)
  qed
  have C_type: "\<Gamma> \<turnstile> ?C : pp_unary_ty"
    using F_type G_type by (rule typed_pp_compose)
  have op_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Eq (Prop \<rightarrow>\<^sub>o Prop) ?I ?C"
  proof (rule CEV_unary_equivalence)
    show "\<Gamma> \<turnstile> ?I : Prop \<rightarrow>\<^sub>o Prop"
      using I_type by (simp add: pp_unary_ty_def)
  next
    show "\<Gamma> \<turnstile> ?C : Prop \<rightarrow>\<^sub>o Prop"
      using C_type by (simp add: pp_unary_ty_def)
  next
    have Ip_type: "Prop # \<Gamma> \<turnstile> shift ?I : pp_unary_ty"
      using I_type by (rule typed_shift_ctx)
    have Mp_type: "Prop # \<Gamma> \<turnstile> shift ?M : pp_unary_ty"
      using M_type by (rule typed_shift_ctx)
    have Cp_type: "Prop # \<Gamma> \<turnstile> shift ?C : pp_unary_ty"
      using C_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    have A_type:
      "Prop # \<Gamma> \<turnstile> App (shift ?I) (Var 0) : Prop"
      using Ip_type v_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have B_type:
      "Prop # \<Gamma> \<turnstile> App (shift ?M) (Var 0) : Prop"
      using Mp_type v_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have Cx_type:
      "Prop # \<Gamma> \<turnstile> App (shift ?C) (Var 0) : Prop"
      using Cp_type v_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have first_shift:
      "compatible_step beta_contract (shift ?I) (shift ?M)"
      using compatible_beta_rename[
          OF pp_composition_instance_first_beta, where r = Suc]
      by (simp add: shift_def)
    have first_step:
      "compatible_step beta_contract
        (App (shift ?I) (Var 0))
        (App (shift ?M) (Var 0))"
      using first_shift by (rule compatible_step.App_left)
    have first:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App (shift ?I) (Var 0) \<longleftrightarrow>\<^sub>o
          App (shift ?M) (Var 0))"
      using A_type B_type first_step by (rule CEV_beta_step)
    have second_shift:
      "compatible_step beta_contract (shift ?M) (shift ?C)"
      using compatible_beta_rename[
          OF pp_composition_instance_second_beta, where r = Suc]
      by (simp add: shift_def)
    have second_step:
      "compatible_step beta_contract
        (App (shift ?M) (Var 0))
        (App (shift ?C) (Var 0))"
      using second_shift by (rule compatible_step.App_left)
    have second:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App (shift ?M) (Var 0) \<longleftrightarrow>\<^sub>o
          App (shift ?C) (Var 0))"
      using B_type Cx_type second_step by (rule CEV_beta_step)
    show "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (shift ?I) (Var 0) \<longleftrightarrow>\<^sub>o
        App (shift ?C) (Var 0))"
      using A_type B_type Cx_type first second
      by (rule CEV_biconditional_trans)
  qed
  show ?thesis
    using op_eq by (simp add: pp_unary_ty_def)
qed

lemma pp_composition_builder_purity_axiom:
  "pp_pure
      (pp_unary_ty \<rightarrow>\<^sub>o
        (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty))
      pp_composition_builder \<in> pp_T6_core_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
proof (intro UnI1 CollectI exI conjI)
  show "[] \<turnstile> pp_composition_builder :
      pp_unary_ty \<rightarrow>\<^sub>o
        (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty)"
    by (rule typed_pp_composition_builder)
  show "consts_of pp_composition_builder = {}"
    by (rule pp_composition_builder_constant_free)
qed simp

theorem pp_compose_pure:
  assumes F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and G_type: "\<Gamma> \<turnstile> G : pp_unary_ty"
    and pure_F:
      "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty F"
    and pure_G:
      "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty G"
  shows "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty (pp_compose F G)"
proof -
  have builder_pure:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure
        (pp_unary_ty \<rightarrow>\<^sub>o
          (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty))
        pp_composition_builder"
    using pp_composition_builder_purity_axiom
      typed_pp_pure[OF typed_pp_composition_builder]
    by (rule CEV_axiom_proves.Axiom)
  have first_pure:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure
        (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty)
        (App pp_composition_builder F)"
    using pp_T6_application_closure_axiom
      typed_pp_composition_builder F_type builder_pure pure_F
    by (rule pp_axiom_application_closed)
  have instance_pure:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty (pp_composition_instance F G)"
    unfolding pp_composition_instance_def
    using pp_T6_application_closure_axiom
      has_type.App[OF typed_pp_composition_builder F_type]
      G_type first_pure pure_G
    by (rule pp_axiom_application_closed)
  have ll: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Eq pp_unary_ty
          (pp_composition_instance F G)
          (pp_compose F G))
        (Imp
          (pp_pure pp_unary_ty (pp_composition_instance F G))
          (pp_pure pp_unary_ty (pp_compose F G)))"
    using typed_pp_composition_instance[OF F_type G_type]
      typed_pp_compose[OF F_type G_type] typed_pp_Pure
    unfolding pp_pure_def
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have transfer:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (pp_pure pp_unary_ty (pp_composition_instance F G))
        (pp_pure pp_unary_ty (pp_compose F G))"
    by (rule CEV_axiom_proves.MP
        [OF CEV_axiom_proves.Base[
              OF CEV_pp_composition_instance_eq[OF F_type G_type]]
            CEV_axiom_proves.Base[OF ll]])
  show ?thesis
    using instance_pure transfer by (rule CEV_axiom_proves.MP)
qed

theorem pp_compose_pure_in:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and G_type: "\<Gamma> \<turnstile> G : pp_unary_ty"
    and pure_F:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty F"
    and pure_G:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty G"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty (pp_compose F G)"
proof -
  have builder_pure_core:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure
        (pp_unary_ty \<rightarrow>\<^sub>o
          (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty))
        pp_composition_builder"
    using pp_composition_builder_purity_axiom
      typed_pp_pure[OF typed_pp_composition_builder]
    by (rule CEV_axiom_proves.Axiom)
  have builder_pure:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure
        (pp_unary_ty \<rightarrow>\<^sub>o
          (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty))
        pp_composition_builder"
    using builder_pure_core core by (rule CEV_axiom_proves_mono)
  have closure:
    "pp_application_closure \<sigma> \<tau> \<in> T" for \<sigma> \<tau>
    using pp_T6_application_closure_axiom core by blast
  have first_pure:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure
        (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty)
        (App pp_composition_builder F)"
    using closure
      typed_pp_composition_builder F_type builder_pure pure_F
    by (rule pp_axiom_application_closed)
  have instance_pure:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty (pp_composition_instance F G)"
    unfolding pp_composition_instance_def
    using closure
      has_type.App[OF typed_pp_composition_builder F_type]
      G_type first_pure pure_G
    by (rule pp_axiom_application_closed)
  have ll: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Eq pp_unary_ty
          (pp_composition_instance F G)
          (pp_compose F G))
        (Imp
          (pp_pure pp_unary_ty (pp_composition_instance F G))
          (pp_pure pp_unary_ty (pp_compose F G)))"
    using typed_pp_composition_instance[OF F_type G_type]
      typed_pp_compose[OF F_type G_type] typed_pp_Pure
    unfolding pp_pure_def
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have transfer:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (pp_pure pp_unary_ty (pp_composition_instance F G))
        (pp_pure pp_unary_ty (pp_compose F G))"
    by (rule CEV_axiom_proves.MP
        [OF CEV_axiom_proves.Base[
              OF CEV_pp_composition_instance_eq[OF F_type G_type]]
            CEV_axiom_proves.Base[OF ll]])
  show ?thesis
    using instance_pure transfer by (rule CEV_axiom_proves.MP)
qed

subsection \<open>Local algebra inside conditional derivations\<close>

lemma CEV_axiom_from_eq_sym:
  assumes A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and B_type: "\<Gamma> \<turnstile> B : \<sigma>"
    and eq:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> A B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> B A"
proof -
  have d:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Eq \<sigma> A B) (Eq \<sigma> B A)"
    using CEV_eq_sym[OF A_type B_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using eq d by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_eq_trans:
  assumes A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and B_type: "\<Gamma> \<turnstile> B : \<sigma>"
    and C_type: "\<Gamma> \<turnstile> C : \<sigma>"
    and AB:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> A B"
    and BC:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> B C"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> A C"
proof -
  have d:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Eq \<sigma> A B)
        (Imp (Eq \<sigma> B C) (Eq \<sigma> A C))"
    using CEV_eq_trans[OF A_type B_type C_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Eq \<sigma> B C) (Eq \<sigma> A C)"
    using AB d by (rule CEV_axiom_from.MP)
  show ?thesis
    using BC step by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_eq_app_right:
  assumes F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and B_type: "\<Gamma> \<turnstile> B : \<sigma>"
    and AB:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> A B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq \<tau> (App F A) (App F B)"
proof -
  have d:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Eq \<sigma> A B)
        (Eq \<tau> (App F A) (App F B))"
    using CEV_eq_app_right[OF F_type A_type B_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using AB d by (rule CEV_axiom_from.MP)
qed

lemma pp_axiom_application_closed_imp:
  assumes closure: "pp_application_closure \<sigma> \<tau> \<in> T"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and X_type: "\<Gamma> \<turnstile> X : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F)
        (pp_pure \<sigma> X))
      (pp_pure \<tau> (App F X))"
proof -
  have closure_type:
    "\<Gamma> \<turnstile> pp_application_closure \<sigma> \<tau> : Prop"
    by (rule infer_type_sound)
      (simp add: pp_application_closure_def pp_pure_def pp_Pure_def
        lookup_def)
  have d_closure:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_application_closure \<sigma> \<tau>"
    using closure closure_type by (rule CEV_axiom_proves.Axiom)
  have d_outer_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 F
        (Forall \<sigma>
          (Imp
            (Conj
              (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Var 1))
              (pp_pure \<sigma> (Var 0)))
            (pp_pure \<tau> (App (Var 1) (Var 0)))))"
  proof (rule CEV_axiom_UI_typed)
    show "\<Gamma> \<turnstile>
      Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
        (Forall \<sigma>
          (Imp
            (Conj
              (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Var 1))
              (pp_pure \<sigma> (Var 0)))
            (pp_pure \<tau> (App (Var 1) (Var 0))))) : Prop"
      using closure_type unfolding pp_application_closure_def .
    show "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
      by (rule F_type)
    show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
        (Forall \<sigma>
          (Imp
            (Conj
              (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Var 1))
              (pp_pure \<sigma> (Var 0)))
            (pp_pure \<tau> (App (Var 1) (Var 0)))))"
      using d_closure unfolding pp_application_closure_def .
  qed
  have d_outer:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall \<sigma>
        (Imp
          (Conj
            (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (shift F))
            (pp_pure \<sigma> (Var 0)))
          (pp_pure \<tau> (App (shift F) (Var 0))))"
    using d_outer_raw
    by (simp add: pp_pure_def pp_Pure_def subst0_def shift_def)
  have outer_type:
    "\<Gamma> \<turnstile>
      Forall \<sigma>
        (Imp
          (Conj
            (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (shift F))
            (pp_pure \<sigma> (Var 0)))
          (pp_pure \<tau> (App (shift F) (Var 0)))) : Prop"
    using CEV_axiom_proves_formula[OF d_outer] .
  have d_inner_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 X
        (Imp
          (Conj
            (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (shift F))
            (pp_pure \<sigma> (Var 0)))
          (pp_pure \<tau> (App (shift F) (Var 0))))"
    using outer_type X_type d_outer by (rule CEV_axiom_UI_typed)
  have subst_shift:
    "subst (case_nat X Var) (rename Suc F) = F"
    using subst0_shift[of X F]
    unfolding subst0_def shift_def .
  show ?thesis
    using d_inner_raw
    by (simp add: pp_pure_def pp_Pure_def subst0_def shift_def
      subst_shift)
qed

lemma pp_axiom_application_closed_from:
  assumes closure: "pp_application_closure \<sigma> \<tau> \<in> T"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and X_type: "\<Gamma> \<turnstile> X : \<sigma>"
    and pure_F:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F"
    and pure_X:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<sigma> X"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure \<tau> (App F X)"
proof -
  have pair:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F)
        (pp_pure \<sigma> X)"
    using pure_F pure_X by (rule CEV_axiom_from_conj_intro)
  have rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj
          (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F)
          (pp_pure \<sigma> X))
        (pp_pure \<tau> (App F X))"
    using pp_axiom_application_closed_imp[OF closure F_type X_type]
    by (rule CEV_axiom_from.Theorem)
  show ?thesis
    using pair rule by (rule CEV_axiom_from.MP)
qed

lemma pp_compose_pure_from:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and G_type: "\<Gamma> \<turnstile> G : pp_unary_ty"
    and pure_F:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty F"
    and pure_G:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty G"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_unary_ty (pp_compose F G)"
proof -
  have closure:
    "pp_application_closure \<sigma> \<tau> \<in> T" for \<sigma> \<tau>
    using pp_T6_application_closure_axiom core by blast
  have builder_pure_core:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure
        (pp_unary_ty \<rightarrow>\<^sub>o
          (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty))
        pp_composition_builder"
    using pp_composition_builder_purity_axiom
      typed_pp_pure[OF typed_pp_composition_builder]
    by (rule CEV_axiom_proves.Axiom)
  have builder_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure
        (pp_unary_ty \<rightarrow>\<^sub>o
          (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty))
        pp_composition_builder"
    using CEV_axiom_proves_mono[OF builder_pure_core core]
    by (rule CEV_axiom_from.Theorem)
  have first_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure
        (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty)
        (App pp_composition_builder F)"
    using closure typed_pp_composition_builder F_type
      builder_pure pure_F
    by (rule pp_axiom_application_closed_from)
  have instance_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty (pp_composition_instance F G)"
    unfolding pp_composition_instance_def
    using closure
      has_type.App[OF typed_pp_composition_builder F_type]
      G_type first_pure pure_G
    by (rule pp_axiom_application_closed_from)
  have ll:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Eq pp_unary_ty
          (pp_composition_instance F G)
          (pp_compose F G))
        (Imp
          (pp_pure pp_unary_ty (pp_composition_instance F G))
          (pp_pure pp_unary_ty (pp_compose F G)))"
    using typed_pp_composition_instance[OF F_type G_type]
      typed_pp_compose[OF F_type G_type] typed_pp_Pure
    unfolding pp_pure_def
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base
        CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty
        (pp_composition_instance F G)
        (pp_compose F G)"
    using CEV_pp_composition_instance_eq[OF F_type G_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have transfer:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (pp_pure pp_unary_ty (pp_composition_instance F G))
        (pp_pure pp_unary_ty (pp_compose F G))"
    using eq ll by (rule CEV_axiom_from.MP)
  show ?thesis
    using instance_pure transfer by (rule CEV_axiom_from.MP)
qed

end
