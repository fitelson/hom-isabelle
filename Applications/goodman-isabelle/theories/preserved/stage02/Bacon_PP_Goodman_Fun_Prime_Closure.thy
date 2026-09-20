theory Bacon_PP_Goodman_Fun_Prime_Closure
  imports 
    "Goodman_Legacy_02.Bacon_PP_Goodman_Composition"
begin

section \<open>Goodman's closure of \<open>fun\<acute>\<close> under reversible operators\<close>

lemma shift_Conj_term[simp]:
  "shift (Conj A B) = Conj (shift A) (shift B)"
  by (simp add: shift_def)

lemma shift_Eq_term[simp]:
  "shift (Eq \<sigma> A B) = Eq \<sigma> (shift A) (shift B)"
  by (simp add: shift_def)

lemma shift_Imp_term[simp]:
  "shift (Imp A B) = Imp (shift A) (shift B)"
  by (simp add: shift_def)

lemma shift_App_term[simp]:
  "shift (App F X) = App (shift F) (shift X)"
  by (simp add: shift_def)

lemma rename_pp_compose[simp]:
  "rename r (pp_compose F G) =
    pp_compose (rename r F) (rename r G)"
  by (simp add: pp_compose_def shift_rename_lift)

lemma shift_pp_pure_term[simp]:
  "shift (pp_pure \<sigma> X) = pp_pure \<sigma> (shift X)"
  by (simp add: shift_def pp_pure_def pp_Pure_def)

lemma shift_pp_fun_prime_term[simp]:
  "shift (pp_fun_prime p) = pp_fun_prime (shift p)"
  unfolding shift_def pp_fun_prime_def pp_pure_def pp_Pure_def
    shift_by_def
  apply (simp add: rename_comp)
  by (rule rename_cong) (simp add: shift_ren_def)

lemma shift_shift_eq_shift_by_2:
  "shift (shift M) = shift_by 2 M"
  unfolding shift_def shift_by_def
  apply (simp only: rename_comp)
  by (rule rename_cong) (simp add: shift_ren_def)

subsection \<open>Elimination rule for \<open>fun\<acute>\<close>\<close>

lemma CEV_axiom_from_fun_prime:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and A_type: "\<Gamma> \<turnstile> A : pp_unary_ty"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and fun_p:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
    and pure_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty A"
    and pure_B:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty B"
    and same_value:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App A p) (App B p)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty A B"
proof -
  have outer_raw:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 A
        (Forall pp_unary_ty
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 1))
              (pp_pure pp_unary_ty (Var 0)))
            (Imp
              (Eq Prop
                (App (Var 1) (shift_by 2 p))
                (App (Var 0) (shift_by 2 p)))
              (Eq pp_unary_ty (Var 1) (Var 0)))))"
  proof (rule CEV_axiom_from_UI_typed)
    show "\<Gamma> \<turnstile>
      Forall pp_unary_ty
        (Forall pp_unary_ty
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 1))
              (pp_pure pp_unary_ty (Var 0)))
            (Imp
              (Eq Prop
                (App (Var 1) (shift_by 2 p))
                (App (Var 0) (shift_by 2 p)))
              (Eq pp_unary_ty (Var 1) (Var 0))))) : Prop"
      using typed_pp_fun_prime[OF p_type]
      unfolding pp_fun_prime_def .
    show "\<Gamma> \<turnstile> A : pp_unary_ty"
      by (rule A_type)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall pp_unary_ty
        (Forall pp_unary_ty
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 1))
              (pp_pure pp_unary_ty (Var 0)))
            (Imp
              (Eq Prop
                (App (Var 1) (shift_by 2 p))
                (App (Var 0) (shift_by 2 p)))
              (Eq pp_unary_ty (Var 1) (Var 0)))))"
      using fun_p unfolding pp_fun_prime_def .
  qed
  have outer:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall pp_unary_ty
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift A))
            (pp_pure pp_unary_ty (Var 0)))
          (Imp
            (Eq Prop
              (App (shift A) (shift p))
              (App (Var 0) (shift p)))
            (Eq pp_unary_ty (shift A) (Var 0))))"
    using outer_raw
    by (simp add: pp_fun_prime_def pp_pure_def pp_Pure_def
      subst0_def shift_by_def shift_ren_def shift_def
      subst_lift_shift_by_2)
  have outer_type:
    "\<Gamma> \<turnstile>
      Forall pp_unary_ty
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift A))
            (pp_pure pp_unary_ty (Var 0)))
          (Imp
            (Eq Prop
              (App (shift A) (shift p))
              (App (Var 0) (shift p)))
            (Eq pp_unary_ty (shift A) (Var 0)))) : Prop"
    using outer by (rule CEV_axiom_from_formula)
  have inner_raw:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 B
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift A))
            (pp_pure pp_unary_ty (Var 0)))
          (Imp
            (Eq Prop
              (App (shift A) (shift p))
              (App (Var 0) (shift p)))
            (Eq pp_unary_ty (shift A) (Var 0))))"
    using outer_type B_type outer by (rule CEV_axiom_from_UI_typed)
  have rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj
          (pp_pure pp_unary_ty A)
          (pp_pure pp_unary_ty B))
        (Imp
          (Eq Prop (App A p) (App B p))
          (Eq pp_unary_ty A B))"
  proof -
    have subst_A:
      "subst (case_nat B Var) (rename Suc A) = A"
      using subst0_shift[of B A]
      unfolding subst0_def shift_def .
    have subst_p:
      "subst (case_nat B Var) (rename Suc p) = p"
      using subst0_shift[of B p]
      unfolding subst0_def shift_def .
    show ?thesis
    using inner_raw
      by (simp add: pp_pure_def pp_Pure_def subst0_def shift_def
        subst_A subst_p)
  qed
  have pair:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty A)
        (pp_pure pp_unary_ty B)"
    using pure_A pure_B by (rule CEV_axiom_from_conj_intro)
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Eq Prop (App A p) (App B p))
        (Eq pp_unary_ty A B)"
    using pair rule by (rule CEV_axiom_from.MP)
  show ?thesis
    using same_value step by (rule CEV_axiom_from.MP)
qed

subsection \<open>Congruence of composition\<close>

lemma CEV_unary_eq_of_beta_step:
  assumes A_type: "\<Gamma> \<turnstile> A : pp_unary_ty"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and step: "compatible_step beta_contract A B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Eq pp_unary_ty A B"
proof -
  have op_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Eq (Prop \<rightarrow>\<^sub>o Prop) A B"
  proof (rule CEV_unary_equivalence)
    show "\<Gamma> \<turnstile> A : Prop \<rightarrow>\<^sub>o Prop"
      using A_type by (simp add: pp_unary_ty_def)
    show "\<Gamma> \<turnstile> B : Prop \<rightarrow>\<^sub>o Prop"
      using B_type by (simp add: pp_unary_ty_def)
    have Ap_type: "Prop # \<Gamma> \<turnstile> shift A : pp_unary_ty"
      using A_type by (rule typed_shift_ctx)
    have Bp_type: "Prop # \<Gamma> \<turnstile> shift B : pp_unary_ty"
      using B_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    have left_type:
      "Prop # \<Gamma> \<turnstile> App (shift A) (Var 0) : Prop"
      using Ap_type v_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have right_type:
      "Prop # \<Gamma> \<turnstile> App (shift B) (Var 0) : Prop"
      using Bp_type v_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have shifted:
      "compatible_step beta_contract (shift A) (shift B)"
      using compatible_beta_rename[OF step, where r = Suc]
      by (simp add: shift_def)
    have app_step:
      "compatible_step beta_contract
        (App (shift A) (Var 0))
        (App (shift B) (Var 0))"
      using shifted by (rule compatible_step.App_left)
    show "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (shift A) (Var 0) \<longleftrightarrow>\<^sub>o
        App (shift B) (Var 0))"
      using left_type right_type app_step by (rule CEV_beta_step)
  qed
  show ?thesis
    using op_eq by (simp add: pp_unary_ty_def)
qed

definition pp_postcompose_context :: "oterm \<Rightarrow> oterm" where
  "pp_postcompose_context Z =
    Lam pp_unary_ty
      (pp_compose (Var 0) (shift Z))"

definition pp_precompose_context :: "oterm \<Rightarrow> oterm" where
  "pp_precompose_context Z =
    Lam pp_unary_ty
      (pp_compose (shift Z) (Var 0))"

lemma typed_pp_postcompose_context:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_postcompose_context Z :
    pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
proof (unfold pp_postcompose_context_def, rule has_type.Lam)
  have v_type: "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
    by (rule typed_var0)
  have Z_shift: "pp_unary_ty # \<Gamma> \<turnstile> shift Z : pp_unary_ty"
    using Z_type by (rule typed_shift_ctx)
  show "pp_unary_ty # \<Gamma> \<turnstile>
    pp_compose (Var 0) (shift Z) : pp_unary_ty"
    using v_type Z_shift by (rule typed_pp_compose)
qed

lemma typed_pp_precompose_context:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_precompose_context Z :
    pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
proof (unfold pp_precompose_context_def, rule has_type.Lam)
  have v_type: "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
    by (rule typed_var0)
  have Z_shift: "pp_unary_ty # \<Gamma> \<turnstile> shift Z : pp_unary_ty"
    using Z_type by (rule typed_shift_ctx)
  show "pp_unary_ty # \<Gamma> \<turnstile>
    pp_compose (shift Z) (Var 0) : pp_unary_ty"
    using Z_shift v_type by (rule typed_pp_compose)
qed

lemma pp_postcompose_context_beta:
  "compatible_step beta_contract
    (App (pp_postcompose_context Z) A)
    (pp_compose A Z)"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty
          (pp_compose (Var 0) (shift Z)))
        A)
      (subst0 A (pp_compose (Var 0) (shift Z)))"
    by (rule beta_contract.beta)
  show "beta_contract
    (App (pp_postcompose_context Z) A)
    (pp_compose A Z)"
    using step
    by (simp add: pp_postcompose_context_def pp_compose_def
      subst0_def subst_lift_shift)
qed

lemma pp_precompose_context_beta:
  "compatible_step beta_contract
    (App (pp_precompose_context Z) A)
    (pp_compose Z A)"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty
          (pp_compose (shift Z) (Var 0)))
        A)
      (subst0 A (pp_compose (shift Z) (Var 0)))"
    by (rule beta_contract.beta)
  show "beta_contract
    (App (pp_precompose_context Z) A)
    (pp_compose Z A)"
    using step
    by (simp add: pp_precompose_context_def pp_compose_def
      subst0_def subst_lift_shift)
qed

lemma CEV_pp_postcompose_context_eq:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and A_type: "\<Gamma> \<turnstile> A : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (App (pp_postcompose_context Z) A)
      (pp_compose A Z)"
proof (rule CEV_unary_eq_of_beta_step)
  show "\<Gamma> \<turnstile>
    App (pp_postcompose_context Z) A : pp_unary_ty"
    using typed_pp_postcompose_context[OF Z_type] A_type
    by (rule has_type.App)
  show "\<Gamma> \<turnstile> pp_compose A Z : pp_unary_ty"
    using A_type Z_type by (rule typed_pp_compose)
  show "compatible_step beta_contract
    (App (pp_postcompose_context Z) A)
    (pp_compose A Z)"
    by (rule pp_postcompose_context_beta)
qed

lemma CEV_pp_precompose_context_eq:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and A_type: "\<Gamma> \<turnstile> A : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (App (pp_precompose_context Z) A)
      (pp_compose Z A)"
proof (rule CEV_unary_eq_of_beta_step)
  show "\<Gamma> \<turnstile>
    App (pp_precompose_context Z) A : pp_unary_ty"
    using typed_pp_precompose_context[OF Z_type] A_type
    by (rule has_type.App)
  show "\<Gamma> \<turnstile> pp_compose Z A : pp_unary_ty"
    using Z_type A_type by (rule typed_pp_compose)
  show "compatible_step beta_contract
    (App (pp_precompose_context Z) A)
    (pp_compose Z A)"
    by (rule pp_precompose_context_beta)
qed

lemma CEV_axiom_from_pp_compose_cong_left:
  assumes A_type: "\<Gamma> \<turnstile> A : pp_unary_ty"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and AB:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty A B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq pp_unary_ty (pp_compose A Z) (pp_compose B Z)"
proof -
  let ?K = "pp_postcompose_context Z"
  let ?KA = "App ?K A"
  let ?KB = "App ?K B"
  have K_type: "\<Gamma> \<turnstile> ?K : pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
    using Z_type by (rule typed_pp_postcompose_context)
  have KA_type: "\<Gamma> \<turnstile> ?KA : pp_unary_ty"
    using K_type A_type by (rule has_type.App)
  have KB_type: "\<Gamma> \<turnstile> ?KB : pp_unary_ty"
    using K_type B_type by (rule has_type.App)
  have AZ_type: "\<Gamma> \<turnstile> pp_compose A Z : pp_unary_ty"
    using A_type Z_type by (rule typed_pp_compose)
  have BZ_type: "\<Gamma> \<turnstile> pp_compose B Z : pp_unary_ty"
    using B_type Z_type by (rule typed_pp_compose)
  have eq_apps:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty ?KA ?KB"
    using K_type A_type B_type AB
    by (rule CEV_axiom_from_eq_app_right)
  have norm_A:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?KA (pp_compose A Z)"
    using CEV_pp_postcompose_context_eq[OF Z_type A_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have norm_A_sym:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty (pp_compose A Z) ?KA"
    using KA_type AZ_type norm_A by (rule CEV_axiom_from_eq_sym)
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty (pp_compose A Z) ?KB"
    using AZ_type KA_type KB_type norm_A_sym eq_apps
    by (rule CEV_axiom_from_eq_trans)
  have norm_B:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?KB (pp_compose B Z)"
    using CEV_pp_postcompose_context_eq[OF Z_type B_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using AZ_type KB_type BZ_type step norm_B
    by (rule CEV_axiom_from_eq_trans)
qed

lemma CEV_axiom_from_pp_compose_cong_right:
  assumes A_type: "\<Gamma> \<turnstile> A : pp_unary_ty"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and AB:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty A B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq pp_unary_ty (pp_compose Z A) (pp_compose Z B)"
proof -
  let ?K = "pp_precompose_context Z"
  let ?KA = "App ?K A"
  let ?KB = "App ?K B"
  have K_type: "\<Gamma> \<turnstile> ?K : pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
    using Z_type by (rule typed_pp_precompose_context)
  have KA_type: "\<Gamma> \<turnstile> ?KA : pp_unary_ty"
    using K_type A_type by (rule has_type.App)
  have KB_type: "\<Gamma> \<turnstile> ?KB : pp_unary_ty"
    using K_type B_type by (rule has_type.App)
  have ZA_type: "\<Gamma> \<turnstile> pp_compose Z A : pp_unary_ty"
    using Z_type A_type by (rule typed_pp_compose)
  have ZB_type: "\<Gamma> \<turnstile> pp_compose Z B : pp_unary_ty"
    using Z_type B_type by (rule typed_pp_compose)
  have eq_apps:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty ?KA ?KB"
    using K_type A_type B_type AB
    by (rule CEV_axiom_from_eq_app_right)
  have norm_A:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?KA (pp_compose Z A)"
    using CEV_pp_precompose_context_eq[OF Z_type A_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have norm_A_sym:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty (pp_compose Z A) ?KA"
    using KA_type ZA_type norm_A by (rule CEV_axiom_from_eq_sym)
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty (pp_compose Z A) ?KB"
    using ZA_type KA_type KB_type norm_A_sym eq_apps
    by (rule CEV_axiom_from_eq_trans)
  have norm_B:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?KB (pp_compose Z B)"
    using CEV_pp_precompose_context_eq[OF Z_type B_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using ZA_type KB_type ZB_type step norm_B
    by (rule CEV_axiom_from_eq_trans)
qed

subsection \<open>Cancellation by an explicit right inverse\<close>

lemma CEV_pp_compose_apply_eq:
  assumes F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and G_type: "\<Gamma> \<turnstile> G : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop
      (App (pp_compose F G) p)
      (App F (App G p))"
proof -
  have left_type:
    "\<Gamma> \<turnstile> App (pp_compose F G) p : Prop"
    using typed_pp_compose[OF F_type G_type] p_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have Gp_type: "\<Gamma> \<turnstile> App G p : Prop"
    using G_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have right_type: "\<Gamma> \<turnstile> App F (App G p) : Prop"
    using F_type Gp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    using left_type right_type
      CEV_pp_compose_apply[OF F_type G_type p_type]
    by (rule CEV_zeroary_equivalence)
qed

lemma CEV_axiom_from_cancel_right_inverse:
  assumes Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and W_type: "\<Gamma> \<turnstile> W : pp_unary_ty"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and I_type: "\<Gamma> \<turnstile> I : pp_unary_ty"
    and YZ_WZ:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (pp_compose Y Z)
          (pp_compose W Z)"
    and right_inverse:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (pp_compose Z I)
          pp_identity_operator"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq pp_unary_ty Y W"
proof -
  let ?YZ = "pp_compose Y Z"
  let ?WZ = "pp_compose W Z"
  let ?ZI = "pp_compose Z I"
  let ?LY = "pp_compose ?YZ I"
  let ?LW = "pp_compose ?WZ I"
  let ?AY = "pp_compose Y ?ZI"
  let ?AW = "pp_compose W ?ZI"
  let ?Yid = "pp_compose Y pp_identity_operator"
  let ?Wid = "pp_compose W pp_identity_operator"
  have YZ_type: "\<Gamma> \<turnstile> ?YZ : pp_unary_ty"
    using Y_type Z_type by (rule typed_pp_compose)
  have WZ_type: "\<Gamma> \<turnstile> ?WZ : pp_unary_ty"
    using W_type Z_type by (rule typed_pp_compose)
  have ZI_type: "\<Gamma> \<turnstile> ?ZI : pp_unary_ty"
    using Z_type I_type by (rule typed_pp_compose)
  have LY_type: "\<Gamma> \<turnstile> ?LY : pp_unary_ty"
    using YZ_type I_type by (rule typed_pp_compose)
  have LW_type: "\<Gamma> \<turnstile> ?LW : pp_unary_ty"
    using WZ_type I_type by (rule typed_pp_compose)
  have AY_type: "\<Gamma> \<turnstile> ?AY : pp_unary_ty"
    using Y_type ZI_type by (rule typed_pp_compose)
  have AW_type: "\<Gamma> \<turnstile> ?AW : pp_unary_ty"
    using W_type ZI_type by (rule typed_pp_compose)
  have Yid_type: "\<Gamma> \<turnstile> ?Yid : pp_unary_ty"
    using Y_type typed_pp_identity_operator by (rule typed_pp_compose)
  have Wid_type: "\<Gamma> \<turnstile> ?Wid : pp_unary_ty"
    using W_type typed_pp_identity_operator by (rule typed_pp_compose)
  have composed:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?LY ?LW"
    using YZ_type WZ_type I_type YZ_WZ
    by (rule CEV_axiom_from_pp_compose_cong_left)
  have assoc_Y:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?LY ?AY"
    using CEV_pp_compose_associative[OF Y_type Z_type I_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have replace_Y:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?AY ?Yid"
    using ZI_type typed_pp_identity_operator Y_type right_inverse
    by (rule CEV_axiom_from_pp_compose_cong_right)
  have unit_Y:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?Yid Y"
    using CEV_pp_compose_right_identity[OF Y_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have LY_AY_Yid:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?LY ?Yid"
    using LY_type AY_type Yid_type assoc_Y replace_Y
    by (rule CEV_axiom_from_eq_trans)
  have norm_Y:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?LY Y"
    using LY_type Yid_type Y_type LY_AY_Yid unit_Y
    by (rule CEV_axiom_from_eq_trans)
  have assoc_W:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?LW ?AW"
    using CEV_pp_compose_associative[OF W_type Z_type I_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have replace_W:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?AW ?Wid"
    using ZI_type typed_pp_identity_operator W_type right_inverse
    by (rule CEV_axiom_from_pp_compose_cong_right)
  have unit_W:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?Wid W"
    using CEV_pp_compose_right_identity[OF W_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have LW_AW_Wid:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?LW ?Wid"
    using LW_type AW_type Wid_type assoc_W replace_W
    by (rule CEV_axiom_from_eq_trans)
  have norm_W:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?LW W"
    using LW_type Wid_type W_type LW_AW_Wid unit_W
    by (rule CEV_axiom_from_eq_trans)
  have norm_Y_sym:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty Y ?LY"
    using LY_type Y_type norm_Y by (rule CEV_axiom_from_eq_sym)
  have Y_LW:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty Y ?LW"
    using Y_type LY_type LW_type norm_Y_sym composed
    by (rule CEV_axiom_from_eq_trans)
  show ?thesis
    using Y_type LW_type W_type Y_LW norm_W
    by (rule CEV_axiom_from_eq_trans)
qed

theorem CEV_axiom_from_fun_prime_under_explicit_inverse:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and W_type: "\<Gamma> \<turnstile> W : pp_unary_ty"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and I_type: "\<Gamma> \<turnstile> I : pp_unary_ty"
    and fun_p:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
    and pure_Y:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty Y"
    and pure_W:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty W"
    and pure_Z:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty Z"
    and same_value:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop
          (App Y (App Z p))
          (App W (App Z p))"
    and right_inverse:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (pp_compose Z I)
          pp_identity_operator"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq pp_unary_ty Y W"
proof -
  let ?YZ = "pp_compose Y Z"
  let ?WZ = "pp_compose W Z"
  let ?YZp = "App ?YZ p"
  let ?WZp = "App ?WZ p"
  let ?Y_Zp = "App Y (App Z p)"
  let ?W_Zp = "App W (App Z p)"
  have YZ_type: "\<Gamma> \<turnstile> ?YZ : pp_unary_ty"
    using Y_type Z_type by (rule typed_pp_compose)
  have WZ_type: "\<Gamma> \<turnstile> ?WZ : pp_unary_ty"
    using W_type Z_type by (rule typed_pp_compose)
  have Zp_type: "\<Gamma> \<turnstile> App Z p : Prop"
    using Z_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have YZp_type: "\<Gamma> \<turnstile> ?YZp : Prop"
    using YZ_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have WZp_type: "\<Gamma> \<turnstile> ?WZp : Prop"
    using WZ_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Y_Zp_type: "\<Gamma> \<turnstile> ?Y_Zp : Prop"
    using Y_type Zp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have W_Zp_type: "\<Gamma> \<turnstile> ?W_Zp : Prop"
    using W_type Zp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have pure_YZ:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?YZ"
    using core Y_type Z_type pure_Y pure_Z
    by (rule pp_compose_pure_from)
  have pure_WZ:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?WZ"
    using core W_type Z_type pure_W pure_Z
    by (rule pp_compose_pure_from)
  have beta_Y:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?YZp ?Y_Zp"
    using CEV_pp_compose_apply_eq[OF Y_type Z_type p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have beta_W:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?WZp ?W_Zp"
    using CEV_pp_compose_apply_eq[OF W_type Z_type p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have beta_W_sym:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?W_Zp ?WZp"
    using WZp_type W_Zp_type beta_W by (rule CEV_axiom_from_eq_sym)
  have first:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?YZp ?W_Zp"
    using YZp_type Y_Zp_type W_Zp_type beta_Y same_value
    by (rule CEV_axiom_from_eq_trans)
  have composed_same:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?YZp ?WZp"
    using YZp_type W_Zp_type WZp_type first beta_W_sym
    by (rule CEV_axiom_from_eq_trans)
  have composed_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?YZ ?WZ"
    using p_type YZ_type WZ_type fun_p pure_YZ pure_WZ composed_same
    by (rule CEV_axiom_from_fun_prime)
  show ?thesis
    using Y_type W_type Z_type I_type composed_eq right_inverse
    by (rule CEV_axiom_from_cancel_right_inverse)
qed

subsection \<open>The object-language explicit-inverse closure theorem\<close>

definition pp_fun_prime_explicit_inverse_premises ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_fun_prime_explicit_inverse_premises p Z I =
    Conj
      (pp_fun_prime p)
      (Conj
        (pp_pure pp_unary_ty Z)
        (Eq pp_unary_ty
          (pp_compose Z I)
          pp_identity_operator))"

lemma typed_pp_fun_prime_explicit_inverse_premises:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and I_type: "\<Gamma> \<turnstile> I : pp_unary_ty"
  shows "\<Gamma> \<turnstile>
    pp_fun_prime_explicit_inverse_premises p Z I : Prop"
  unfolding pp_fun_prime_explicit_inverse_premises_def
  using typed_pp_fun_prime[OF p_type]
    typed_pp_pure[OF Z_type]
    typed_pp_compose[OF Z_type I_type]
    typed_pp_identity_operator
  by (intro has_type.Conj has_type.Eq)

lemma shift_pp_fun_prime_explicit_inverse_premises[simp]:
  "shift (pp_fun_prime_explicit_inverse_premises p Z I) =
    pp_fun_prime_explicit_inverse_premises
      (shift p) (shift Z) (shift I)"
  by (simp add: pp_fun_prime_explicit_inverse_premises_def)

theorem CEV_fun_prime_under_explicit_inverse:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and I_type: "\<Gamma> \<turnstile> I : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime_explicit_inverse_premises p Z I)
      (pp_fun_prime (App Z p))"
proof -
  let ?P =
    "pp_fun_prime_explicit_inverse_premises p Z I"
  let ?p1 = "shift p"
  let ?Z1 = "shift Z"
  let ?I1 = "shift I"
  let ?P1 =
    "pp_fun_prime_explicit_inverse_premises ?p1 ?Z1 ?I1"
  let ?p2 = "shift_by 2 p"
  let ?Z2 = "shift_by 2 Z"
  let ?I2 = "shift_by 2 I"
  let ?P2 =
    "pp_fun_prime_explicit_inverse_premises ?p2 ?Z2 ?I2"
  let ?Y = "Var 1"
  let ?W = "Var 0"
  let ?Zp = "App ?Z2 ?p2"
  let ?pair =
    "Conj
      (pp_pure pp_unary_ty ?Y)
      (pp_pure pp_unary_ty ?W)"
  let ?same =
    "Eq Prop
      (App ?Y ?Zp)
      (App ?W ?Zp)"
  let ?conclusion = "Eq pp_unary_ty ?Y ?W"
  let ?body = "Imp ?pair (Imp ?same ?conclusion)"
  have p1_type: "pp_unary_ty # \<Gamma> \<turnstile> ?p1 : Prop"
    using p_type by (rule typed_shift_ctx)
  have Z1_type: "pp_unary_ty # \<Gamma> \<turnstile> ?Z1 : pp_unary_ty"
    using Z_type by (rule typed_shift_ctx)
  have I1_type: "pp_unary_ty # \<Gamma> \<turnstile> ?I1 : pp_unary_ty"
    using I_type by (rule typed_shift_ctx)
  have p2_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?p2 : Prop"
  proof -
    have "[pp_unary_ty, pp_unary_ty] @ \<Gamma> \<turnstile>
      shift_by (length [pp_unary_ty, pp_unary_ty]) p : Prop"
      using p_type by (rule shift_by_preserves_typing)
    then show ?thesis by (simp add: numeral_2_eq_2)
  qed
  have Z2_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?Z2 : pp_unary_ty"
  proof -
    have "[pp_unary_ty, pp_unary_ty] @ \<Gamma> \<turnstile>
      shift_by (length [pp_unary_ty, pp_unary_ty]) Z : pp_unary_ty"
      using Z_type by (rule shift_by_preserves_typing)
    then show ?thesis by (simp add: numeral_2_eq_2)
  qed
  have I2_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?I2 : pp_unary_ty"
  proof -
    have "[pp_unary_ty, pp_unary_ty] @ \<Gamma> \<turnstile>
      shift_by (length [pp_unary_ty, pp_unary_ty]) I : pp_unary_ty"
      using I_type by (rule shift_by_preserves_typing)
    then show ?thesis by (simp add: numeral_2_eq_2)
  qed
  have Y_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?Y : pp_unary_ty"
    by (rule has_type.Var) (simp add: lookup_def)
  have W_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?W : pp_unary_ty"
    by (rule typed_var0)
  have Zp_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?Zp : Prop"
    using Z2_type p2_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have pair_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?pair : Prop"
    using typed_pp_pure[OF Y_type] typed_pp_pure[OF W_type]
    by (rule has_type.Conj)
  have YZp_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile>
      App ?Y ?Zp : Prop"
    using Y_type Zp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have WZp_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile>
      App ?W ?Zp : Prop"
    using W_type Zp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have same_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?same : Prop"
    using YZp_type WZp_type by (rule has_type.Eq)
  have conclusion_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?conclusion : Prop"
    using Y_type W_type by (rule has_type.Eq)
  have body_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?body : Prop"
    using pair_type same_type conclusion_type
    by (intro has_type.Imp)
  have P2_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?P2 : Prop"
    using p2_type Z2_type I2_type
    by (rule typed_pp_fun_prime_explicit_inverse_premises)
  have d_P2:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ;
      insert ?same (insert ?pair {?P2})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P2"
    using P2_type by (intro CEV_axiom_from.Assumption) simp
  have d_fun:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ;
      insert ?same (insert ?pair {?P2})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime ?p2"
    using d_P2
    unfolding pp_fun_prime_explicit_inverse_premises_def
    by (rule CEV_axiom_from_conj_left)
  have d_right:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ;
      insert ?same (insert ?pair {?P2})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Conj
          (pp_pure pp_unary_ty ?Z2)
          (Eq pp_unary_ty
            (pp_compose ?Z2 ?I2)
            pp_identity_operator)"
    using d_P2
    unfolding pp_fun_prime_explicit_inverse_premises_def
    by (rule CEV_axiom_from_conj_right)
  have d_pure_Z:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ;
      insert ?same (insert ?pair {?P2})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty ?Z2"
    using d_right by (rule CEV_axiom_from_conj_left)
  have d_inverse:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ;
      insert ?same (insert ?pair {?P2})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (pp_compose ?Z2 ?I2)
          pp_identity_operator"
    using d_right by (rule CEV_axiom_from_conj_right)
  have d_pair:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ;
      insert ?same (insert ?pair {?P2})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?pair"
    using pair_type by (intro CEV_axiom_from.Assumption) simp
  have d_pure_Y:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ;
      insert ?same (insert ?pair {?P2})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty ?Y"
    using d_pair by (rule CEV_axiom_from_conj_left)
  have d_pure_W:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ;
      insert ?same (insert ?pair {?P2})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty ?W"
    using d_pair by (rule CEV_axiom_from_conj_right)
  have d_same:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ;
      insert ?same (insert ?pair {?P2})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?same"
    using same_type by (intro CEV_axiom_from.Assumption) simp
  have d_conclusion:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ;
      insert ?same (insert ?pair {?P2})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?conclusion"
    using core p2_type Y_type W_type Z2_type I2_type
      d_fun d_pure_Y d_pure_W d_pure_Z d_same d_inverse
    by (rule CEV_axiom_from_fun_prime_under_explicit_inverse)
  have d_same_imp:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ;
      insert ?pair {?P2}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?same ?conclusion"
    using same_type d_conclusion by (rule CEV_axiom_from_deduction)
  have d_pair_imp:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ; {?P2}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?body"
    using pair_type d_same_imp by (rule CEV_axiom_from_deduction)
  have d_P2_imp_local:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?P2 ?body"
    using P2_type d_pair_imp by (rule CEV_axiom_from_deduction)
  have d_P2_imp:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T
      \<turnstile>\<^sub>CEV\<^sup>+ Imp ?P2 ?body"
    using d_P2_imp_local CEV_axiom_from_empty_iff by blast
  have P1_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?P1 : Prop"
    using p1_type Z1_type I1_type
    by (rule typed_pp_fun_prime_explicit_inverse_premises)
  have inner_body_type:
    "pp_unary_ty # \<Gamma> \<turnstile> Forall pp_unary_ty ?body : Prop"
    using body_type by (rule has_type.Forall)
  have d_inner:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P1 (Forall pp_unary_ty ?body)"
  proof (rule CEV_axiom_proves.Gen)
    show "pp_unary_ty # \<Gamma> \<turnstile> ?P1 : Prop"
      by (rule P1_type)
    show "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?body : Prop"
      by (rule body_type)
    show "pp_unary_ty # pp_unary_ty # \<Gamma> ; T
      \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ?P1) ?body"
      using d_P2_imp
      by (simp add: shift_shift_eq_shift_by_2)
  qed
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using p_type Z_type I_type
    by (rule typed_pp_fun_prime_explicit_inverse_premises)
  have d_outer:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P (Forall pp_unary_ty (Forall pp_unary_ty ?body))"
  proof (rule CEV_axiom_proves.Gen)
    show "\<Gamma> \<turnstile> ?P : Prop"
      by (rule P_type)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      Forall pp_unary_ty ?body : Prop"
      by (rule inner_body_type)
    show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?P) (Forall pp_unary_ty ?body)"
      using d_inner by simp
  qed
  show ?thesis
    using d_outer
    by (simp add: pp_fun_prime_def shift_by_def shift_ren_def
      shift_shift_eq_shift_by_2)
qed

subsection \<open>Goodman T2a: closure under \<open>G\<close>\<close>

lemma shift_pp_negation_operator[simp]:
  "shift pp_negation_operator = pp_negation_operator"
  by (simp add: shift_def pp_negation_operator_def)

lemma pp_negation_apply_beta:
  "compatible_step beta_contract
    (App pp_negation_operator A)
    (Neg A)"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App (Lam Prop (Neg (Var 0))) A)
      (subst0 A (Neg (Var 0)))"
    by (rule beta_contract.beta)
  show "beta_contract
    (App pp_negation_operator A)
    (Neg A)"
    using step
    by (simp add: pp_negation_operator_def subst0_def)
qed

theorem CEV_pp_negation_involution:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (pp_compose pp_negation_operator pp_negation_operator)
      pp_identity_operator"
proof -
  have op_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Eq (Prop \<rightarrow>\<^sub>o Prop)
        (pp_compose pp_negation_operator pp_negation_operator)
        pp_identity_operator"
  proof (rule CEV_unary_equivalence)
    show "\<Gamma> \<turnstile>
      pp_compose pp_negation_operator pp_negation_operator :
        Prop \<rightarrow>\<^sub>o Prop"
      using typed_pp_compose[
        OF typed_pp_negation_operator typed_pp_negation_operator]
      by (simp add: pp_unary_ty_def)
    show "\<Gamma> \<turnstile>
      pp_identity_operator : Prop \<rightarrow>\<^sub>o Prop"
      using typed_pp_identity_operator by (simp add: pp_unary_ty_def)
    let ?v = "Var 0"
    let ?NNapp =
      "App pp_negation_operator
        (App pp_negation_operator ?v)"
    let ?Napp = "Neg (App pp_negation_operator ?v)"
    let ?NN = "Neg (Neg ?v)"
    have v_type: "Prop # \<Gamma> \<turnstile> ?v : Prop"
      by (rule typed_var0)
    have neg_v_type:
      "Prop # \<Gamma> \<turnstile>
        App pp_negation_operator ?v : Prop"
      using typed_pp_negation_operator v_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have NNapp_type: "Prop # \<Gamma> \<turnstile> ?NNapp : Prop"
      using typed_pp_negation_operator neg_v_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have Napp_type: "Prop # \<Gamma> \<turnstile> ?Napp : Prop"
      using neg_v_type by (rule has_type.Neg)
    have NN_type: "Prop # \<Gamma> \<turnstile> ?NN : Prop"
      using v_type by (intro has_type.Neg)
    have comp_type:
      "Prop # \<Gamma> \<turnstile>
        App
          (pp_compose
            pp_negation_operator
            pp_negation_operator)
          ?v : Prop"
      using typed_pp_compose[
          OF typed_pp_negation_operator typed_pp_negation_operator]
        v_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have id_app_type:
      "Prop # \<Gamma> \<turnstile>
        App pp_identity_operator ?v : Prop"
      using typed_pp_identity_operator v_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have first:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App
          (pp_compose
            pp_negation_operator
            pp_negation_operator)
          ?v
        \<longleftrightarrow>\<^sub>o ?NNapp)"
      using typed_pp_negation_operator typed_pp_negation_operator v_type
      by (rule CEV_pp_compose_apply)
    have outer_step:
      "compatible_step beta_contract ?NNapp ?Napp"
      by (rule pp_negation_apply_beta)
    have second:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?NNapp \<longleftrightarrow>\<^sub>o ?Napp)"
      using NNapp_type Napp_type outer_step by (rule CEV_beta_step)
    have inner_step:
      "compatible_step beta_contract ?Napp ?NN"
      by (intro compatible_step.Neg_body pp_negation_apply_beta)
    have third:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?Napp \<longleftrightarrow>\<^sub>o ?NN)"
      using Napp_type NN_type inner_step by (rule CEV_beta_step)
    have double_neg:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?NN \<longleftrightarrow>\<^sub>o ?v)"
    proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
      have iff_type:
        "Prop # \<Gamma> \<turnstile> (?NN \<longleftrightarrow>\<^sub>o ?v) : Prop"
        using NN_type v_type
        by (intro has_type.Conj has_type.Imp)
      show "prop_tautology (Prop # \<Gamma>) (?NN \<longleftrightarrow>\<^sub>o ?v)"
        unfolding prop_tautology_def
        using iff_type by auto
    qed
    have id_beta:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App pp_identity_operator ?v \<longleftrightarrow>\<^sub>o ?v)"
      using v_type by (rule CEV_pp_identity_apply)
    have v_id:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (?v \<longleftrightarrow>\<^sub>o App pp_identity_operator ?v)"
      using id_app_type v_type id_beta by (rule CEV_biconditional_sym)
    have c1:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App
          (pp_compose
            pp_negation_operator
            pp_negation_operator)
          ?v
        \<longleftrightarrow>\<^sub>o ?Napp)"
      using comp_type NNapp_type Napp_type first second
      by (rule CEV_biconditional_trans)
    have c2:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App
          (pp_compose
            pp_negation_operator
            pp_negation_operator)
          ?v
        \<longleftrightarrow>\<^sub>o ?NN)"
      using comp_type Napp_type NN_type c1 third
      by (rule CEV_biconditional_trans)
    have c3:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App
          (pp_compose
            pp_negation_operator
            pp_negation_operator)
          ?v
        \<longleftrightarrow>\<^sub>o ?v)"
      using comp_type NN_type v_type c2 double_neg
      by (rule CEV_biconditional_trans)
    have final:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App
          (pp_compose
            pp_negation_operator
            pp_negation_operator)
          ?v
        \<longleftrightarrow>\<^sub>o
          App pp_identity_operator ?v)"
      using comp_type v_type id_app_type c3 v_id
      by (rule CEV_biconditional_trans)
    show "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App
        (shift
          (pp_compose
            pp_negation_operator
            pp_negation_operator))
        (Var 0)
      \<longleftrightarrow>\<^sub>o
        App (shift pp_identity_operator) (Var 0))"
      using final by simp
  qed
  show ?thesis
    using op_eq by (simp add: pp_unary_ty_def)
qed

lemma pp_T6_negation_purity_axiom:
  "pp_pure pp_unary_ty pp_negation_operator
    \<in> pp_T6_core_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def
  using pp_negation_operator_purity_axiom by blast

theorem pp_negation_operator_group_member:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_group_member pp_negation_operator"
proof -
  let ?N = "pp_negation_operator"
  let ?body =
    "Conj
      (pp_pure pp_unary_ty (Var 0))
      (Conj
        (Eq pp_unary_ty
          (pp_compose (shift ?N) (Var 0))
          pp_identity_operator)
        (Eq pp_unary_ty
          (pp_compose (Var 0) (shift ?N))
          pp_identity_operator))"
  have pure_N_core:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty ?N"
    using pp_T6_negation_purity_axiom
      typed_pp_pure[OF typed_pp_negation_operator]
    by (rule CEV_axiom_proves.Axiom)
  have pure_N:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty ?N"
    using pure_N_core core by (rule CEV_axiom_proves_mono)
  have involution:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq pp_unary_ty (pp_compose ?N ?N) pp_identity_operator"
    using CEV_pp_negation_involution
    by (rule CEV_axiom_proves.Base)
  have equations:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Conj
        (Eq pp_unary_ty (pp_compose ?N ?N) pp_identity_operator)
        (Eq pp_unary_ty (pp_compose ?N ?N) pp_identity_operator)"
    using involution involution by (rule CEV_axiom_conj_intro)
  have witness:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Conj
        (pp_pure pp_unary_ty ?N)
        (Conj
          (Eq pp_unary_ty (pp_compose ?N ?N) pp_identity_operator)
          (Eq pp_unary_ty (pp_compose ?N ?N) pp_identity_operator))"
    using pure_N equations by (rule CEV_axiom_conj_intro)
  have body_type: "pp_unary_ty # \<Gamma> \<turnstile> ?body : Prop"
  proof -
    have N_shift:
      "pp_unary_ty # \<Gamma> \<turnstile> shift ?N : pp_unary_ty"
      using typed_pp_negation_operator by (rule typed_shift_ctx)
    have v_type:
      "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
      by (rule typed_var0)
    have Nv_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_compose (shift ?N) (Var 0) : pp_unary_ty"
      using N_shift v_type by (rule typed_pp_compose)
    have vN_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_compose (Var 0) (shift ?N) : pp_unary_ty"
      using v_type N_shift by (rule typed_pp_compose)
    show ?thesis
      using typed_pp_pure[OF v_type] Nv_type vN_type
        typed_pp_identity_operator
      by (intro has_type.Conj has_type.Eq)
  qed
  have eg_raw:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (subst0 ?N ?body)
        (Exists pp_unary_ty ?body)"
    using body_type typed_pp_negation_operator
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.EG)
  have subst_left:
    "subst (case_nat ?N Var)
      (pp_compose ?N (Var 0)) =
      pp_compose ?N ?N"
    by (simp add: pp_compose_def subst_lift_shift
      pp_negation_operator_def)
  have subst_right:
    "subst (case_nat ?N Var)
      (pp_compose (Var 0) ?N) =
      pp_compose ?N ?N"
    by (simp add: pp_compose_def subst_lift_shift
      pp_negation_operator_def)
  have subst_id:
    "subst (case_nat ?N Var) pp_identity_operator =
      pp_identity_operator"
    by (simp add: pp_identity_operator_def)
  have eg:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Conj
          (pp_pure pp_unary_ty ?N)
          (Conj
            (Eq pp_unary_ty
              (pp_compose ?N ?N)
              pp_identity_operator)
            (Eq pp_unary_ty
              (pp_compose ?N ?N)
              pp_identity_operator)))
        (pp_reversible ?N)"
    using eg_raw
    unfolding pp_reversible_def
    by (intro CEV_axiom_proves.Base)
      (simp add: subst0_def pp_pure_def pp_Pure_def
        subst_left subst_right subst_id)
  have reversible:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_reversible ?N"
    using witness eg by (rule CEV_axiom_proves.MP)
  show ?thesis
    unfolding pp_group_member_def
    using pure_N reversible by (rule CEV_axiom_conj_intro)
qed

theorem CEV_fun_prime_under_reversible:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_reversible Z)
      (Imp
        (Conj
          (pp_fun_prime p)
          (pp_pure pp_unary_ty Z))
        (pp_fun_prime (App Z p)))"
proof -
  let ?p1 = "shift p"
  let ?Z1 = "shift Z"
  let ?I = "Var 0"
  let ?WB =
    "Conj
      (pp_pure pp_unary_ty ?I)
      (Conj
        (Eq pp_unary_ty
          (pp_compose ?Z1 ?I)
          pp_identity_operator)
        (Eq pp_unary_ty
          (pp_compose ?I ?Z1)
          pp_identity_operator))"
  let ?R =
    "Conj
      (pp_fun_prime p)
      (pp_pure pp_unary_ty Z)"
  let ?R1 =
    "Conj
      (pp_fun_prime ?p1)
      (pp_pure pp_unary_ty ?Z1)"
  let ?target = "pp_fun_prime (App Z p)"
  let ?target1 = "pp_fun_prime (App ?Z1 ?p1)"
  let ?EP =
    "pp_fun_prime_explicit_inverse_premises ?p1 ?Z1 ?I"
  have p1_type: "pp_unary_ty # \<Gamma> \<turnstile> ?p1 : Prop"
    using p_type by (rule typed_shift_ctx)
  have Z1_type: "pp_unary_ty # \<Gamma> \<turnstile> ?Z1 : pp_unary_ty"
    using Z_type by (rule typed_shift_ctx)
  have I_type: "pp_unary_ty # \<Gamma> \<turnstile> ?I : pp_unary_ty"
    by (rule typed_var0)
  have WB_type: "pp_unary_ty # \<Gamma> \<turnstile> ?WB : Prop"
  proof -
    have ZI_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_compose ?Z1 ?I : pp_unary_ty"
      using Z1_type I_type by (rule typed_pp_compose)
    have IZ_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_compose ?I ?Z1 : pp_unary_ty"
      using I_type Z1_type by (rule typed_pp_compose)
    have id_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_identity_operator : pp_unary_ty"
      by (rule typed_pp_identity_operator)
    show ?thesis
      using typed_pp_pure[OF I_type] ZI_type IZ_type id_type
      by (intro has_type.Conj has_type.Eq)
  qed
  have R1_type: "pp_unary_ty # \<Gamma> \<turnstile> ?R1 : Prop"
    using typed_pp_fun_prime[OF p1_type] typed_pp_pure[OF Z1_type]
    by (rule has_type.Conj)
  have target1_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?target1 : Prop"
  proof (rule typed_pp_fun_prime)
    show "pp_unary_ty # \<Gamma> \<turnstile> App ?Z1 ?p1 : Prop"
      using Z1_type p1_type unfolding pp_unary_ty_def
      by (rule has_type.App)
  qed
  have d_WB:
    "pp_unary_ty # \<Gamma> ; T ; insert ?R1 {?WB}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?WB"
    using WB_type by (intro CEV_axiom_from.Assumption) simp
  have d_WB_right:
    "pp_unary_ty # \<Gamma> ; T ; insert ?R1 {?WB}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Conj
          (Eq pp_unary_ty
            (pp_compose ?Z1 ?I)
            pp_identity_operator)
          (Eq pp_unary_ty
            (pp_compose ?I ?Z1)
            pp_identity_operator)"
    using d_WB by (rule CEV_axiom_from_conj_right)
  have d_right_inverse:
    "pp_unary_ty # \<Gamma> ; T ; insert ?R1 {?WB}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (pp_compose ?Z1 ?I)
          pp_identity_operator"
    using d_WB_right by (rule CEV_axiom_from_conj_left)
  have d_R1:
    "pp_unary_ty # \<Gamma> ; T ; insert ?R1 {?WB}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R1"
    using R1_type by (intro CEV_axiom_from.Assumption) simp
  have d_fun:
    "pp_unary_ty # \<Gamma> ; T ; insert ?R1 {?WB}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime ?p1"
    using d_R1 by (rule CEV_axiom_from_conj_left)
  have d_pure_Z:
    "pp_unary_ty # \<Gamma> ; T ; insert ?R1 {?WB}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty ?Z1"
    using d_R1 by (rule CEV_axiom_from_conj_right)
  have d_tail:
    "pp_unary_ty # \<Gamma> ; T ; insert ?R1 {?WB}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Conj
          (pp_pure pp_unary_ty ?Z1)
          (Eq pp_unary_ty
            (pp_compose ?Z1 ?I)
            pp_identity_operator)"
    using d_pure_Z d_right_inverse by (rule CEV_axiom_from_conj_intro)
  have d_EP:
    "pp_unary_ty # \<Gamma> ; T ; insert ?R1 {?WB}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?EP"
    unfolding pp_fun_prime_explicit_inverse_premises_def
    using d_fun d_tail by (rule CEV_axiom_from_conj_intro)
  have explicit_rule:
    "pp_unary_ty # \<Gamma> ; T ; insert ?R1 {?WB}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?EP ?target1"
    using CEV_fun_prime_under_explicit_inverse[
        OF core p1_type Z1_type I_type]
    by (rule CEV_axiom_from.Theorem)
  have d_target:
    "pp_unary_ty # \<Gamma> ; T ; insert ?R1 {?WB}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?target1"
    using d_EP explicit_rule by (rule CEV_axiom_from.MP)
  have d_R1_imp:
    "pp_unary_ty # \<Gamma> ; T ; {?WB}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?R1 ?target1"
    using R1_type d_target by (rule CEV_axiom_from_deduction)
  have d_WB_imp_local:
    "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?WB (Imp ?R1 ?target1)"
    using WB_type d_R1_imp by (rule CEV_axiom_from_deduction)
  have d_WB_imp:
    "pp_unary_ty # \<Gamma> ; T
      \<turnstile>\<^sub>CEV\<^sup>+ Imp ?WB (Imp ?R1 ?target1)"
    using d_WB_imp_local CEV_axiom_from_empty_iff by blast
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using typed_pp_fun_prime[OF p_type] typed_pp_pure[OF Z_type]
    by (rule has_type.Conj)
  have target_type: "\<Gamma> \<turnstile> ?target : Prop"
  proof (rule typed_pp_fun_prime)
    show "\<Gamma> \<turnstile> App Z p : Prop"
      using Z_type p_type unfolding pp_unary_ty_def
      by (rule has_type.App)
  qed
  have eliminated:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Exists pp_unary_ty ?WB) (Imp ?R ?target)"
  proof (rule CEV_axiom_proves.Inst)
    show "pp_unary_ty # \<Gamma> \<turnstile> ?WB : Prop"
      by (rule WB_type)
    show "\<Gamma> \<turnstile> Imp ?R ?target : Prop"
      using R_type target_type by (rule has_type.Imp)
    show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?WB (shift (Imp ?R ?target))"
      using d_WB_imp
      by simp
  qed
  show ?thesis
    using eliminated
    by (simp add: pp_reversible_def)
qed

theorem CEV_fun_prime_under_group_member:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_fun_prime p)
        (pp_group_member Z))
      (pp_fun_prime (App Z p))"
proof -
  let ?A =
    "Conj
      (pp_fun_prime p)
      (pp_group_member Z)"
  let ?R =
    "Conj
      (pp_fun_prime p)
      (pp_pure pp_unary_ty Z)"
  let ?target = "pp_fun_prime (App Z p)"
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using typed_pp_fun_prime[OF p_type]
      typed_pp_group_member[OF Z_type]
    by (rule has_type.Conj)
  have d_A:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    using A_type by (intro CEV_axiom_from.Assumption) simp
  have d_fun:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
    using d_A by (rule CEV_axiom_from_conj_left)
  have d_group:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member Z"
    using d_A by (rule CEV_axiom_from_conj_right)
  have d_pure:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty Z"
    using d_group
    unfolding pp_group_member_def
    by (rule CEV_axiom_from_conj_left)
  have d_rev:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_reversible Z"
    using d_group
    unfolding pp_group_member_def
    by (rule CEV_axiom_from_conj_right)
  have d_R:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
    using d_fun d_pure by (rule CEV_axiom_from_conj_intro)
  have rule:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_reversible Z) (Imp ?R ?target)"
    using CEV_fun_prime_under_reversible[OF core p_type Z_type]
    by (rule CEV_axiom_from.Theorem)
  have step:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?R ?target"
    using d_rev rule by (rule CEV_axiom_from.MP)
  have d_target:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?target"
    using d_R step by (rule CEV_axiom_from.MP)
  show ?thesis
    using A_type d_target by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_fun_prime_under_negation_operator:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime p)
      (pp_fun_prime (App pp_negation_operator p))"
proof -
  let ?A = "pp_fun_prime p"
  let ?target = "pp_fun_prime (App pp_negation_operator p)"
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using p_type by (rule typed_pp_fun_prime)
  have d_A:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    using A_type by (intro CEV_axiom_from.Assumption) simp
  have group:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_group_member pp_negation_operator"
    using pp_negation_operator_group_member[OF core]
    by (rule CEV_axiom_from.Theorem)
  have pair:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj ?A (pp_group_member pp_negation_operator)"
    using d_A group by (rule CEV_axiom_from_conj_intro)
  have closure:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj ?A (pp_group_member pp_negation_operator))
        ?target"
    using CEV_fun_prime_under_group_member[
        OF core p_type typed_pp_negation_operator]
    by (rule CEV_axiom_from.Theorem)
  have d_target:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?target"
    using pair closure by (rule CEV_axiom_from.MP)
  show ?thesis
    using A_type d_target by (rule CEV_axiom_from_singleton_imp)
qed

definition pp_fun_prime_classifier :: oterm where
  "pp_fun_prime_classifier =
    Lam Prop (pp_fun_prime (Var 0))"

lemma typed_pp_fun_prime_classifier:
  "\<Gamma> \<turnstile> pp_fun_prime_classifier : Prop \<rightarrow>\<^sub>o Prop"
  unfolding pp_fun_prime_classifier_def
proof (rule has_type.Lam)
  have "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  then show "Prop # \<Gamma> \<turnstile> pp_fun_prime (Var 0) : Prop"
    by (rule typed_pp_fun_prime)
qed

lemma pp_fun_prime_classifier_beta:
  "compatible_step beta_contract
    (App pp_fun_prime_classifier A)
    (pp_fun_prime A)"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam Prop (pp_fun_prime (Var 0)))
        A)
      (subst0 A (pp_fun_prime (Var 0)))"
    by (rule beta_contract.beta)
  show "beta_contract
    (App pp_fun_prime_classifier A)
    (pp_fun_prime A)"
  proof -
    have ren:
      "rename Suc (rename Suc A) =
        rename (shift_ren 2 0) A"
      using shift_shift_eq_shift_by_2[of A]
      unfolding shift_def shift_by_def .
    show ?thesis
    using step
      by (simp add: pp_fun_prime_classifier_def pp_fun_prime_def
        pp_pure_def pp_Pure_def subst0_def shift_by_def shift_ren_def ren)
  qed
qed

lemma CEV_pp_fun_prime_classifier_beta:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    (App pp_fun_prime_classifier A \<longleftrightarrow>\<^sub>o
      pp_fun_prime A)"
proof -
  have left_type:
    "\<Gamma> \<turnstile> App pp_fun_prime_classifier A : Prop"
    using typed_pp_fun_prime_classifier A_type by (rule has_type.App)
  have right_type: "\<Gamma> \<turnstile> pp_fun_prime A : Prop"
    using A_type by (rule typed_pp_fun_prime)
  show ?thesis
    using left_type right_type pp_fun_prime_classifier_beta
    by (rule CEV_beta_step)
qed

lemma CEV_axiom_fun_prime_eq_transport:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Eq Prop A B)
      (Imp
        (pp_fun_prime A)
        (pp_fun_prime B))"
proof -
  let ?E = "Eq Prop A B"
  let ?FA = "pp_fun_prime A"
  let ?FB = "pp_fun_prime B"
  let ?CA = "App pp_fun_prime_classifier A"
  let ?CB = "App pp_fun_prime_classifier B"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using A_type B_type by (rule has_type.Eq)
  have FA_type: "\<Gamma> \<turnstile> ?FA : Prop"
    using A_type by (rule typed_pp_fun_prime)
  have CA_type: "\<Gamma> \<turnstile> ?CA : Prop"
    using typed_pp_fun_prime_classifier A_type by (rule has_type.App)
  have CB_type: "\<Gamma> \<turnstile> ?CB : Prop"
    using typed_pp_fun_prime_classifier B_type by (rule has_type.App)
  have FB_type: "\<Gamma> \<turnstile> ?FB : Prop"
    using B_type by (rule typed_pp_fun_prime)
  have d_E:
    "\<Gamma> ; T ; insert ?FA {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using E_type by (intro CEV_axiom_from.Assumption) simp
  have d_FA:
    "\<Gamma> ; T ; insert ?FA {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?FA"
    using FA_type by (intro CEV_axiom_from.Assumption) simp
  have FA_CA_base: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?FA ?CA"
    using CA_type FA_type CEV_pp_fun_prime_classifier_beta[OF A_type]
    by (rule CEV_beta_right_imp)
  have FA_CA:
    "\<Gamma> ; T ; insert ?FA {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?FA ?CA"
    using FA_CA_base
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_CA:
    "\<Gamma> ; T ; insert ?FA {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?CA"
    using d_FA FA_CA by (rule CEV_axiom_from.MP)
  have ll_base: "\<Gamma> \<turnstile>\<^sub>CEV
    Imp ?E (Imp ?CA ?CB)"
    using A_type B_type typed_pp_fun_prime_classifier
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have ll:
    "\<Gamma> ; T ; insert ?FA {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?E (Imp ?CA ?CB)"
    using ll_base
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have CA_CB:
    "\<Gamma> ; T ; insert ?FA {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?CA ?CB"
    using d_E ll by (rule CEV_axiom_from.MP)
  have d_CB:
    "\<Gamma> ; T ; insert ?FA {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?CB"
    using d_CA CA_CB by (rule CEV_axiom_from.MP)
  have CB_FB_base: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?CB ?FB"
    using CB_type FB_type CEV_pp_fun_prime_classifier_beta[OF B_type]
    by (rule CEV_beta_left_imp)
  have CB_FB:
    "\<Gamma> ; T ; insert ?FA {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?CB ?FB"
    using CB_FB_base
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_FB:
    "\<Gamma> ; T ; insert ?FA {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?FB"
    using d_CB CB_FB by (rule CEV_axiom_from.MP)
  have d_FA_imp:
    "\<Gamma> ; T ; {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?FA ?FB"
    using FA_type d_FB by (rule CEV_axiom_from_deduction)
  have d_E_imp_local:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?E (Imp ?FA ?FB)"
    using E_type d_FA_imp by (rule CEV_axiom_from_deduction)
  show ?thesis
    using d_E_imp_local CEV_axiom_from_empty_iff by blast
qed

lemma CEV_pp_negation_apply_eq:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop
      (App pp_negation_operator p)
      (Neg p)"
proof -
  have left_type:
    "\<Gamma> \<turnstile> App pp_negation_operator p : Prop"
    using typed_pp_negation_operator p_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have right_type: "\<Gamma> \<turnstile> Neg p : Prop"
    using p_type by (rule has_type.Neg)
  have iff: "\<Gamma> \<turnstile>\<^sub>CEV
    (App pp_negation_operator p \<longleftrightarrow>\<^sub>o Neg p)"
    using left_type right_type pp_negation_apply_beta
    by (rule CEV_beta_step)
  show ?thesis
    using left_type right_type iff by (rule CEV_zeroary_equivalence)
qed

theorem CEV_fun_prime_under_negation:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime p)
      (pp_fun_prime (Neg p))"
proof -
  let ?A = "pp_fun_prime p"
  let ?NA = "App pp_negation_operator p"
  let ?target_op = "pp_fun_prime ?NA"
  let ?target = "pp_fun_prime (Neg p)"
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using p_type by (rule typed_pp_fun_prime)
  have NA_type: "\<Gamma> \<turnstile> ?NA : Prop"
    using typed_pp_negation_operator p_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have neg_type: "\<Gamma> \<turnstile> Neg p : Prop"
    using p_type by (rule has_type.Neg)
  have d_A:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    using A_type by (intro CEV_axiom_from.Assumption) simp
  have op_rule:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?A ?target_op"
    using CEV_fun_prime_under_negation_operator[OF core p_type]
    by (rule CEV_axiom_from.Theorem)
  have d_target_op:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?target_op"
    using d_A op_rule by (rule CEV_axiom_from.MP)
  have eq:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?NA (Neg p)"
    using CEV_pp_negation_apply_eq[OF p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have transport:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Eq Prop ?NA (Neg p))
        (Imp ?target_op ?target)"
    using CEV_axiom_fun_prime_eq_transport[
        OF NA_type neg_type, where T = T]
    by (rule CEV_axiom_from.Theorem)
  have step:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?target_op ?target"
    using eq transport by (rule CEV_axiom_from.MP)
  have d_target:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?target"
    using d_target_op step by (rule CEV_axiom_from.MP)
  show ?thesis
    using A_type d_target by (rule CEV_axiom_from_singleton_imp)
qed

end
