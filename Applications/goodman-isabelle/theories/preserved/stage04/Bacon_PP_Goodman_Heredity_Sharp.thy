theory Bacon_PP_Goodman_Heredity_Sharp
  imports 
    "Goodman_Legacy_04.Bacon_PP_Goodman_Heredity_Exhaustion"
begin

section \<open>Sharp dependency analysis: what T3 really needs\<close>

subsection \<open>The modal core alone: only \<open>\<diamond>(Y = Z)\<close> is reachable\<close>

text \<open>
  From necessitated QSS and Persistence alone --- exactly the two principles
  Goodman flags for T3 --- the derivation reaches \<open>\<diamond>(Y = Z)\<close> and
  stops there.  No purity schema, no application closure, no PP is used.
\<close>

theorem CEV_T3_modal_core:
  assumes qss: "pp_QSS \<in> T"
    and pers: "pp_persistence pp_unary_ty \<in> T"
    and x_type: "\<Gamma> \<turnstile> x : Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (\<diamond>\<^sub>o (pp_fun Prop x))
      (Imp
        (Conj (pp_pure pp_unary_ty Y) (pp_pure pp_unary_ty Z))
        (Imp
          (Eq Prop (App Y x) (App Z x))
          (\<diamond>\<^sub>o (Eq pp_unary_ty Y Z))))"
proof -
  let ?PY = "pp_pure pp_unary_ty Y"
  let ?PZ = "pp_pure pp_unary_ty Z"
  let ?PC = "Conj ?PY ?PZ"
  let ?EA = "Eq Prop (App Y x) (App Z x)"
  let ?D = "Eq pp_unary_ty Y Z"
  let ?B = "pp_fun Prop x"
  let ?Dia = "\<diamond>\<^sub>o ?B"
  let ?A = "Conj ?PY (Conj ?PZ ?EA)"
  let ?S = "insert ?EA (insert ?PC {?Dia})"
  have PY_type: "\<Gamma> \<turnstile> ?PY : Prop"
    using Y_type by (rule typed_pp_pure)
  have PZ_type: "\<Gamma> \<turnstile> ?PZ : Prop"
    using Z_type by (rule typed_pp_pure)
  have PC_type: "\<Gamma> \<turnstile> ?PC : Prop"
    using PY_type PZ_type by (intro has_type.Conj has_type.Imp)
  have Yx_type: "\<Gamma> \<turnstile> App Y x : Prop"
    using Y_type[unfolded pp_unary_ty_def] x_type by (rule has_type.App)
  have Zx_type: "\<Gamma> \<turnstile> App Z x : Prop"
    using Z_type[unfolded pp_unary_ty_def] x_type by (rule has_type.App)
  have EA_type: "\<Gamma> \<turnstile> ?EA : Prop"
    using Yx_type Zx_type by (rule has_type.Eq)
  have D_type: "\<Gamma> \<turnstile> ?D : Prop"
    using Y_type Z_type by (rule has_type.Eq)
  have B_type: "\<Gamma> \<turnstile> ?B : Prop"
    using x_type by (rule typed_pp_fun)
  have Dia_type: "\<Gamma> \<turnstile> ?Dia : Prop"
    using B_type by (rule typed_ObjDiamond)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using PY_type PZ_type EA_type by (intro has_type.Conj has_type.Imp)
  have d_Dia: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Dia"
    using Dia_type by (intro CEV_axiom_from.Assumption) simp
  have d_PC: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PC"
    using PC_type by (intro CEV_axiom_from.Assumption) simp
  have d_EA: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?EA"
    using EA_type by (intro CEV_axiom_from.Assumption) simp
  have d_PY: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PY"
    using d_PC by (rule CEV_axiom_from_conj_left)
  have d_PZ: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PZ"
    using d_PC by (rule CEV_axiom_from_conj_right)
  have d_boxPY: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o ?PY"
    using d_PY
      CEV_axiom_from.Theorem[
        OF CEV_axiom_persistence_instance[OF pers Y_type]]
    by (rule CEV_axiom_from.MP)
  have d_boxPZ: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o ?PZ"
    using d_PZ
      CEV_axiom_from.Theorem[
        OF CEV_axiom_persistence_instance[OF pers Z_type]]
    by (rule CEV_axiom_from.MP)
  have d_boxEA: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o ?EA"
    using Yx_type Zx_type d_EA by (rule CEV_axiom_from_box_of_eq)
  have d_boxPZEA:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o (Conj ?PZ ?EA)"
    using PZ_type EA_type d_boxPZ d_boxEA by (rule CEV_axiom_from_box_conj)
  have d_boxA: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o ?A"
    using PY_type has_type.Conj[OF PZ_type EA_type] d_boxPY d_boxPZEA
    by (rule CEV_axiom_from_box_conj)
  have qss_inst: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ qss_body3 Y Z x"
    using qss Y_type Z_type x_type by (rule CEV_axiom_QSS_instance)
  have qss_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj ?PY (Conj ?PZ ?B)) (Imp ?EA ?D)"
    using qss_inst unfolding qss_body3_def .
  have rearrange:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp (Conj ?PY (Conj ?PZ ?B)) (Imp ?EA ?D))
        (Imp ?A (Imp ?B ?D))"
  proof (rule CEV_prop_tautology)
    have type:
      "\<Gamma> \<turnstile>
        Imp (Imp (Conj ?PY (Conj ?PZ ?B)) (Imp ?EA ?D))
          (Imp ?A (Imp ?B ?D)) : Prop"
      using PY_type PZ_type EA_type D_type B_type A_type by auto
    moreover have
      "\<forall>v. prop_eval v
        (Imp (Imp (Conj ?PY (Conj ?PZ ?B)) (Imp ?EA ?D))
          (Imp ?A (Imp ?B ?D)))"
      apply (simp only: prop_eval.simps) by blast
    ultimately show
      "prop_tautology \<Gamma>
        (Imp (Imp (Conj ?PY (Conj ?PZ ?B)) (Imp ?EA ?D))
          (Imp ?A (Imp ?B ?D)))"
      unfolding prop_tautology_def by blast
  qed
  have imp_thm: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?A (Imp ?B ?D)"
    using qss_raw CEV_axiom_proves.Base[OF rearrange]
    by (rule CEV_axiom_proves.MP)
  have d_diaD: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o ?D"
    using A_type B_type D_type imp_thm d_boxA d_Dia
    by (rule CEV_axiom_from_box_diamond_mp)
  have step1:
    "\<Gamma> ; T ; insert ?PC {?Dia}
       \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?EA (\<diamond>\<^sub>o ?D)"
    using EA_type d_diaD by (rule CEV_axiom_from_deduction)
  have step2:
    "\<Gamma> ; T ; {?Dia} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?PC (Imp ?EA (\<diamond>\<^sub>o ?D))"
    using PC_type step1 by (rule CEV_axiom_from_deduction)
  show ?thesis
    using Dia_type step2 by (rule CEV_axiom_from_singleton_imp)
qed

subsection \<open>The minimal extra principle: rigidity of pure identities\<close>

definition pp_pure_eq_rigidity :: "otype \<Rightarrow> oterm" where
  "pp_pure_eq_rigidity \<sigma> =
    Forall \<sigma>
      (Forall \<sigma>
        (Imp
          (Conj (pp_pure \<sigma> (Var 1)) (pp_pure \<sigma> (Var 0)))
          (Imp
            (\<diamond>\<^sub>o (Eq \<sigma> (Var 1) (Var 0)))
            (Eq \<sigma> (Var 1) (Var 0)))))"

lemma typed_pp_pure_eq_rigidity:
  "\<Gamma> \<turnstile> pp_pure_eq_rigidity \<sigma> : Prop"
  by (rule infer_type_sound)
    (simp add: pp_pure_eq_rigidity_def pp_pure_def pp_Pure_def
      ObjDiamond_def ObjBox_def ObjTrue_def lookup_def)

definition rigid_body2 :: "otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "rigid_body2 \<sigma> X Y =
    Imp
      (Conj (pp_pure \<sigma> X) (pp_pure \<sigma> Y))
      (Imp (\<diamond>\<^sub>o (Eq \<sigma> X Y)) (Eq \<sigma> X Y))"

lemma pp_pure_eq_rigidity_as_body:
  "pp_pure_eq_rigidity \<sigma> =
    Forall \<sigma> (Forall \<sigma> (rigid_body2 \<sigma> (Var 1) (Var 0)))"
  by (simp add: pp_pure_eq_rigidity_def rigid_body2_def)

lemma subst_rigid_body2:
  "subst \<theta> (rigid_body2 \<sigma> X Y) =
    rigid_body2 \<sigma> (subst \<theta> X) (subst \<theta> Y)"
  by (simp add: rigid_body2_def pp_pure_def pp_Pure_def
    ObjDiamond_def ObjBox_def ObjTrue_def)

lemma CEV_axiom_rigidity_instance:
  assumes rig: "pp_pure_eq_rigidity \<sigma> \<in> T"
    and X_type: "\<Gamma> \<turnstile> X : \<sigma>"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ rigid_body2 \<sigma> X Y"
proof -
  have d0: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure_eq_rigidity \<sigma>"
    using rig typed_pp_pure_eq_rigidity by (rule CEV_axiom_proves.Axiom)
  have t0: "\<Gamma> \<turnstile>
    Forall \<sigma> (Forall \<sigma> (rigid_body2 \<sigma> (Var 1) (Var 0))) : Prop"
    using typed_pp_pure_eq_rigidity unfolding pp_pure_eq_rigidity_as_body .
  have d1raw: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    subst0 X (Forall \<sigma> (rigid_body2 \<sigma> (Var 1) (Var 0)))"
    using t0 X_type d0[unfolded pp_pure_eq_rigidity_as_body]
    by (rule CEV_axiom_UI_typed)
  have e1:
    "subst0 X (Forall \<sigma> (rigid_body2 \<sigma> (Var 1) (Var 0))) =
     Forall \<sigma> (rigid_body2 \<sigma> (shift X) (Var 0))"
    by (simp add: subst0_def subst_rigid_body2 rigid_body2_def shift_def
      pp_pure_def pp_Pure_def ObjDiamond_def ObjBox_def ObjTrue_def
      eval_nat_numeral)
  have d1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Forall \<sigma> (rigid_body2 \<sigma> (shift X) (Var 0))"
    using d1raw unfolding e1 .
  have t1: "\<Gamma> \<turnstile>
    Forall \<sigma> (rigid_body2 \<sigma> (shift X) (Var 0)) : Prop"
    using CEV_axiom_proves_formula[OF d1] .
  have d2raw: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    subst0 Y (rigid_body2 \<sigma> (shift X) (Var 0))"
    using t1 Y_type d1 by (rule CEV_axiom_UI_typed)
  have e2:
    "subst0 Y (rigid_body2 \<sigma> (shift X) (Var 0)) =
     rigid_body2 \<sigma> X Y"
    by (simp add: subst0_def subst_rigid_body2 rigid_body2_def shift_def
      pp_pure_def pp_Pure_def ObjDiamond_def ObjBox_def ObjTrue_def
      subst0_shift[of Y X, unfolded subst0_def shift_def])
  show ?thesis
    using d2raw unfolding e2 .
qed

definition pp_T3_rigid_axioms :: "oterm set" where
  "pp_T3_rigid_axioms =
    {pp_persistence pp_unary_ty, pp_QSS,
     pp_pure_eq_rigidity pp_unary_ty}"

theorem CEV_T3_parameter_rigid:
  assumes ax: "pp_T3_rigid_axioms \<subseteq> T"
    and x_type: "\<Gamma> \<turnstile> x : Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (\<diamond>\<^sub>o (pp_fun Prop x))
      (Imp
        (Conj (pp_pure pp_unary_ty Y) (pp_pure pp_unary_ty Z))
        (Imp
          (Eq Prop (App Y x) (App Z x))
          (Eq pp_unary_ty Y Z)))"
proof -
  have qss: "pp_QSS \<in> T"
    using ax unfolding pp_T3_rigid_axioms_def by blast
  have pers: "pp_persistence pp_unary_ty \<in> T"
    using ax unfolding pp_T3_rigid_axioms_def by blast
  have rig: "pp_pure_eq_rigidity pp_unary_ty \<in> T"
    using ax unfolding pp_T3_rigid_axioms_def by blast
  let ?PY = "pp_pure pp_unary_ty Y"
  let ?PZ = "pp_pure pp_unary_ty Z"
  let ?PC = "Conj ?PY ?PZ"
  let ?EA = "Eq Prop (App Y x) (App Z x)"
  let ?D = "Eq pp_unary_ty Y Z"
  let ?B = "pp_fun Prop x"
  let ?Dia = "\<diamond>\<^sub>o ?B"
  let ?S = "insert ?EA (insert ?PC {?Dia})"
  have PY_type: "\<Gamma> \<turnstile> ?PY : Prop"
    using Y_type by (rule typed_pp_pure)
  have PZ_type: "\<Gamma> \<turnstile> ?PZ : Prop"
    using Z_type by (rule typed_pp_pure)
  have PC_type: "\<Gamma> \<turnstile> ?PC : Prop"
    using PY_type PZ_type by (intro has_type.Conj has_type.Imp)
  have Yx_type: "\<Gamma> \<turnstile> App Y x : Prop"
    using Y_type[unfolded pp_unary_ty_def] x_type by (rule has_type.App)
  have Zx_type: "\<Gamma> \<turnstile> App Z x : Prop"
    using Z_type[unfolded pp_unary_ty_def] x_type by (rule has_type.App)
  have EA_type: "\<Gamma> \<turnstile> ?EA : Prop"
    using Yx_type Zx_type by (rule has_type.Eq)
  have D_type: "\<Gamma> \<turnstile> ?D : Prop"
    using Y_type Z_type by (rule has_type.Eq)
  have B_type: "\<Gamma> \<turnstile> ?B : Prop"
    using x_type by (rule typed_pp_fun)
  have Dia_type: "\<Gamma> \<turnstile> ?Dia : Prop"
    using B_type by (rule typed_ObjDiamond)
  have core:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?Dia (Imp ?PC (Imp ?EA (\<diamond>\<^sub>o ?D)))"
    using CEV_T3_modal_core[OF qss pers x_type Y_type Z_type] .
  have d_Dia: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Dia"
    using Dia_type by (intro CEV_axiom_from.Assumption) simp
  have d_PC: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PC"
    using PC_type by (intro CEV_axiom_from.Assumption) simp
  have d_EA: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?EA"
    using EA_type by (intro CEV_axiom_from.Assumption) simp
  have s1: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Imp ?PC (Imp ?EA (\<diamond>\<^sub>o ?D))"
    using d_Dia CEV_axiom_from.Theorem[OF core] by (rule CEV_axiom_from.MP)
  have s2: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Imp ?EA (\<diamond>\<^sub>o ?D)"
    using d_PC s1 by (rule CEV_axiom_from.MP)
  have d_diaD: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o ?D"
    using d_EA s2 by (rule CEV_axiom_from.MP)
  have d_rig: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    rigid_body2 pp_unary_ty Y Z"
    using CEV_axiom_rigidity_instance[OF rig Y_type Z_type]
    by (rule CEV_axiom_from.Theorem)
  have d_rig': "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Imp ?PC (Imp (\<diamond>\<^sub>o ?D) ?D)"
    using d_rig unfolding rigid_body2_def .
  have d_step: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Imp (\<diamond>\<^sub>o ?D) ?D"
    using d_PC d_rig' by (rule CEV_axiom_from.MP)
  have d_D: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?D"
    using d_diaD d_step by (rule CEV_axiom_from.MP)
  have step1:
    "\<Gamma> ; T ; insert ?PC {?Dia}
       \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?EA ?D"
    using EA_type d_D by (rule CEV_axiom_from_deduction)
  have step2:
    "\<Gamma> ; T ; {?Dia} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?PC (Imp ?EA ?D)"
    using PC_type step1 by (rule CEV_axiom_from_deduction)
  show ?thesis
    using Dia_type step2 by (rule CEV_axiom_from_singleton_imp)
qed

text \<open>
  The binder closure is literally the one used for the Exhaustion route, so
  we factor it out as a locale-free lemma over an arbitrary parameter
  theorem.
\<close>

lemma CEV_T3_close_binders:
  assumes param:
    "\<And>\<Gamma> x Y Z.
      \<Gamma> \<turnstile> x : Prop \<Longrightarrow>
      \<Gamma> \<turnstile> Y : pp_unary_ty \<Longrightarrow>
      \<Gamma> \<turnstile> Z : pp_unary_ty \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (\<diamond>\<^sub>o (pp_fun Prop x))
          (Imp
            (Conj (pp_pure pp_unary_ty Y) (pp_pure pp_unary_ty Z))
            (Imp
              (Eq Prop (App Y x) (App Z x))
              (Eq pp_unary_ty Y Z)))"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_T3_heredity"
proof -
  let ?U = pp_unary_ty
  let ?G3 = "[?U, ?U, Prop]"
  let ?BODY =
    "Imp
      (Conj (pp_pure ?U (Var 1)) (pp_pure ?U (Var 0)))
      (Imp
        (Eq Prop (App (Var 1) (Var 2)) (App (Var 0) (Var 2)))
        (Eq ?U (Var 1) (Var 0)))"
  have x2_type: "?G3 \<turnstile> Var 2 : Prop"
    by (rule has_type.Var) (simp add: lookup_def)
  have Y1_type: "?G3 \<turnstile> Var 1 : ?U"
    by (rule has_type.Var) (simp add: lookup_def)
  have Z0_type: "?G3 \<turnstile> Var 0 : ?U"
    by (rule has_type.Var) (simp add: lookup_def)
  have core:
    "?G3 ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<diamond>\<^sub>o (pp_fun Prop (Var 2))) ?BODY"
    using param[OF x2_type Y1_type Z0_type] .
  have BODY_type: "?G3 \<turnstile> ?BODY : Prop"
    using CEV_axiom_proves_formula[OF core] by (auto elim: has_type.cases)
  have fp_unfold:
    "pp_fun_prime (Var 0) = Forall ?U (Forall ?U ?BODY)"
    by (simp add: pp_fun_prime_def shift_by_def shift_ren_def)
  have gen1:
    "[?U, Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<diamond>\<^sub>o (pp_fun Prop (Var 1))) (Forall ?U ?BODY)"
  proof (rule CEV_axiom_proves.Gen)
    show "[?U, Prop] \<turnstile> \<diamond>\<^sub>o (pp_fun Prop (Var 1)) : Prop"
      by (intro typed_ObjDiamond typed_pp_fun has_type.Var)
        (simp add: lookup_def)
    show "?U # [?U, Prop] \<turnstile> ?BODY : Prop"
      using BODY_type by simp
    show "?U # [?U, Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (\<diamond>\<^sub>o (pp_fun Prop (Var 1)))) ?BODY"
      using core
      by (simp add: shift_def pp_fun_def pp_Fun_def
        ObjDiamond_def ObjBox_def ObjTrue_def eval_nat_numeral)
  qed
  have gen2:
    "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<diamond>\<^sub>o (pp_fun Prop (Var 0))) (Forall ?U (Forall ?U ?BODY))"
  proof (rule CEV_axiom_proves.Gen)
    show "[Prop] \<turnstile> \<diamond>\<^sub>o (pp_fun Prop (Var 0)) : Prop"
      by (intro typed_ObjDiamond typed_pp_fun has_type.Var)
        (simp add: lookup_def)
    show "?U # [Prop] \<turnstile> Forall ?U ?BODY : Prop"
      using BODY_type by (intro has_type.Forall) simp
    show "?U # [Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (\<diamond>\<^sub>o (pp_fun Prop (Var 0)))) (Forall ?U ?BODY)"
      using gen1
      by (simp add: shift_def pp_fun_def pp_Fun_def
        ObjDiamond_def ObjBox_def ObjTrue_def eval_nat_numeral)
  qed
  have inner:
    "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<diamond>\<^sub>o (pp_fun Prop (Var 0))) (pp_fun_prime (Var 0))"
    using gen2 unfolding fp_unfold .
  have inner_type:
    "[Prop] \<turnstile>
      Imp (\<diamond>\<^sub>o (pp_fun Prop (Var 0))) (pp_fun_prime (Var 0)) : Prop"
    using CEV_axiom_proves_formula[OF inner] .
  have guarded:
    "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue
        (Imp (\<diamond>\<^sub>o (pp_fun Prop (Var 0))) (pp_fun_prime (Var 0)))"
    using typed_ObjTrue inner by (rule CEV_axiom_imp_of_right)
  have gen3:
    "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ObjTrue pp_T3_heredity"
    unfolding pp_T3_heredity_def
  proof (rule CEV_axiom_proves.Gen)
    show "[] \<turnstile> ObjTrue : Prop" by (rule typed_ObjTrue)
    show "Prop # [] \<turnstile>
      Imp (\<diamond>\<^sub>o (pp_fun Prop (Var 0))) (pp_fun_prime (Var 0)) : Prop"
      using inner_type by simp
    show "Prop # [] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ObjTrue)
        (Imp (\<diamond>\<^sub>o (pp_fun Prop (Var 0))) (pp_fun_prime (Var 0)))"
      using guarded by (simp add: ObjTrue_def shift_def)
  qed
  have d_true: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjTrue"
    by (rule CEV_axiom_proves_ObjTrue)
  show ?thesis
    using d_true gen3 by (rule CEV_axiom_proves.MP)
qed

theorem CEV_Goodman_T3_heredity_rigid:
  assumes ax: "pp_T3_rigid_axioms \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_T3_heredity"
  by (rule CEV_T3_close_binders) (rule CEV_T3_parameter_rigid[OF ax])

corollary CEV_Goodman_T3_heredity_over_T3_axioms_plus_rigidity:
  "[] ; insert (pp_pure_eq_rigidity pp_unary_ty) pp_T3_axioms
     \<turnstile>\<^sub>CEV\<^sup>+ pp_T3_heredity"
proof (rule CEV_Goodman_T3_heredity_rigid)
  show "pp_T3_rigid_axioms
      \<subseteq> insert (pp_pure_eq_rigidity pp_unary_ty) pp_T3_axioms"
    unfolding pp_T3_rigid_axioms_def pp_T3_axioms_def
      pp_persistence_schema_def by blast
qed

subsection \<open>Unrestricted rigidity of identity is refutable\<close>

text \<open>
  The restriction to \<^emph>\<open>pure\<close> arguments in
  \<open>pp_pure_eq_rigidity\<close> is not cosmetic.  Over the T6 core together
  with a \<open>fun\<acute>\<close> proposition \<open>r\<close>, the object theory already proves
  \<open>\<diamond>(r = \<top>)\<close> (Goodman T2c/T2d) and \<open>\<not>(\<top> = r)\<close>
  (Goodman T2f).  Hence the unrestricted schema
  \<open>\<diamond>(M = N) \<longrightarrow> M = N\<close> is inconsistent with the very setting in
  which T3 is asserted.
\<close>

definition pp_unrestricted_rigidity :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_unrestricted_rigidity M N =
    Imp (\<diamond>\<^sub>o (Eq Prop M N)) (Eq Prop M N)"

theorem CEV_unrestricted_rigidity_refuted:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r)
      (Imp (pp_unrestricted_rigidity r ObjTrue) ObjFalse)"
proof -
  let ?F = "pp_fun_prime r"
  let ?E = "Eq Prop r ObjTrue"
  let ?R = "Imp (\<diamond>\<^sub>o ?E) ?E"
  let ?S = "insert ?R {?F}"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using E_type by (intro has_type.Imp typed_ObjDiamond)
  have d_F: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_R: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
    using R_type by (intro CEV_axiom_from.Assumption) simp
  \<comment> \<open>T2c: a fun-prime proposition is possibly identical to any pure one\<close>
  have t2c:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F (Imp (pp_pure Prop ObjTrue) (\<diamond>\<^sub>o ?E))"
    using CEV_Goodman_T2c_parameter[
      OF pp_T2_min_axioms_into_T6_extension[OF core]
        r_type typed_ObjTrue]
    by (rule CEV_axiom_from.Theorem)
  have d_pure_true:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop ObjTrue"
    using pp_ObjTrue_pure_in_core_extension[OF core]
    by (rule CEV_axiom_from.Theorem)
  have d_dia:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o ?E"
    using d_pure_true
      CEV_axiom_from.MP[OF d_F t2c]
    by (rule CEV_axiom_from.MP)
  have d_E: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using d_dia d_R by (rule CEV_axiom_from.MP)
  \<comment> \<open>T2f: the six propositions are pairwise distinct, so \<open>\<top> \<noteq> r\<close>\<close>
  have d_six:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_T2f_six_distinct r"
    using d_F
      CEV_axiom_from.Theorem[OF CEV_Goodman_T2f[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have d_ne:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop ObjTrue r)"
    using d_six unfolding pp_T2f_six_distinct_def
    by (metis CEV_axiom_from_conj_left CEV_axiom_from_conj_right)
  have d_sym:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ObjTrue r"
    using r_type typed_ObjTrue d_E by (rule CEV_axiom_from_eq_sym)
  have d_false: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_sym d_ne
    by (rule CEV_axiom_from_contradiction)
  have step1:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?R ObjFalse"
    using R_type d_false by (rule CEV_axiom_from_deduction)
  show ?thesis
    unfolding pp_unrestricted_rigidity_def
    using F_type step1 by (rule CEV_axiom_from_singleton_imp)
qed

end
