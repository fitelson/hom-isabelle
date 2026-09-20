theory Bacon_PP_Goodman_Heredity_Exhaustion
  imports 
    "Goodman_Legacy_03.Bacon_PP_Goodman_Heredity_Core"
begin

section \<open>Goodman T3 with the required rigidity supplied by Exhaustion\<close>

definition pp_T3_min_axioms :: "oterm set" where
  "pp_T3_min_axioms =
    pp_purity_schema \<union>
    pp_application_closure_schema \<union>
    {pp_persistence pp_unary_ty, pp_QSS, pp_zeroary_exhaustion}"

lemma pp_T3_min_subset:
  "pp_T3_min_axioms \<subseteq> insert pp_zeroary_exhaustion pp_T3_axioms"
  unfolding pp_T3_min_axioms_def pp_T3_axioms_def
    pp_T6_core_PP_axioms_def pp_persistence_schema_def
  by blast

subsection \<open>The parameter theorem\<close>

lemma CEV_T3_parameter:
  assumes ax: "pp_T3_min_axioms \<subseteq> T"
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
    using ax unfolding pp_T3_min_axioms_def by blast
  have pers: "pp_persistence pp_unary_ty \<in> T"
    using ax unfolding pp_T3_min_axioms_def by blast
  have exh: "pp_zeroary_exhaustion \<in> T"
    using ax unfolding pp_T3_min_axioms_def by blast
  have cl_pp: "pp_application_closure Prop Prop \<in> T"
    using ax unfolding pp_T3_min_axioms_def
      pp_application_closure_schema_def by blast
  have cl1:
    "pp_application_closure pp_unary_ty
       (pp_unary_ty \<rightarrow>\<^sub>o Prop) \<in> T"
    using ax unfolding pp_T3_min_axioms_def
      pp_application_closure_schema_def by blast
  have cl2: "pp_application_closure pp_unary_ty Prop \<in> T"
    using ax unfolding pp_T3_min_axioms_def
      pp_application_closure_schema_def by blast
  have negpure: "pp_pure pp_unary_ty pp_negation_operator \<in> T"
    using ax pp_negation_operator_purity_axiom
    unfolding pp_T3_min_axioms_def by blast
  have eqb:
    "pp_pure (pp_unary_ty \<rightarrow>\<^sub>o (pp_unary_ty \<rightarrow>\<^sub>o Prop))
       (pp_eq_builder pp_unary_ty) \<in> T"
    using ax pp_eq_builder_purity_axiom
    unfolding pp_T3_min_axioms_def by blast

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

  \<comment> \<open>Persistence boxes the two purity premises\<close>
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
  \<comment> \<open>identity premises are necessary\<close>
  have d_boxEA: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o ?EA"
    using Yx_type Zx_type d_EA by (rule CEV_axiom_from_box_of_eq)
  have d_boxPZEA:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (Conj ?PZ ?EA)"
    using PZ_type EA_type d_boxPZ d_boxEA by (rule CEV_axiom_from_box_conj)
  have d_boxA: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o ?A"
    using PY_type has_type.Conj[OF PZ_type EA_type] d_boxPY d_boxPZEA
    by (rule CEV_axiom_from_box_conj)

  \<comment> \<open>necessitated QSS, in the form required by the K-transfer\<close>
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
  have imp_thm:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?A (Imp ?B ?D)"
    using qss_raw CEV_axiom_proves.Base[OF rearrange]
    by (rule CEV_axiom_proves.MP)

  have d_diaD: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o ?D"
    using A_type B_type D_type imp_thm d_boxA d_Dia
    by (rule CEV_axiom_from_box_diamond_mp)

  \<comment> \<open>the identity between two pure operators is a pure proposition\<close>
  have d_pureD: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop ?D"
    using cl1 cl2 eqb Y_type Z_type d_PY d_PZ
    by (rule CEV_axiom_from_pure_eq_proposition)
  have d_D: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?D"
    using exh cl_pp negpure D_type d_pureD d_diaD
    by (rule CEV_axiom_from_pure_diamond_elim)

  \<comment> \<open>discharge the three local assumptions\<close>
  have step1:
    "\<Gamma> ; T ; insert ?PC {?Dia}
       \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?EA ?D"
    using EA_type d_D by (rule CEV_axiom_from_deduction)
  have step2:
    "\<Gamma> ; T ; {?Dia} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?PC (Imp ?EA ?D)"
    using PC_type step1 by (rule CEV_axiom_from_deduction)
  show ?thesis
    using Dia_type step2 by (rule CEV_axiom_from_singleton_imp)
qed

subsection \<open>Closing the binders\<close>

theorem CEV_Goodman_T3_heredity_min:
  assumes ax: "pp_T3_min_axioms \<subseteq> T"
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
    using CEV_T3_parameter[OF ax x2_type Y1_type Z0_type] .
  have BODY_type: "?G3 \<turnstile> ?BODY : Prop"
    using CEV_axiom_proves_formula[OF core] by (auto elim: has_type.cases)
  have fp_unfold:
    "pp_fun_prime (Var 0) = Forall ?U (Forall ?U ?BODY)"
    by (simp add: pp_fun_prime_def shift_by_def shift_ren_def)
  have dia1_type:
    "[?U, Prop] \<turnstile> \<diamond>\<^sub>o (pp_fun Prop (Var 1)) : Prop"
    by (intro typed_ObjDiamond typed_pp_fun has_type.Var)
      (simp add: lookup_def)
  have dia0_type:
    "[Prop] \<turnstile> \<diamond>\<^sub>o (pp_fun Prop (Var 0)) : Prop"
    by (intro typed_ObjDiamond typed_pp_fun has_type.Var)
      (simp add: lookup_def)
  have gen1:
    "[?U, Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<diamond>\<^sub>o (pp_fun Prop (Var 1))) (Forall ?U ?BODY)"
  proof (rule CEV_axiom_proves.Gen)
    show "[?U, Prop] \<turnstile> \<diamond>\<^sub>o (pp_fun Prop (Var 1)) : Prop"
      by (rule dia1_type)
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
      by (rule dia0_type)
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

corollary CEV_Goodman_T3_heredity_with_exhaustion:
  "[] ; insert pp_zeroary_exhaustion pp_T3_axioms
     \<turnstile>\<^sub>CEV\<^sup>+ pp_T3_heredity"
  using pp_T3_min_subset by (rule CEV_Goodman_T3_heredity_min)

end
