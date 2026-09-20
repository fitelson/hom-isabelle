theory Bacon_PP_Fun_Prime_Control_Heredity
  imports 
    "Goodman_Legacy_Control.Bacon_PP_Fun_Prime_Control"
    "Goodman_Legacy_04.Bacon_PP_Goodman_Heredity_Exhaustion"
begin

section \<open>Heredity of fun-prime under PP and zeroary Exhaustion\<close>

lemma CEV_PP_unary_persistence_from:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and exh: "pp_zeroary_exhaustion \<in> T"
    and xt: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and px: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty X"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o (pp_pure pp_unary_ty X)"
proof -
  have ct: "\<Gamma> \<turnstile> pp_Pure pp_unary_ty : pp_unary_classifier_ty"
    using typed_pp_Pure by (simp add: pp_unary_classifier_ty_def)
  have pp_type: "\<Gamma> \<turnstile> pp_target_PP : Prop"
    by (rule infer_type_sound)
      (simp add: pp_target_PP_def pp_purity_of_pure_def pp_pure_def pp_Pure_def lookup_def)
  have pp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_target_PP"
    using core pp_T6_target_axiom pp_type
    by (meson CEV_axiom_proves.Axiom subsetD)
  have cp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_classifier_ty (pp_Pure pp_unary_ty)"
    using CEV_axiom_from.Theorem[OF pp]
    by (simp add: pp_target_PP_def pp_purity_of_pure_def pp_unary_classifier_ty_def pp_unary_ty_def)
  have cl: "pp_application_closure pp_unary_ty Prop \<in> T"
    using core pp_T6_application_closure_axiom by blast
  have ppx: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop (pp_pure pp_unary_ty X)"
    using pp_axiom_application_closed_from[OF cl ct[unfolded pp_unary_classifier_ty_def] xt
      cp[unfolded pp_unary_classifier_ty_def] px]
    by (simp only: pp_pure_def)
  have rule: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_pure Prop (pp_pure pp_unary_ty X))
        (Imp (pp_pure pp_unary_ty X) (\<box>\<^sub>o (pp_pure pp_unary_ty X)))"
    using pp_axiom_zeroary_exhaustion_imp[OF exh typed_pp_pure[OF xt]]
    by (rule CEV_axiom_from.Theorem)
  show ?thesis using px CEV_axiom_from.MP[OF ppx rule] by (rule CEV_axiom_from.MP)
qed

lemma CEV_control_separation_rule:
  assumes p: "\<Gamma> \<turnstile> p : Prop"
    and a: "\<Gamma> \<turnstile> A : pp_unary_ty" and b: "\<Gamma> \<turnstile> B : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Conj (pp_pure pp_unary_ty A)
      (Conj (pp_pure pp_unary_ty B) (Eq Prop (App A p) (App B p))))
      (Imp (pp_fun_prime p) (Eq pp_unary_ty A B))"
proof -
  let ?H = "Conj (pp_pure pp_unary_ty A)
    (Conj (pp_pure pp_unary_ty B) (Eq Prop (App A p) (App B p)))"
  let ?F = "pp_fun_prime p"
  have ft: "\<Gamma> \<turnstile> ?F : Prop" using p by (rule typed_pp_fun_prime)
  have ap: "\<Gamma> \<turnstile> App A p : Prop"
    using a p unfolding pp_unary_ty_def by (rule has_type.App)
  have bp: "\<Gamma> \<turnstile> App B p : Prop"
    using b p unfolding pp_unary_ty_def by (rule has_type.App)
  have ht: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_pure[OF a] typed_pp_pure[OF b] ap bp
    by (intro has_type.Conj has_type.Eq)
  have h: "\<Gamma> ; T ; insert ?F {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using ht by (intro CEV_axiom_from.Assumption) simp
  have f: "\<Gamma> ; T ; insert ?F {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using ft by (intro CEV_axiom_from.Assumption) simp
  have pa: "\<Gamma> ; T ; insert ?F {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty A"
    using h by (rule CEV_axiom_from_conj_left)
  have tail: "\<Gamma> ; T ; insert ?F {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Conj (pp_pure pp_unary_ty B) (Eq Prop (App A p) (App B p))"
    using h by (rule CEV_axiom_from_conj_right)
  have pb: "\<Gamma> ; T ; insert ?F {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty B"
    using tail by (rule CEV_axiom_from_conj_left)
  have eq: "\<Gamma> ; T ; insert ?F {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App A p) (App B p)"
    using tail by (rule CEV_axiom_from_conj_right)
  have ab: "\<Gamma> ; T ; insert ?F {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty A B"
    using p a b f pa pb eq by (rule CEV_axiom_from_fun_prime)
  show ?thesis using ht CEV_axiom_from_deduction[OF ft ab]
    by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_fun_prime_heredity_parameter:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
    and x_type: "\<Gamma> \<turnstile> x : Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (\<diamond>\<^sub>o (pp_fun_prime x))
      (Imp
        (Conj (pp_pure pp_unary_ty Y) (pp_pure pp_unary_ty Z))
        (Imp
          (Eq Prop (App Y x) (App Z x))
          (Eq pp_unary_ty Y Z)))"
proof -
  have core: "pp_T6_core_PP_axioms \<subseteq> T" using ax by blast
  have exh: "pp_zeroary_exhaustion \<in> T"
    using ax unfolding pp_T6_core_PP_axioms_def by blast
  have cl_pp: "pp_application_closure Prop Prop \<in> T"
    using ax unfolding pp_T6_core_PP_axioms_def
      pp_application_closure_schema_def by blast
  have cl1:
    "pp_application_closure pp_unary_ty
       (pp_unary_ty \<rightarrow>\<^sub>o Prop) \<in> T"
    using ax unfolding pp_T6_core_PP_axioms_def
      pp_application_closure_schema_def by blast
  have cl2: "pp_application_closure pp_unary_ty Prop \<in> T"
    using ax unfolding pp_T6_core_PP_axioms_def
      pp_application_closure_schema_def by blast
  have negpure: "pp_pure pp_unary_ty pp_negation_operator \<in> T"
    using ax pp_negation_operator_purity_axiom
    unfolding pp_T6_core_PP_axioms_def by blast
  have eqb:
    "pp_pure (pp_unary_ty \<rightarrow>\<^sub>o (pp_unary_ty \<rightarrow>\<^sub>o Prop))
       (pp_eq_builder pp_unary_ty) \<in> T"
    using ax pp_eq_builder_purity_axiom
    unfolding pp_T6_core_PP_axioms_def by blast

  let ?PY = "pp_pure pp_unary_ty Y"
  let ?PZ = "pp_pure pp_unary_ty Z"
  let ?PC = "Conj ?PY ?PZ"
  let ?EA = "Eq Prop (App Y x) (App Z x)"
  let ?D = "Eq pp_unary_ty Y Z"
  let ?B = "pp_fun_prime x"
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
    using x_type by (rule typed_pp_fun_prime)
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
    using core exh Y_type d_PY by (rule CEV_PP_unary_persistence_from)
  have d_boxPZ: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o ?PZ"
    using core exh Z_type d_PZ by (rule CEV_PP_unary_persistence_from)
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

  have imp_thm:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?A (Imp ?B ?D)"
    using x_type Y_type Z_type by (rule CEV_control_separation_rule)

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

lemma shift_fun_prime_diamond[simp]:
  "shift (\<diamond>\<^sub>o (pp_fun_prime p)) = \<diamond>\<^sub>o (pp_fun_prime (shift p))"
proof -
  have st: "shift ObjTrue = ObjTrue" by (simp add: ObjTrue_def shift_def)
  show ?thesis by (simp add: ObjDiamond_def ObjBox_def st)
qed

theorem CEV_fun_prime_heredity_PP_exhaustion:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (\<diamond>\<^sub>o (pp_fun_prime p)) (pp_fun_prime p)"
proof -
  let ?U = pp_unary_ty
  let ?p2 = "shift_by 2 p"
  let ?BODY = "Imp (Conj (pp_pure ?U (Var 1)) (pp_pure ?U (Var 0)))
    (Imp (Eq Prop (App (Var 1) ?p2) (App (Var 0) ?p2))
      (Eq ?U (Var 1) (Var 0)))"
  have p1: "?U # \<Gamma> \<turnstile> shift p : Prop" using p by (rule typed_shift_ctx)
  have p2: "?U # ?U # \<Gamma> \<turnstile> ?p2 : Prop"
    using shift_by_preserves_typing[OF p, of "[?U,?U]"] by (simp add: numeral_2_eq_2)
  have y: "?U # ?U # \<Gamma> \<turnstile> Var 1 : ?U"
    by (rule has_type.Var) (simp add: lookup_def)
  have z: "?U # ?U # \<Gamma> \<turnstile> Var 0 : ?U" by (rule typed_var0)
  have parameter: "?U # ?U # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (\<diamond>\<^sub>o (pp_fun_prime ?p2)) ?BODY"
    using ax p2 y z by (rule CEV_fun_prime_heredity_parameter)
  have bt: "?U # ?U # \<Gamma> \<turnstile> ?BODY : Prop"
    using CEV_axiom_proves_formula[OF parameter] by (auto elim: has_type.cases)
  have gen1: "?U # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (\<diamond>\<^sub>o (pp_fun_prime (shift p))) (Forall ?U ?BODY)"
  proof (rule CEV_axiom_proves.Gen)
    show "?U # \<Gamma> \<turnstile> \<diamond>\<^sub>o (pp_fun_prime (shift p)) : Prop"
      using p1 by (intro typed_ObjDiamond typed_pp_fun_prime)
    show "?U # ?U # \<Gamma> \<turnstile> ?BODY : Prop" by (rule bt)
    show "?U # ?U # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (\<diamond>\<^sub>o (pp_fun_prime (shift p)))) ?BODY"
      using parameter by (simp add: shift_shift_eq_shift_by_2)
  qed
  have gen2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (\<diamond>\<^sub>o (pp_fun_prime p)) (Forall ?U (Forall ?U ?BODY))"
  proof (rule CEV_axiom_proves.Gen)
    show "\<Gamma> \<turnstile> \<diamond>\<^sub>o (pp_fun_prime p) : Prop"
      using p by (intro typed_ObjDiamond typed_pp_fun_prime)
    show "?U # \<Gamma> \<turnstile> Forall ?U ?BODY : Prop" using bt by (rule has_type.Forall)
    show "?U # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (\<diamond>\<^sub>o (pp_fun_prime p))) (Forall ?U ?BODY)"
      using gen1 by simp
  qed
  show ?thesis using gen2 by (simp only: pp_fun_prime_def)
qed

theorem CEV_non_fun_prime_persists_PP_exhaustion:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Neg (pp_fun_prime p)) (\<box>\<^sub>o (Neg (pp_fun_prime p)))"
proof -
  let ?J = "pp_fun_prime p"
  have jt: "\<Gamma> \<turnstile> ?J : Prop" using p by (rule typed_pp_fun_prime)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Imp (\<diamond>\<^sub>o ?J) ?J) (Imp (Neg ?J) (\<box>\<^sub>o (Neg ?J)))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Neg typed_ObjBox typed_ObjDiamond jt,
       simp only: ObjDiamond_def prop_eval.simps, blast)
  show ?thesis using CEV_fun_prime_heredity_PP_exhaustion[OF ax p] taut
    by (rule CEV_axiom_proves.MP)
qed

lemma CEV_control_local_iff_right_cong:
  assumes at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop"
    and ct: "\<Gamma> \<turnstile> C : Prop"
    and eq: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop B C"
  shows "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (A \<longleftrightarrow>\<^sub>o B) (A \<longleftrightarrow>\<^sub>o C)"
proof -
  let ?FB = "pp_biconditional_operator B"
  let ?FC = "pp_biconditional_operator C"
  have fb: "\<Gamma> \<turnstile> ?FB : pp_unary_ty" using bt by (rule typed_pp_biconditional_operator)
  have fc: "\<Gamma> \<turnstile> ?FC : pp_unary_ty" using ct by (rule typed_pp_biconditional_operator)
  have ba: "\<Gamma> \<turnstile> App ?FB A : Prop"
    using fb at unfolding pp_unary_ty_def by (rule has_type.App)
  have ca: "\<Gamma> \<turnstile> App ?FC A : Prop"
    using fc at unfolding pp_unary_ty_def by (rule has_type.App)
  have ab: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using at bt by (intro has_type.Conj has_type.Imp)
  have ac: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o C) : Prop"
    using at ct by (intro has_type.Conj has_type.Imp)
  have eqops: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty ?FB ?FC"
    unfolding pp_biconditional_operator_def
    using typed_pp_biconditional_builder bt ct eq by (rule CEV_axiom_from_eq_app_right)
  have middle: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?FB A) (App ?FC A)"
    using fb fc at eqops by (rule CEV_axiom_from_pp_apply_cong_left)
  have left0: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (App ?FB A) (A \<longleftrightarrow>\<^sub>o B)"
    using ba ab CEV_pp_biconditional_operator_apply[OF bt at] by (rule CEV_zeroary_equivalence)
  have left: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (A \<longleftrightarrow>\<^sub>o B) (App ?FB A)"
    using ba ab CEV_axiom_from.Theorem[OF CEV_axiom_proves.Base[OF left0]]
    by (rule CEV_axiom_from_eq_sym)
  have right0: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (App ?FC A) (A \<longleftrightarrow>\<^sub>o C)"
    using ca ac CEV_pp_biconditional_operator_apply[OF ct at] by (rule CEV_zeroary_equivalence)
  have mid: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (A \<longleftrightarrow>\<^sub>o B) (App ?FC A)"
    using ab ba ca left middle by (rule CEV_axiom_from_eq_trans)
  show ?thesis using ab ca ac mid CEV_axiom_from.Theorem[OF CEV_axiom_proves.Base[OF right0]]
    by (rule CEV_axiom_from_eq_trans)
qed

theorem CEV_control_eq_negation_when_not_fun_prime:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Neg (pp_fun_prime p)) (Eq Prop (App pp_fun_prime_control p) (Neg p))"
proof -
  let ?F = "pp_fun_prime p"
  let ?Jp = "App pp_fun_prime_classifier p"
  let ?Sp = "App pp_fun_prime_control p"
  let ?H = "Neg ?F"
  have ft: "\<Gamma> \<turnstile> ?F : Prop" using p by (rule typed_pp_fun_prime)
  have ht: "\<Gamma> \<turnstile> ?H : Prop" using ft by (rule has_type.Neg)
  have jt: "\<Gamma> \<turnstile> ?Jp : Prop" using typed_pp_fun_prime_classifier p by (rule has_type.App)
  have st: "\<Gamma> \<turnstile> ?Sp : Prop"
    using typed_fun_prime_control p unfolding pp_unary_ty_def by (rule has_type.App)
  have nt: "\<Gamma> \<turnstile> Neg p : Prop" using p by (rule has_type.Neg)
  have ptj: "\<Gamma> \<turnstile> (p \<longleftrightarrow>\<^sub>o ?Jp) : Prop"
    using p jt by (intro has_type.Conj has_type.Imp)
  have ptf: "\<Gamma> \<turnstile> (p \<longleftrightarrow>\<^sub>o ObjFalse) : Prop"
    using p typed_ObjFalse by (intro has_type.Conj has_type.Imp)
  have h: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using ht by (intro CEV_axiom_from.Assumption) simp
  have boxed: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o ?H"
    using h CEV_axiom_from.Theorem[OF CEV_non_fun_prime_persists_PP_exhaustion[OF ax p]]
    by (rule CEV_axiom_from.MP)
  have f0: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?F ObjFalse"
    using boxed CEV_axiom_from.Theorem[OF CEV_axiom_box_neg_implies_eq_ObjFalse[OF ft]]
    by (rule CEV_axiom_from.MP)
  have j0: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?Jp ObjFalse"
    using jt ft typed_ObjFalse CEV_axiom_from.Theorem[OF CEV_control_J_beta_eq[OF p]] f0
    by (rule CEV_axiom_from_eq_trans)
  have middle: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (p \<longleftrightarrow>\<^sub>o ?Jp) (p \<longleftrightarrow>\<^sub>o ObjFalse)"
    using p jt typed_ObjFalse j0 by (rule CEV_control_local_iff_right_cong)
  have sb: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?Sp (p \<longleftrightarrow>\<^sub>o ?Jp)"
    using st ptj CEV_axiom_proves.Base[OF CEV_control_beta[OF p]]
    by (rule CEV_axiom_zeroary_equivalence)
  have nb: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (p \<longleftrightarrow>\<^sub>o ObjFalse) (Neg p)"
    using ptf nt CEV_axiom_proves.Base[OF CEV_biconditional_with_ObjFalse[OF p]]
    by (rule CEV_axiom_zeroary_equivalence)
  have sp0: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?Sp (p \<longleftrightarrow>\<^sub>o ObjFalse)"
    using st ptj ptf CEV_axiom_from.Theorem[OF sb] middle by (rule CEV_axiom_from_eq_trans)
  have result: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?Sp (Neg p)"
    using st ptf nt sp0 CEV_axiom_from.Theorem[OF nb] by (rule CEV_axiom_from_eq_trans)
  show ?thesis using ht result by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_fun_prime_negation_reflection:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T" and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime (Neg p)) (pp_fun_prime p)"
proof -
  have np: "\<Gamma> \<turnstile> Neg p : Prop" using p by (rule has_type.Neg)
  have nnp: "\<Gamma> \<turnstile> Neg (Neg p) : Prop" using np by (rule has_type.Neg)
  have eq: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (Neg (Neg p)) p"
    using p nnp CEV_axiom_proves.Base[OF CEV_double_negation_eq[OF p]]
    by (rule CEV_control_eq_sym)
  have reflect_nn: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime (Neg (Neg p))) (pp_fun_prime p)"
    using eq CEV_axiom_fun_prime_eq_transport[OF nnp p] by (rule CEV_axiom_proves.MP)
  have forward: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime (Neg p)) (pp_fun_prime (Neg (Neg p)))"
    using core np by (rule CEV_fun_prime_under_negation)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Imp (pp_fun_prime (Neg p)) (pp_fun_prime (Neg (Neg p))))
      (Imp (Imp (pp_fun_prime (Neg (Neg p))) (pp_fun_prime p))
        (Imp (pp_fun_prime (Neg p)) (pp_fun_prime p)))"
    by (rule CEV_control_PC)
      (intro has_type.Imp typed_pp_fun_prime p np nnp, simp only: prop_eval.simps, blast)
  show ?thesis using reflect_nn CEV_axiom_proves.MP[OF forward taut] by (rule CEV_axiom_proves.MP)
qed

theorem CEV_control_reflects_fun_prime_PP_exhaustion:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime (App pp_fun_prime_control p)) (pp_fun_prime p)"
proof -
  let ?Sp = "App pp_fun_prime_control p"
  let ?F = "pp_fun_prime p"
  let ?FS = "pp_fun_prime ?Sp"
  let ?FN = "pp_fun_prime (Neg p)"
  let ?E = "Eq Prop ?Sp (Neg p)"
  have core: "pp_T6_core_PP_axioms \<subseteq> T" using ax by blast
  have sp: "\<Gamma> \<turnstile> ?Sp : Prop"
    using typed_fun_prime_control p unfolding pp_unary_ty_def by (rule has_type.App)
  have np: "\<Gamma> \<turnstile> Neg p : Prop" using p by (rule has_type.Neg)
  have ft: "\<Gamma> \<turnstile> ?F : Prop" using p by (rule typed_pp_fun_prime)
  have fst: "\<Gamma> \<turnstile> ?FS : Prop" using sp by (rule typed_pp_fun_prime)
  have fnt: "\<Gamma> \<turnstile> ?FN : Prop" using np by (rule typed_pp_fun_prime)
  have et: "\<Gamma> \<turnstile> ?E : Prop" using sp np by (rule has_type.Eq)
  have eqrule: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Neg ?F) ?E"
    using ax p by (rule CEV_control_eq_negation_when_not_fun_prime)
  have transport: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?E (Imp ?FS ?FN)"
    using sp np by (rule CEV_axiom_fun_prime_eq_transport)
  have negback: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?FN ?F"
    using core p by (rule CEV_fun_prime_negation_reflection)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Imp (Neg ?F) ?E) (Imp (Imp ?E (Imp ?FS ?FN)) (Imp (Imp ?FN ?F) (Imp ?FS ?F)))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Neg ft et fst fnt, simp only: prop_eval.simps, blast)
  show ?thesis using CEV_axiom_proves.MP[OF negback
    CEV_axiom_proves.MP[OF transport CEV_axiom_proves.MP[OF eqrule taut]]] .
qed

text \<open>
  The reverse implication is established from the core PP stock plus ZEROARY
  Exhaustion. No Recombination, QSS, fundamental entity, or fun-prime witness
  is assumed. This does not prove preservation of fun-prime by S, and does
  not settle the control identity for the Recombination-only stock.
\<close>

ML \<open>
  val checked = [
    @{thm CEV_PP_unary_persistence_from},
    @{thm CEV_fun_prime_heredity_PP_exhaustion},
    @{thm CEV_non_fun_prime_persists_PP_exhaustion},
    @{thm CEV_control_eq_negation_when_not_fun_prime},
    @{thm CEV_control_reflects_fun_prime_PP_exhaustion}]
  val _ = List.app (fn thm =>
    if null (Thm_Deps.all_oracles [thm]) andalso null (Thm.hyps_of thm)
       andalso null (Thm.tpairs_of thm)
    then () else error "Fun-prime heredity audit failed") checked
  val _ = writeln "GOODMAN-FUN-PRIME-HEREDITY: five theorem objects kernel-clean"
\<close>

end
