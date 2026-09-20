theory Bacon_PP_Goodman_Heredity_Core
  imports 
    "Goodman_Legacy_03.Bacon_PP_Goodman_Heredity_Rigidity"
begin

section \<open>Exact instantiations of QSS and Persistence\<close>

definition qss_body3 :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "qss_body3 X Y z =
    Imp
      (Conj
        (pp_pure pp_unary_ty X)
        (Conj (pp_pure pp_unary_ty Y) (pp_fun Prop z)))
      (Imp
        (Eq Prop (App X z) (App Y z))
        (Eq pp_unary_ty X Y))"

lemma pp_QSS_as_body:
  "pp_QSS =
    Forall pp_unary_ty
      (Forall pp_unary_ty
        (Forall Prop (qss_body3 (Var 2) (Var 1) (Var 0))))"
  by (simp add: pp_QSS_def qss_body3_def)

lemma subst_qss_body3:
  "subst \<theta> (qss_body3 X Y z) =
    qss_body3 (subst \<theta> X) (subst \<theta> Y) (subst \<theta> z)"
  by (simp add: qss_body3_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def)

lemma typed_qss_body3:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and z_type: "\<Gamma> \<turnstile> z : Prop"
  shows "\<Gamma> \<turnstile> qss_body3 X Y z : Prop"
  unfolding qss_body3_def
  using typed_pp_pure[OF X_type] typed_pp_pure[OF Y_type]
    typed_pp_fun[OF z_type]
    has_type.App[OF X_type[unfolded pp_unary_ty_def] z_type]
    has_type.App[OF Y_type[unfolded pp_unary_ty_def] z_type]
    X_type Y_type
  by (intro has_type.Imp has_type.Conj has_type.Eq)

lemma typed_pp_QSS_ctx:
  "\<Gamma> \<turnstile> pp_QSS : Prop"
  by (rule infer_type_sound)
    (simp add: pp_QSS_def pp_unary_ty_def pp_pure_def pp_Pure_def
      pp_fun_def pp_Fun_def lookup_def)

lemma CEV_axiom_QSS_instance:
  assumes qss: "pp_QSS \<in> T"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and z_type: "\<Gamma> \<turnstile> z : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ qss_body3 X Y z"
proof -
  have d0: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS"
    using qss typed_pp_QSS_ctx by (rule CEV_axiom_proves.Axiom)
  have d0': "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Forall pp_unary_ty
      (Forall pp_unary_ty
        (Forall Prop (qss_body3 (Var 2) (Var 1) (Var 0))))"
    using d0 unfolding pp_QSS_as_body .
  have t0: "\<Gamma> \<turnstile>
    Forall pp_unary_ty
      (Forall pp_unary_ty
        (Forall Prop (qss_body3 (Var 2) (Var 1) (Var 0)))) : Prop"
    using typed_pp_QSS_ctx unfolding pp_QSS_as_body .
  have d1raw: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    subst0 X
      (Forall pp_unary_ty
        (Forall Prop (qss_body3 (Var 2) (Var 1) (Var 0))))"
    using t0 X_type d0' by (rule CEV_axiom_UI_typed)
  have e1:
    "subst0 X
      (Forall pp_unary_ty
        (Forall Prop (qss_body3 (Var 2) (Var 1) (Var 0)))) =
     Forall pp_unary_ty
       (Forall Prop
         (qss_body3 (shift (shift X)) (Var 1) (Var 0)))"
    by (simp add: subst0_def subst_qss_body3 qss_body3_def shift_def
      pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def eval_nat_numeral)
  have d1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Forall pp_unary_ty
      (Forall Prop
        (qss_body3 (shift (shift X)) (Var 1) (Var 0)))"
    using d1raw unfolding e1 .
  have t1: "\<Gamma> \<turnstile>
    Forall pp_unary_ty
      (Forall Prop
        (qss_body3 (shift (shift X)) (Var 1) (Var 0))) : Prop"
    using CEV_axiom_proves_formula[OF d1] .
  have d2raw: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    subst0 Y
      (Forall Prop
        (qss_body3 (shift (shift X)) (Var 1) (Var 0)))"
    using t1 Y_type d1 by (rule CEV_axiom_UI_typed)
  have e2:
    "subst0 Y
      (Forall Prop
        (qss_body3 (shift (shift X)) (Var 1) (Var 0))) =
     Forall Prop (qss_body3 (shift X) (shift Y) (Var 0))"
    by (simp add: subst0_def subst_qss_body3 qss_body3_def shift_def
      pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def eval_nat_numeral
      subst_lift_shift[unfolded shift_def]
      subst0_shift[of Y X, unfolded subst0_def shift_def])
  have d2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Forall Prop (qss_body3 (shift X) (shift Y) (Var 0))"
    using d2raw unfolding e2 .
  have t2: "\<Gamma> \<turnstile>
    Forall Prop (qss_body3 (shift X) (shift Y) (Var 0)) : Prop"
    using CEV_axiom_proves_formula[OF d2] .
  have d3raw: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    subst0 z (qss_body3 (shift X) (shift Y) (Var 0))"
    using t2 z_type d2 by (rule CEV_axiom_UI_typed)
  have e3:
    "subst0 z (qss_body3 (shift X) (shift Y) (Var 0)) =
     qss_body3 X Y z"
    by (simp add: subst0_def subst_qss_body3 qss_body3_def shift_def
      pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def eval_nat_numeral
      subst0_shift[of z X, unfolded subst0_def shift_def]
      subst0_shift[of z Y, unfolded subst0_def shift_def])
  show ?thesis
    using d3raw unfolding e3 .
qed

lemma CEV_axiom_persistence_instance:
  assumes pers: "pp_persistence \<sigma> \<in> T"
    and X_type: "\<Gamma> \<turnstile> X : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_pure \<sigma> X) (\<box>\<^sub>o (pp_pure \<sigma> X))"
proof -
  have pers_type: "\<Gamma> \<turnstile> pp_persistence \<sigma> : Prop"
    by (rule infer_type_sound)
      (simp add: pp_persistence_def pp_pure_def pp_Pure_def
        ObjBox_def ObjTrue_def lookup_def)
  have d0: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_persistence \<sigma>"
    using pers pers_type by (rule CEV_axiom_proves.Axiom)
  have d1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    subst0 X
      (Imp (pp_pure \<sigma> (Var 0)) (\<box>\<^sub>o (pp_pure \<sigma> (Var 0))))"
    using pers_type[unfolded pp_persistence_def] X_type
      d0[unfolded pp_persistence_def]
    by (rule CEV_axiom_UI_typed)
  show ?thesis
    using d1
    by (simp add: subst0_def pp_pure_def pp_Pure_def ObjBox_def ObjTrue_def)
qed

end
