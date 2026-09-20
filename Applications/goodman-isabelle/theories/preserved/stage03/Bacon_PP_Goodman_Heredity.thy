theory Bacon_PP_Goodman_Heredity
  imports 
    "Goodman_Legacy_03.Bacon_PP_Goodman_T2f_Verified"
begin

section \<open>Goodman T3: Heredity\<close>

text \<open>
  QSS says that two pure proposition-valued unary operators which agree on a
  fundamental proposition are identical.  In an axiom extension, QSS can be
  necessitated by \<open>CEV_axiom_necessitation\<close>.  Goodman claims that
  Persistence then suffices to show that anything which is possibly
  fundamental is a \<open>fun\<acute>\<close> proposition.  The derivation below isolates
  the exact modal gap in that claim.
\<close>

definition pp_QSS :: oterm where
  "pp_QSS =
    Forall pp_unary_ty
      (Forall pp_unary_ty
        (Forall Prop
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 2))
              (Conj
                (pp_pure pp_unary_ty (Var 1))
                (pp_fun Prop (Var 0))))
            (Imp
              (Eq Prop (App (Var 2) (Var 0))
                (App (Var 1) (Var 0)))
              (Eq pp_unary_ty (Var 2) (Var 1))))))"

definition pp_QSS_instance ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_QSS_instance X Y x =
    Imp
      (Conj
        (pp_pure pp_unary_ty X)
        (Conj
          (pp_pure pp_unary_ty Y)
          (pp_fun Prop x)))
      (Imp
        (Eq Prop (App X x) (App Y x))
        (Eq pp_unary_ty X Y))"

lemma typed_pp_QSS:
  "[] \<turnstile> pp_QSS : Prop"
  by (rule infer_type_sound)
    (simp add: pp_QSS_def pp_unary_ty_def pp_pure_def pp_Pure_def
      pp_fun_def pp_Fun_def lookup_def)

lemma typed_pp_QSS_instance:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and x_type: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile> pp_QSS_instance X Y x : Prop"
  unfolding pp_QSS_instance_def
  using typed_pp_pure[OF X_type] typed_pp_pure[OF Y_type]
    typed_pp_fun[OF x_type]
  using X_type Y_type x_type
  unfolding pp_unary_ty_def
  by (intro has_type.Imp has_type.Conj has_type.Eq has_type.App)

definition pp_T3_axioms :: "oterm set" where
  "pp_T3_axioms =
    pp_T6_core_PP_axioms \<union> pp_persistence_schema \<union> {pp_QSS}"

lemma pp_persistence_schema_typed_T3:
  assumes "A \<in> pp_persistence_schema"
  shows "[] \<turnstile> A : Prop"
  using assms typed_pp_persistence
  unfolding pp_persistence_schema_def by blast

lemma pp_T3_axioms_typed:
  assumes "A \<in> pp_T3_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_purity_schema_typed pp_application_closure_schema_typed
    typed_pp_target_PP pp_persistence_schema_typed_T3 typed_pp_QSS
  unfolding pp_T3_axioms_def pp_T6_core_PP_axioms_def
  by blast

lemma pp_axiom_QSS_instance:
  assumes qss: "pp_QSS \<in> T"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and x_type: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS_instance X Y x"
proof -
  let ?op = pp_unary_ty
  have qss_type: "\<Gamma> \<turnstile> pp_QSS : Prop"
    by (rule infer_type_sound)
      (simp add: pp_QSS_def pp_unary_ty_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def lookup_def)
  have d_qss: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_QSS"
    using qss qss_type by (rule CEV_axiom_proves.Axiom)
  have first_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 X
        (Forall ?op
          (Forall Prop
            (Imp
              (Conj
                (pp_pure ?op (Var 2))
                (Conj
                  (pp_pure ?op (Var 1))
                  (pp_fun Prop (Var 0))))
              (Imp
                (Eq Prop
                  (App (Var 2) (Var 0))
                  (App (Var 1) (Var 0)))
                (Eq ?op (Var 2) (Var 1))))))"
    using qss_type X_type d_qss
    unfolding pp_QSS_def
    by (rule CEV_axiom_UI_typed)
  have first:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall ?op
        (Forall Prop
          (Imp
            (Conj
              (pp_pure ?op (rename Suc (rename Suc X)))
              (Conj
                (pp_pure ?op (Var 1))
                (pp_fun Prop (Var 0))))
            (Imp
              (Eq Prop
                (App (rename Suc (rename Suc X)) (Var 0))
                (App (Var 1) (Var 0)))
              (Eq ?op
                (rename Suc (rename Suc X))
                (Var 1)))))"
    using first_raw
    by (simp add: subst0_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def subst_lift_shift eval_nat_numeral)
  have first_type:
    "\<Gamma> \<turnstile>
      Forall ?op
        (Forall Prop
          (Imp
            (Conj
              (pp_pure ?op (rename Suc (rename Suc X)))
              (Conj
                (pp_pure ?op (Var 1))
                (pp_fun Prop (Var 0))))
            (Imp
              (Eq Prop
                (App (rename Suc (rename Suc X)) (Var 0))
                (App (Var 1) (Var 0)))
              (Eq ?op
                (rename Suc (rename Suc X))
                (Var 1))))) : Prop"
    using first by (rule CEV_axiom_proves_formula)
  have second_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 Y
        (Forall Prop
          (Imp
            (Conj
              (pp_pure ?op (rename Suc (rename Suc X)))
              (Conj
                (pp_pure ?op (Var 1))
                (pp_fun Prop (Var 0))))
            (Imp
              (Eq Prop
                (App (rename Suc (rename Suc X)) (Var 0))
                (App (Var 1) (Var 0)))
              (Eq ?op
                (rename Suc (rename Suc X))
                (Var 1)))))"
    using first_type Y_type first
    by (rule CEV_axiom_UI_typed)
  have cancel_X:
    "subst (lift_subst (case_nat Y Var))
      (rename Suc (rename Suc X)) = rename Suc X"
  proof -
    have inner:
      "subst (case_nat Y Var) (shift X) = X"
      using subst0_shift[of Y X]
      unfolding subst0_def .
    have outer:
      "subst (lift_subst (case_nat Y Var)) (shift (shift X)) =
        shift (subst (case_nat Y Var) (shift X))"
      by (rule subst_lift_shift)
    show ?thesis
      using outer inner unfolding shift_def by simp
  qed
  have second:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall Prop
        (Imp
          (Conj
            (pp_pure ?op (rename Suc X))
            (Conj
              (pp_pure ?op (rename Suc Y))
              (pp_fun Prop (Var 0))))
          (Imp
            (Eq Prop
              (App (rename Suc X) (Var 0))
              (App (rename Suc Y) (Var 0)))
            (Eq ?op (rename Suc X) (rename Suc Y))))"
    using second_raw
    by (simp add: subst0_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def subst_lift_shift cancel_X)
  have second_type:
    "\<Gamma> \<turnstile>
      Forall Prop
        (Imp
          (Conj
            (pp_pure ?op (rename Suc X))
            (Conj
              (pp_pure ?op (rename Suc Y))
              (pp_fun Prop (Var 0))))
          (Imp
            (Eq Prop
              (App (rename Suc X) (Var 0))
              (App (rename Suc Y) (Var 0)))
            (Eq ?op (rename Suc X) (rename Suc Y)))) : Prop"
    using second by (rule CEV_axiom_proves_formula)
  have third_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 x
        (Imp
          (Conj
            (pp_pure ?op (rename Suc X))
            (Conj
              (pp_pure ?op (rename Suc Y))
              (pp_fun Prop (Var 0))))
          (Imp
            (Eq Prop
              (App (rename Suc X) (Var 0))
              (App (rename Suc Y) (Var 0)))
            (Eq ?op (rename Suc X) (rename Suc Y))))"
    using second_type x_type second
    by (rule CEV_axiom_UI_typed)
  have cancel_X_x:
    "subst (case_nat x Var) (rename Suc X) = X"
    using subst0_shift[of x X]
    unfolding subst0_def shift_def .
  have cancel_Y_x:
    "subst (case_nat x Var) (rename Suc Y) = Y"
    using subst0_shift[of x Y]
    unfolding subst0_def shift_def .
  show ?thesis
    using third_raw
    by (simp add: pp_QSS_instance_def subst0_def
        pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def
        cancel_X_x cancel_Y_x)
qed

lemma pp_axiom_persistence_imp:
  assumes persistence: "pp_persistence \<sigma> \<in> T"
    and X_type: "\<Gamma> \<turnstile> X : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_pure \<sigma> X)
      (\<box>\<^sub>o (pp_pure \<sigma> X))"
proof -
  have persistence_type:
    "\<Gamma> \<turnstile> pp_persistence \<sigma> : Prop"
    by (rule infer_type_sound)
      (simp add: pp_persistence_def pp_pure_def pp_Pure_def
        ObjBox_def ObjTrue_def lookup_def)
  have d_persistence:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_persistence \<sigma>"
    using persistence persistence_type
    by (rule CEV_axiom_proves.Axiom)
  have raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 X
        (Imp
          (pp_pure \<sigma> (Var 0))
          (\<box>\<^sub>o (pp_pure \<sigma> (Var 0))))"
    using persistence_type X_type d_persistence
    unfolding pp_persistence_def
    by (rule CEV_axiom_UI_typed)
  show ?thesis
    using raw
    by (simp add: subst0_def pp_pure_def pp_Pure_def
        ObjBox_def ObjTrue_def)
qed

lemma CEV_box_imp_diamond_imp:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp
      (\<box>\<^sub>o (Imp A B))
      (Imp (\<diamond>\<^sub>o A) (\<diamond>\<^sub>o B))"
proof -
  let ?H = "\<box>\<^sub>o (Imp A B)"
  let ?C = "Imp (Neg B) (Neg A)"
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using A_type B_type
    by (intro typed_ObjBox has_type.Imp)
  have neg_A_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by (rule has_type.Neg)
  have neg_B_type: "\<Gamma> \<turnstile> Neg B : Prop"
    using B_type by (rule has_type.Neg)
  have contra:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp A B) ?C"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma> (Imp (Imp A B) ?C)"
      unfolding prop_tautology_def
      using A_type B_type
      by (auto simp: prop_eval.simps)
  qed
  have box_contra:
    "\<Gamma> \<turnstile>\<^sub>CEV
      \<box>\<^sub>o (Imp (Imp A B) ?C)"
    using contra by (rule CEV_necessitation)
  have K1:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (\<box>\<^sub>o (Imp (Imp A B) ?C))
        (Imp ?H (\<box>\<^sub>o ?C))"
    using CEV_modal_K[
      OF has_type.Imp[OF A_type B_type]
        has_type.Imp[OF neg_B_type neg_A_type]]
    unfolding modal_K_def .
  have H_imp_box_C:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp ?H (\<box>\<^sub>o ?C)"
    using box_contra K1 by (rule CEV_proves.MP)
  have local_H: "CEV_from \<Gamma> ?H ?H"
    using H_type by (rule CEV_from.Assumption)
  have local_box_C:
    "CEV_from \<Gamma> ?H (\<box>\<^sub>o ?C)"
    using local_H CEV_from.Theorem[OF H_imp_box_C]
    by (rule CEV_from.MP)
  have K2:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (\<box>\<^sub>o ?C)
        (Imp
          (\<box>\<^sub>o (Neg B))
          (\<box>\<^sub>o (Neg A)))"
    using CEV_modal_K[OF neg_B_type neg_A_type]
    unfolding modal_K_def .
  have local_box_neg_imp:
    "CEV_from \<Gamma> ?H
      (Imp
        (\<box>\<^sub>o (Neg B))
        (\<box>\<^sub>o (Neg A)))"
    using local_box_C CEV_from.Theorem[OF K2]
    by (rule CEV_from.MP)
  have box_neg_A_type:
    "\<Gamma> \<turnstile> \<box>\<^sub>o (Neg A) : Prop"
    using neg_A_type by (rule typed_ObjBox)
  have box_neg_B_type:
    "\<Gamma> \<turnstile> \<box>\<^sub>o (Neg B) : Prop"
    using neg_B_type by (rule typed_ObjBox)
  have outer_contra:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp
          (\<box>\<^sub>o (Neg B))
          (\<box>\<^sub>o (Neg A)))
        (Imp
          (Neg (\<box>\<^sub>o (Neg A)))
          (Neg (\<box>\<^sub>o (Neg B))))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp
          (\<box>\<^sub>o (Neg B))
          (\<box>\<^sub>o (Neg A)))
        (Imp
          (Neg (\<box>\<^sub>o (Neg A)))
          (Neg (\<box>\<^sub>o (Neg B)))))"
      unfolding prop_tautology_def
      using box_neg_A_type box_neg_B_type
      by (auto simp: prop_eval.simps)
  qed
  have local_diamond_imp:
    "CEV_from \<Gamma> ?H
      (Imp
        (Neg (\<box>\<^sub>o (Neg A)))
        (Neg (\<box>\<^sub>o (Neg B))))"
    using local_box_neg_imp CEV_from.Theorem[OF outer_contra]
    by (rule CEV_from.MP)
  have result:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp ?H
        (Imp
          (Neg (\<box>\<^sub>o (Neg A)))
          (Neg (\<box>\<^sub>o (Neg B))))"
    using local_diamond_imp H_type
    by (rule CEV_from_deduction)
  show ?thesis
  using result unfolding ObjDiamond_def .
qed

lemma CEV_axiom_from_box_MP:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and box_imp:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        \<box>\<^sub>o (Imp A B)"
    and box_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o B"
proof -
  have K:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (\<box>\<^sub>o (Imp A B))
        (Imp (\<box>\<^sub>o A) (\<box>\<^sub>o B))"
    using CEV_modal_K[OF A_type B_type]
    unfolding modal_K_def
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (\<box>\<^sub>o A) (\<box>\<^sub>o B)"
    using box_imp K by (rule CEV_axiom_from.MP)
  show ?thesis
    using box_A step by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_diamond_MP:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and box_imp:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        \<box>\<^sub>o (Imp A B)"
    and diamond_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o B"
proof -
  have rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (\<box>\<^sub>o (Imp A B))
        (Imp (\<diamond>\<^sub>o A) (\<diamond>\<^sub>o B))"
    using CEV_box_imp_diamond_imp[OF A_type B_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (\<diamond>\<^sub>o A) (\<diamond>\<^sub>o B)"
    using box_imp rule by (rule CEV_axiom_from.MP)
  show ?thesis
    using diamond_A step by (rule CEV_axiom_from.MP)
qed

definition pp_T3_heredity :: oterm where
  "pp_T3_heredity =
    Forall Prop
      (Imp
        (\<diamond>\<^sub>o (pp_fun Prop (Var 0)))
        (pp_fun_prime (Var 0)))"

lemma typed_pp_T3_heredity:
  "[] \<turnstile> pp_T3_heredity : Prop"
  unfolding pp_T3_heredity_def
  by (intro has_type.Forall has_type.Imp typed_ObjDiamond
      typed_pp_fun typed_pp_fun_prime has_type.Var)
    (simp_all add: lookup_def)

subsection \<open>The missing possible-identity principle\<close>

definition pp_possible_identity_actual :: "otype \<Rightarrow> oterm" where
  "pp_possible_identity_actual \<sigma> =
    Forall \<sigma>
      (Forall \<sigma>
        (Imp
          (\<diamond>\<^sub>o (Eq \<sigma> (Var 1) (Var 0)))
          (Eq \<sigma> (Var 1) (Var 0))))"

lemma typed_pp_possible_identity_actual:
  "[] \<turnstile> pp_possible_identity_actual \<sigma> : Prop"
  by (rule infer_type_sound)
    (simp add: pp_possible_identity_actual_def ObjDiamond_def
      ObjBox_def ObjTrue_def lookup_def)

definition pp_T3_repaired_axioms :: "oterm set" where
  "pp_T3_repaired_axioms =
    pp_T3_axioms \<union>
      {pp_possible_identity_actual pp_unary_ty}"

lemma pp_T3_repaired_axioms_typed:
  assumes "A \<in> pp_T3_repaired_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_T3_axioms_typed typed_pp_possible_identity_actual
  unfolding pp_T3_repaired_axioms_def by blast

lemma pp_axiom_possible_identity_actual_instance:
  assumes pia: "pp_possible_identity_actual \<sigma> \<in> T"
    and X_type: "\<Gamma> \<turnstile> X : \<sigma>"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (\<diamond>\<^sub>o (Eq \<sigma> X Y))
      (Eq \<sigma> X Y)"
proof -
  have pia_type:
    "\<Gamma> \<turnstile> pp_possible_identity_actual \<sigma> : Prop"
    by (rule infer_type_sound)
      (simp add: pp_possible_identity_actual_def ObjDiamond_def
        ObjBox_def ObjTrue_def lookup_def)
  have d_pia:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_possible_identity_actual \<sigma>"
    using pia pia_type by (rule CEV_axiom_proves.Axiom)
  have first_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 X
        (Forall \<sigma>
          (Imp
            (\<diamond>\<^sub>o (Eq \<sigma> (Var 1) (Var 0)))
            (Eq \<sigma> (Var 1) (Var 0))))"
    using pia_type X_type d_pia
    unfolding pp_possible_identity_actual_def
    by (rule CEV_axiom_UI_typed)
  have first:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall \<sigma>
        (Imp
          (\<diamond>\<^sub>o (Eq \<sigma> (rename Suc X) (Var 0)))
          (Eq \<sigma> (rename Suc X) (Var 0)))"
    using first_raw
    by (simp add: subst0_def ObjDiamond_def ObjBox_def ObjTrue_def)
  have first_type:
    "\<Gamma> \<turnstile>
      Forall \<sigma>
        (Imp
          (\<diamond>\<^sub>o (Eq \<sigma> (rename Suc X) (Var 0)))
          (Eq \<sigma> (rename Suc X) (Var 0))) : Prop"
    using first by (rule CEV_axiom_proves_formula)
  have second_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 Y
        (Imp
          (\<diamond>\<^sub>o (Eq \<sigma> (rename Suc X) (Var 0)))
          (Eq \<sigma> (rename Suc X) (Var 0)))"
    using first_type Y_type first
    by (rule CEV_axiom_UI_typed)
  have cancel_X_Y:
    "subst (case_nat Y Var) (rename Suc X) = X"
    using subst0_shift[of Y X]
    unfolding subst0_def shift_def .
  show ?thesis
    using second_raw
    by (simp add: subst0_def ObjDiamond_def ObjBox_def ObjTrue_def
        cancel_X_Y)
qed

lemma CEV_Goodman_T3_possible_identity_parameter:
  assumes qss: "pp_QSS \<in> T"
    and persistence: "pp_persistence pp_unary_ty \<in> T"
    and x_type: "\<Gamma> \<turnstile> x : Prop"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (\<diamond>\<^sub>o (pp_fun Prop x))
      (Imp
        (Conj
          (pp_pure pp_unary_ty X)
          (pp_pure pp_unary_ty Y))
        (Imp
          (Eq Prop (App X x) (App Y x))
          (\<diamond>\<^sub>o (Eq pp_unary_ty X Y))))"
proof -
  let ?PX = "pp_pure pp_unary_ty X"
  let ?PY = "pp_pure pp_unary_ty Y"
  let ?F = "pp_fun Prop x"
  let ?E = "Eq Prop (App X x) (App Y x)"
  let ?I = "Eq pp_unary_ty X Y"
  let ?D = "\<diamond>\<^sub>o ?F"
  let ?H = "Conj ?D (Conj ?PX (Conj ?PY ?E))"
  have PX_type: "\<Gamma> \<turnstile> ?PX : Prop"
    using X_type by (rule typed_pp_pure)
  have PY_type: "\<Gamma> \<turnstile> ?PY : Prop"
    using Y_type by (rule typed_pp_pure)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using x_type by (rule typed_pp_fun)
  have app_X_type: "\<Gamma> \<turnstile> App X x : Prop"
    using X_type x_type
    unfolding pp_unary_ty_def
    by (rule has_type.App)
  have app_Y_type: "\<Gamma> \<turnstile> App Y x : Prop"
    using Y_type x_type
    unfolding pp_unary_ty_def
    by (rule has_type.App)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using app_X_type app_Y_type by (rule has_type.Eq)
  have I_type: "\<Gamma> \<turnstile> ?I : Prop"
    using X_type Y_type by (rule has_type.Eq)
  have D_type: "\<Gamma> \<turnstile> ?D : Prop"
    using F_type by (rule typed_ObjDiamond)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using D_type PX_type PY_type E_type
    by (intro has_type.Conj)
  have qss_instance:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_QSS_instance X Y x"
    using qss X_type Y_type x_type
    by (rule pp_axiom_QSS_instance)
  have reorder:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (pp_QSS_instance X Y x)
        (Imp ?PX (Imp ?PY (Imp ?E (Imp ?F ?I))))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (pp_QSS_instance X Y x)
        (Imp ?PX (Imp ?PY (Imp ?E (Imp ?F ?I)))))"
      unfolding prop_tautology_def pp_QSS_instance_def
      using PX_type PY_type F_type E_type I_type
      by (auto simp: prop_eval.simps
          intro!: has_type.Imp has_type.Conj)
  qed
  have curried:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?PX (Imp ?PY (Imp ?E (Imp ?F ?I)))"
    using qss_instance CEV_axiom_proves.Base[OF reorder]
    by (rule CEV_axiom_proves.MP)
  have box_curried:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o
        (Imp ?PX (Imp ?PY (Imp ?E (Imp ?F ?I))))"
    using CEV_axiom_necessitation[OF curried]
    by (rule CEV_axiom_from.Theorem)
  have d_H:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using H_type by (intro CEV_axiom_from.Assumption) simp
  have d_D:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?D"
    using d_H by (rule CEV_axiom_from_conj_left)
  have d_tail:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj ?PX (Conj ?PY ?E)"
    using d_H by (rule CEV_axiom_from_conj_right)
  have d_PX:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PX"
    using d_tail by (rule CEV_axiom_from_conj_left)
  have d_tail2:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj ?PY ?E"
    using d_tail by (rule CEV_axiom_from_conj_right)
  have d_PY:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PY"
    using d_tail2 by (rule CEV_axiom_from_conj_left)
  have d_E:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using d_tail2 by (rule CEV_axiom_from_conj_right)
  have persistence_X:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?PX (\<box>\<^sub>o ?PX)"
    using pp_axiom_persistence_imp[OF persistence X_type]
    by (rule CEV_axiom_from.Theorem)
  have persistence_Y:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?PY (\<box>\<^sub>o ?PY)"
    using pp_axiom_persistence_imp[OF persistence Y_type]
    by (rule CEV_axiom_from.Theorem)
  have box_PX:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o ?PX"
    using d_PX persistence_X by (rule CEV_axiom_from.MP)
  have box_PY:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o ?PY"
    using d_PY persistence_Y by (rule CEV_axiom_from.MP)
  have NI_E:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?E (\<box>\<^sub>o ?E)"
    using CEV_eq_truth_of_eq[OF app_X_type app_Y_type]
    unfolding ObjBox_def
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have box_E:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o ?E"
    using d_E NI_E by (rule CEV_axiom_from.MP)
  have box_after_X:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (Imp ?PY (Imp ?E (Imp ?F ?I)))"
    using PX_type
      has_type.Imp[OF PY_type
        has_type.Imp[OF E_type has_type.Imp[OF F_type I_type]]]
      box_curried box_PX
    by (rule CEV_axiom_from_box_MP)
  have box_after_Y:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (Imp ?E (Imp ?F ?I))"
    using PY_type
      has_type.Imp[OF E_type has_type.Imp[OF F_type I_type]]
      box_after_X box_PY
    by (rule CEV_axiom_from_box_MP)
  have box_F_imp_I:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (Imp ?F ?I)"
    using E_type has_type.Imp[OF F_type I_type]
      box_after_Y box_E
    by (rule CEV_axiom_from_box_MP)
  have diamond_I:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<diamond>\<^sub>o ?I"
    using F_type I_type box_F_imp_I d_D
    by (rule CEV_axiom_from_diamond_MP)
  have diamond_I_type:
    "\<Gamma> \<turnstile> \<diamond>\<^sub>o ?I : Prop"
    using I_type by (rule typed_ObjDiamond)
  have H_imp_diamond_I:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?H (\<diamond>\<^sub>o ?I)"
    using H_type diamond_I
    by (rule CEV_axiom_from_singleton_imp)
  have finish:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp ?H (\<diamond>\<^sub>o ?I))
        (Imp ?D
          (Imp
            (Conj ?PX ?PY)
            (Imp ?E (\<diamond>\<^sub>o ?I))))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp ?H (\<diamond>\<^sub>o ?I))
        (Imp ?D
          (Imp
            (Conj ?PX ?PY)
            (Imp ?E (\<diamond>\<^sub>o ?I)))))"
      unfolding prop_tautology_def
      using D_type PX_type PY_type E_type diamond_I_type H_type
      by (auto simp: prop_eval.simps
          intro!: has_type.Imp has_type.Conj)
  qed
  show ?thesis
    using H_imp_diamond_I CEV_axiom_proves.Base[OF finish]
    by (rule CEV_axiom_proves.MP)
qed

lemma CEV_Goodman_T3_repaired_parameter:
  assumes qss: "pp_QSS \<in> T"
    and persistence: "pp_persistence pp_unary_ty \<in> T"
    and pia:
      "pp_possible_identity_actual pp_unary_ty \<in> T"
    and x_type: "\<Gamma> \<turnstile> x : Prop"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (\<diamond>\<^sub>o (pp_fun Prop x))
      (Imp
        (Conj
          (pp_pure pp_unary_ty X)
          (pp_pure pp_unary_ty Y))
        (Imp
          (Eq Prop (App X x) (App Y x))
          (Eq pp_unary_ty X Y)))"
proof -
  let ?D = "\<diamond>\<^sub>o (pp_fun Prop x)"
  let ?P = "Conj
    (pp_pure pp_unary_ty X)
    (pp_pure pp_unary_ty Y)"
  let ?E = "Eq Prop (App X x) (App Y x)"
  let ?I = "Eq pp_unary_ty X Y"
  have possible:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?D (Imp ?P (Imp ?E (\<diamond>\<^sub>o ?I)))"
    using CEV_Goodman_T3_possible_identity_parameter[
      OF qss persistence x_type X_type Y_type] .
  have actual:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<diamond>\<^sub>o ?I) ?I"
    using pp_axiom_possible_identity_actual_instance[
      OF pia X_type Y_type] .
  have D_type: "\<Gamma> \<turnstile> ?D : Prop"
    using typed_pp_fun[OF x_type] by (rule typed_ObjDiamond)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_pure[OF X_type] typed_pp_pure[OF Y_type]
    by (rule has_type.Conj)
  have app_X_type: "\<Gamma> \<turnstile> App X x : Prop"
    using X_type x_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have app_Y_type: "\<Gamma> \<turnstile> App Y x : Prop"
    using Y_type x_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using app_X_type app_Y_type by (rule has_type.Eq)
  have I_type: "\<Gamma> \<turnstile> ?I : Prop"
    using X_type Y_type by (rule has_type.Eq)
  have diamond_I_type: "\<Gamma> \<turnstile> \<diamond>\<^sub>o ?I : Prop"
    using I_type by (rule typed_ObjDiamond)
  have compose:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp ?D (Imp ?P (Imp ?E (\<diamond>\<^sub>o ?I))))
        (Imp
          (Imp (\<diamond>\<^sub>o ?I) ?I)
          (Imp ?D (Imp ?P (Imp ?E ?I))))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp ?D (Imp ?P (Imp ?E (\<diamond>\<^sub>o ?I))))
        (Imp
          (Imp (\<diamond>\<^sub>o ?I) ?I)
          (Imp ?D (Imp ?P (Imp ?E ?I)))))"
      unfolding prop_tautology_def
      using D_type P_type E_type I_type diamond_I_type
      by (auto simp: prop_eval.simps
          intro!: has_type.Imp has_type.Conj)
  qed
  have step:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Imp (\<diamond>\<^sub>o ?I) ?I)
        (Imp ?D (Imp ?P (Imp ?E ?I)))"
    using possible CEV_axiom_proves.Base[OF compose]
    by (rule CEV_axiom_proves.MP)
  show ?thesis
    using actual step by (rule CEV_axiom_proves.MP)
qed

theorem CEV_Goodman_T3_repaired_at:
  assumes qss: "pp_QSS \<in> T"
    and persistence: "pp_persistence pp_unary_ty \<in> T"
    and pia:
      "pp_possible_identity_actual pp_unary_ty \<in> T"
    and x_type: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (\<diamond>\<^sub>o (pp_fun Prop x))
      (pp_fun_prime x)"
proof -
  let ?P = "\<diamond>\<^sub>o (pp_fun Prop x)"
  let ?body =
    "Imp
      (Conj
        (pp_pure pp_unary_ty (Var 1))
        (pp_pure pp_unary_ty (Var 0)))
      (Imp
        (Eq Prop
          (App (Var 1) (shift_by 2 x))
          (App (Var 0) (shift_by 2 x)))
        (Eq pp_unary_ty (Var 1) (Var 0)))"
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_fun[OF x_type] by (rule typed_ObjDiamond)
  have body_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile> ?body : Prop"
    using typed_pp_fun_prime[OF x_type]
    unfolding pp_fun_prime_def
    by (auto elim: has_type.cases)
  have inner_body_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      Forall pp_unary_ty ?body : Prop"
    using body_type by (rule has_type.Forall)
  have x_shift2_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile>
      shift_by 2 x : Prop"
  proof -
    have "[pp_unary_ty, pp_unary_ty] @ \<Gamma> \<turnstile>
      shift_by (length [pp_unary_ty, pp_unary_ty]) x : Prop"
      using x_type by (rule shift_by_preserves_typing)
    then show ?thesis by (simp add: numeral_2_eq_2)
  qed
  have X_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile>
      Var 1 : pp_unary_ty"
    by (rule has_type.Var) (simp add: lookup_def)
  have Y_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile>
      Var 0 : pp_unary_ty"
    by (rule typed_var0)
  have deepest:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T
      \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (\<diamond>\<^sub>o
          (pp_fun Prop (shift_by 2 x)))
        ?body"
    using CEV_Goodman_T3_repaired_parameter[
      OF qss persistence pia x_shift2_type X_type Y_type]
    by simp
  have ren2_x:
    "rename (Suc \<circ> Suc) x =
      rename (shift_ren 2 0) x"
    using shift_shift_eq_shift_by_2[of x]
    by (simp add: shift_def shift_by_def rename_comp)
  have deepest_shifted:
    "pp_unary_ty # pp_unary_ty # \<Gamma> ; T
      \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (shift ?P)) ?body"
    using deepest
    by (simp add: shift_def shift_by_def pp_fun_def pp_Fun_def
        ObjDiamond_def ObjBox_def ObjTrue_def rename_comp ren2_x)
  have inner:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (shift ?P)
        (Forall pp_unary_ty ?body)"
  proof (rule CEV_axiom_proves.Gen)
    show "pp_unary_ty # \<Gamma> \<turnstile> shift ?P : Prop"
      using P_type by (rule typed_shift_ctx)
    show "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile>
      ?body : Prop"
      by (rule body_type)
    show "pp_unary_ty # pp_unary_ty # \<Gamma> ; T
      \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (shift ?P)) ?body"
      by (rule deepest_shifted)
  qed
  have outer:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P
        (Forall pp_unary_ty
          (Forall pp_unary_ty ?body))"
  proof (rule CEV_axiom_proves.Gen)
    show "\<Gamma> \<turnstile> ?P : Prop"
      by (rule P_type)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      Forall pp_unary_ty ?body : Prop"
      by (rule inner_body_type)
    show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (shift ?P)
        (Forall pp_unary_ty ?body)"
      by (rule inner)
  qed
  show ?thesis
    using outer unfolding pp_fun_prime_def .
qed

theorem CEV_Goodman_T3_repaired_from:
  assumes qss: "pp_QSS \<in> T"
    and persistence: "pp_persistence pp_unary_ty \<in> T"
    and pia:
      "pp_possible_identity_actual pp_unary_ty \<in> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_T3_heredity"
proof -
  let ?Q =
    "Imp
      (\<diamond>\<^sub>o (pp_fun Prop (Var 0)))
      (pp_fun_prime (Var 0))"
  have body:
    "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ ?Q"
    using CEV_Goodman_T3_repaired_at[
      OF qss persistence pia
        typed_var0[where \<sigma> = Prop and \<Gamma> = "[]"]]
    .
  have Q_type: "[Prop] \<turnstile> ?Q : Prop"
    using typed_pp_fun[OF
      typed_var0[where \<sigma> = Prop and \<Gamma> = "[]"]]
      typed_pp_fun_prime[OF
        typed_var0[where \<sigma> = Prop and \<Gamma> = "[]"]]
    by (intro has_type.Imp typed_ObjDiamond)
  have guarded:
    "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue ?Q"
    using typed_ObjTrue body by (rule CEV_axiom_imp_of_right)
  have generalized_imp:
    "[] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue (Forall Prop ?Q)"
  proof (rule CEV_axiom_proves.Gen)
    show "[] \<turnstile> ObjTrue : Prop"
      by (rule typed_ObjTrue)
    show "[Prop] \<turnstile> ?Q : Prop"
      by (rule Q_type)
    show "[Prop] ; T
      \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ObjTrue) ?Q"
      using guarded by (simp add: ObjTrue_def shift_def)
  qed
  have d_true:
    "[] ; T \<turnstile>\<^sub>CEV\<^sup>+
      ObjTrue"
    by (rule CEV_axiom_proves_ObjTrue)
  have generalized:
    "[] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall Prop ?Q"
    using d_true generalized_imp by (rule CEV_axiom_proves.MP)
  show ?thesis
    using generalized unfolding pp_T3_heredity_def .
qed

corollary CEV_Goodman_T3_repaired:
  "[] ; pp_T3_repaired_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_T3_heredity"
proof (rule CEV_Goodman_T3_repaired_from)
  show "pp_QSS \<in> pp_T3_repaired_axioms"
    unfolding pp_T3_repaired_axioms_def pp_T3_axioms_def by blast
  show "pp_persistence pp_unary_ty \<in>
      pp_T3_repaired_axioms"
    unfolding pp_T3_repaired_axioms_def pp_T3_axioms_def
      pp_persistence_schema_def
    by blast
  show "pp_possible_identity_actual pp_unary_ty \<in>
      pp_T3_repaired_axioms"
    unfolding pp_T3_repaired_axioms_def by blast
qed

text \<open>
  Goodman's advertised formal target is:

  \<open>[] ; pp_T3_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_T3_heredity\<close>.

  Necessitated QSS plus Persistence proves only possible operator identity,
  as \<open>CEV_Goodman_T3_possible_identity_parameter\<close> records.  The final
  passage from \<open>\<diamond>(X = Y)\<close> to \<open>X = Y\<close> is not supplied by S4:
  classically it is the contrapositive of Necessity of Distinctness at the
  operator type.

  \<open>CEV_Goodman_T3_repaired\<close> proves the target after adding that unrestricted
  operator-level principle.  The sharper developments imported downstream
  prove two better-calibrated versions: zeroary Exhaustion suffices because
  identities between pure operators are pure propositions, and the strictly
  weaker principle of rigidity for identities between pure operators suffices
  directly.  They also show that unrestricted identity rigidity is
  incompatible with the existing \<open>fun\<acute>\<close> consequences.  Thus Goodman's
  advertised premise list omits a genuine rigidity assumption.
\<close>

end
