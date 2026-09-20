theory Bacon_PP_Goodman_Higher_Type_Diagonal
  imports
    
    "Goodman_Legacy_04.Bacon_PP_Goodman_Heredity_Sharp"
    "Goodman_Legacy_04.Bacon_PP_Goodman_Fun_Prime_Axiom_Collapse"
begin

section \<open>Goodman T4: the higher-type diagonal\<close>

subsection \<open>Type-generic evaluation injectivity\<close>

definition pp_fun_prime_at :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_fun_prime_at \<sigma> x =
    Forall (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Forall (\<sigma> \<rightarrow>\<^sub>o Prop)
        (Imp
          (Conj
            (pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (Var 1))
            (pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (Var 0)))
          (Imp
            (Eq Prop
              (App (Var 1) (shift_by 2 x))
              (App (Var 0) (shift_by 2 x)))
            (Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Var 1) (Var 0)))))"

lemma pp_fun_prime_as_generic:
  "pp_fun_prime p = pp_fun_prime_at Prop p"
  by (simp add: pp_fun_prime_def pp_fun_prime_at_def pp_unary_ty_def)

lemma typed_pp_fun_prime_at:
  assumes x_type: "\<Gamma> \<turnstile> x : \<sigma>"
  shows "\<Gamma> \<turnstile> pp_fun_prime_at \<sigma> x : Prop"
proof -
  let ?P = "\<sigma> \<rightarrow>\<^sub>o Prop"
  have x_shift:
    "?P # ?P # \<Gamma> \<turnstile> shift_by 2 x : \<sigma>"
  proof -
    have "[?P, ?P] @ \<Gamma> \<turnstile>
      shift_by (length [?P, ?P]) x : \<sigma>"
      using x_type by (rule shift_by_preserves_typing)
    then show ?thesis by (simp add: numeral_2_eq_2)
  qed
  have X_type: "?P # ?P # \<Gamma> \<turnstile> Var 1 : ?P"
    by (rule has_type.Var) (simp add: lookup_def)
  have Y_type: "?P # ?P # \<Gamma> \<turnstile> Var 0 : ?P"
    by (rule typed_var0)
  have Xx_type:
    "?P # ?P # \<Gamma> \<turnstile> App (Var 1) (shift_by 2 x) : Prop"
    using X_type x_shift by (rule has_type.App)
  have Yx_type:
    "?P # ?P # \<Gamma> \<turnstile> App (Var 0) (shift_by 2 x) : Prop"
    using Y_type x_shift by (rule has_type.App)
  show ?thesis
    unfolding pp_fun_prime_at_def
    using typed_pp_pure[OF X_type] typed_pp_pure[OF Y_type]
      Xx_type Yx_type X_type Y_type
    by (intro has_type.Forall has_type.Imp has_type.Conj has_type.Eq)
qed

lemma CEV_axiom_from_fun_prime_at:
  assumes x_type: "\<Gamma> \<turnstile> x : \<sigma>"
    and A_type: "\<Gamma> \<turnstile> A : \<sigma> \<rightarrow>\<^sub>o Prop"
    and B_type: "\<Gamma> \<turnstile> B : \<sigma> \<rightarrow>\<^sub>o Prop"
    and fun_x:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime_at \<sigma> x"
    and pure_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) A"
    and pure_B:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) B"
    and same_value:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App A x) (App B x)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq (\<sigma> \<rightarrow>\<^sub>o Prop) A B"
proof -
  let ?P = "\<sigma> \<rightarrow>\<^sub>o Prop"
  have outer_raw:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 A
        (Forall ?P
          (Imp
            (Conj
              (pp_pure ?P (Var 1))
              (pp_pure ?P (Var 0)))
            (Imp
              (Eq Prop
                (App (Var 1) (shift_by 2 x))
                (App (Var 0) (shift_by 2 x)))
              (Eq ?P (Var 1) (Var 0)))))"
  proof (rule CEV_axiom_from_UI_typed)
    show "\<Gamma> \<turnstile>
      Forall ?P
        (Forall ?P
          (Imp
            (Conj
              (pp_pure ?P (Var 1))
              (pp_pure ?P (Var 0)))
            (Imp
              (Eq Prop
                (App (Var 1) (shift_by 2 x))
                (App (Var 0) (shift_by 2 x)))
              (Eq ?P (Var 1) (Var 0))))) : Prop"
      using typed_pp_fun_prime_at[OF x_type]
      unfolding pp_fun_prime_at_def .
    show "\<Gamma> \<turnstile> A : ?P" by (rule A_type)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall ?P
        (Forall ?P
          (Imp
            (Conj
              (pp_pure ?P (Var 1))
              (pp_pure ?P (Var 0)))
            (Imp
              (Eq Prop
                (App (Var 1) (shift_by 2 x))
                (App (Var 0) (shift_by 2 x)))
              (Eq ?P (Var 1) (Var 0)))))"
      using fun_x unfolding pp_fun_prime_at_def .
  qed
  have outer:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall ?P
        (Imp
          (Conj
            (pp_pure ?P (shift A))
            (pp_pure ?P (Var 0)))
          (Imp
            (Eq Prop
              (App (shift A) (shift x))
              (App (Var 0) (shift x)))
            (Eq ?P (shift A) (Var 0))))"
    using outer_raw
    by (simp add: pp_fun_prime_at_def pp_pure_def pp_Pure_def
      subst0_def shift_by_def shift_ren_def shift_def
      subst_lift_shift_by_2)
  have outer_type:
    "\<Gamma> \<turnstile>
      Forall ?P
        (Imp
          (Conj
            (pp_pure ?P (shift A))
            (pp_pure ?P (Var 0)))
          (Imp
            (Eq Prop
              (App (shift A) (shift x))
              (App (Var 0) (shift x)))
            (Eq ?P (shift A) (Var 0)))) : Prop"
    using outer by (rule CEV_axiom_from_formula)
  have inner_raw:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 B
        (Imp
          (Conj
            (pp_pure ?P (shift A))
            (pp_pure ?P (Var 0)))
          (Imp
            (Eq Prop
              (App (shift A) (shift x))
              (App (Var 0) (shift x)))
            (Eq ?P (shift A) (Var 0))))"
    using outer_type B_type outer by (rule CEV_axiom_from_UI_typed)
  have subst_A:
    "subst (case_nat B Var) (rename Suc A) = A"
    using subst0_shift[of B A]
    unfolding subst0_def shift_def .
  have subst_x:
    "subst (case_nat B Var) (rename Suc x) = x"
    using subst0_shift[of B x]
    unfolding subst0_def shift_def .
  have rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj
          (pp_pure ?P A)
          (pp_pure ?P B))
        (Imp
          (Eq Prop (App A x) (App B x))
          (Eq ?P A B))"
    using inner_raw
    by (simp add: pp_pure_def pp_Pure_def subst0_def shift_def
      subst_A subst_x)
  have pair:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_pure ?P A) (pp_pure ?P B)"
    using pure_A pure_B by (rule CEV_axiom_from_conj_intro)
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Eq Prop (App A x) (App B x))
        (Eq ?P A B)"
    using pair rule by (rule CEV_axiom_from.MP)
  show ?thesis
    using same_value step by (rule CEV_axiom_from.MP)
qed

subsection \<open>The diagonal and its witness properties\<close>

definition pp_T4_C_ty :: otype where
  "pp_T4_C_ty = Prop \<rightarrow>\<^sub>o pp_unary_ty"

definition pp_T4_pred_ty :: otype where
  "pp_T4_pred_ty = pp_unary_ty \<rightarrow>\<^sub>o Prop"

definition pp_T4_axioms :: "oterm set" where
  "pp_T4_axioms =
    pp_purity_schema \<union> pp_application_closure_schema"

definition pp_T4_diagonal_builder :: oterm where
  "pp_T4_diagonal_builder =
    Lam pp_T4_C_ty
      (Lam Prop
        (Neg
          (App
            (App (Var 1) (Var 0))
            (Var 0))))"

definition pp_T4_diagonal :: "oterm \<Rightarrow> oterm" where
  "pp_T4_diagonal C = App pp_T4_diagonal_builder C"

definition pp_T4_eq_predicate :: "oterm \<Rightarrow> oterm" where
  "pp_T4_eq_predicate C =
    App (pp_eq_builder pp_unary_ty) (pp_T4_diagonal C)"

definition pp_T4_false_predicate :: oterm where
  "pp_T4_false_predicate = Lam pp_unary_ty ObjFalse"

lemma typed_pp_T4_diagonal_builder:
  "\<Gamma> \<turnstile> pp_T4_diagonal_builder :
    pp_T4_C_ty \<rightarrow>\<^sub>o pp_unary_ty"
  unfolding pp_T4_diagonal_builder_def pp_T4_C_ty_def pp_unary_ty_def
  by (intro has_type.Lam has_type.Neg has_type.App has_type.Var)
    (simp_all add: lookup_def)

lemma typed_pp_T4_diagonal:
  assumes C_type: "\<Gamma> \<turnstile> C : pp_T4_C_ty"
  shows "\<Gamma> \<turnstile> pp_T4_diagonal C : pp_unary_ty"
  unfolding pp_T4_diagonal_def
  using typed_pp_T4_diagonal_builder C_type
  by (rule has_type.App)

lemma typed_pp_T4_eq_predicate:
  assumes C_type: "\<Gamma> \<turnstile> C : pp_T4_C_ty"
  shows "\<Gamma> \<turnstile> pp_T4_eq_predicate C : pp_T4_pred_ty"
  unfolding pp_T4_eq_predicate_def pp_T4_pred_ty_def
  using typed_pp_eq_builder typed_pp_T4_diagonal[OF C_type]
  by (rule has_type.App)

lemma typed_pp_T4_false_predicate:
  "\<Gamma> \<turnstile> pp_T4_false_predicate : pp_T4_pred_ty"
  unfolding pp_T4_false_predicate_def pp_T4_pred_ty_def
  using typed_ObjFalse by (rule has_type.Lam)

lemma pp_T4_diagonal_builder_purity_axiom:
  "pp_pure
      (pp_T4_C_ty \<rightarrow>\<^sub>o pp_unary_ty)
      pp_T4_diagonal_builder
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_T4_diagonal_builder :
      pp_T4_C_ty \<rightarrow>\<^sub>o pp_unary_ty"
    by (rule typed_pp_T4_diagonal_builder)
  show "consts_of pp_T4_diagonal_builder = {}"
    by (simp add: pp_T4_diagonal_builder_def)
  show "pp_pure
      (pp_T4_C_ty \<rightarrow>\<^sub>o pp_unary_ty)
      pp_T4_diagonal_builder =
    pp_pure
      (pp_T4_C_ty \<rightarrow>\<^sub>o pp_unary_ty)
      pp_T4_diagonal_builder"
    by simp
qed

lemma pp_T4_false_predicate_purity_axiom:
  "pp_pure pp_T4_pred_ty pp_T4_false_predicate
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_T4_false_predicate : pp_T4_pred_ty"
    by (rule typed_pp_T4_false_predicate)
  show "consts_of pp_T4_false_predicate = {}"
    by (simp add: pp_T4_false_predicate_def ObjFalse_def ObjTrue_def)
  show "pp_pure pp_T4_pred_ty pp_T4_false_predicate =
    pp_pure pp_T4_pred_ty pp_T4_false_predicate"
    by simp
qed

lemma CEV_axiom_from_T4_pure_diagonal:
  assumes core: "pp_T4_axioms \<subseteq> T"
    and C_type: "\<Gamma> \<turnstile> C : pp_T4_C_ty"
    and pure_C:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_T4_C_ty C"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_unary_ty (pp_T4_diagonal C)"
proof -
  have closure:
    "pp_application_closure pp_T4_C_ty pp_unary_ty \<in> T"
    using core
    unfolding pp_T4_axioms_def pp_application_closure_schema_def
    by blast
  have builder_ax:
    "pp_pure
      (pp_T4_C_ty \<rightarrow>\<^sub>o pp_unary_ty)
      pp_T4_diagonal_builder \<in> T"
    using core pp_T4_diagonal_builder_purity_axiom
    unfolding pp_T4_axioms_def by blast
  have pure_builder:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure
        (pp_T4_C_ty \<rightarrow>\<^sub>o pp_unary_ty)
        pp_T4_diagonal_builder"
    using builder_ax typed_pp_pure[OF typed_pp_T4_diagonal_builder]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  show ?thesis
    unfolding pp_T4_diagonal_def
    using closure typed_pp_T4_diagonal_builder C_type
      pure_builder pure_C
    by (rule pp_axiom_application_closed_from)
qed

lemma CEV_axiom_from_T4_pure_eq_predicate:
  assumes core: "pp_T4_axioms \<subseteq> T"
    and C_type: "\<Gamma> \<turnstile> C : pp_T4_C_ty"
    and pure_D:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty (pp_T4_diagonal C)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_T4_pred_ty (pp_T4_eq_predicate C)"
proof -
  have closure:
    "pp_application_closure pp_unary_ty pp_T4_pred_ty \<in> T"
    using core
    unfolding pp_T4_axioms_def pp_application_closure_schema_def
    by blast
  have eq_ax:
    "pp_pure
      (pp_unary_ty \<rightarrow>\<^sub>o pp_T4_pred_ty)
      (pp_eq_builder pp_unary_ty) \<in> T"
    using core pp_eq_builder_purity_axiom
    unfolding pp_T4_axioms_def pp_T4_pred_ty_def
    by blast
  have eq_type:
    "\<Gamma> \<turnstile> pp_eq_builder pp_unary_ty :
      pp_unary_ty \<rightarrow>\<^sub>o pp_T4_pred_ty"
    unfolding pp_T4_pred_ty_def
    by (rule typed_pp_eq_builder)
  have pure_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure
        (pp_unary_ty \<rightarrow>\<^sub>o pp_T4_pred_ty)
        (pp_eq_builder pp_unary_ty)"
    using eq_ax typed_pp_pure[OF eq_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  show ?thesis
    unfolding pp_T4_eq_predicate_def
    using closure eq_type typed_pp_T4_diagonal[OF C_type]
      pure_eq pure_D
    by (rule pp_axiom_application_closed_from)
qed

lemma CEV_T4_pure_false_predicate:
  assumes core: "pp_T4_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_T4_pred_ty pp_T4_false_predicate"
proof -
  have ax:
    "pp_pure pp_T4_pred_ty pp_T4_false_predicate \<in> T"
    using core pp_T4_false_predicate_purity_axiom
    unfolding pp_T4_axioms_def by blast
  show ?thesis
    using ax typed_pp_pure[OF typed_pp_T4_false_predicate]
    by (rule CEV_axiom_proves.Axiom)
qed

subsection \<open>Beta laws for the diagonal and witnesses\<close>

definition pp_T4_diagonal_lambda :: "oterm \<Rightarrow> oterm" where
  "pp_T4_diagonal_lambda C =
    Lam Prop
      (Neg
        (App
          (App (shift C) (Var 0))
          (Var 0)))"

lemma typed_pp_T4_diagonal_lambda:
  assumes C_type: "\<Gamma> \<turnstile> C : pp_T4_C_ty"
  shows "\<Gamma> \<turnstile> pp_T4_diagonal_lambda C : pp_unary_ty"
proof -
  have shift_C:
    "Prop # \<Gamma> \<turnstile> shift C : pp_T4_C_ty"
    using C_type by (rule typed_shift_ctx)
  show ?thesis
    unfolding pp_T4_diagonal_lambda_def pp_T4_C_ty_def pp_unary_ty_def
    using shift_C[unfolded pp_T4_C_ty_def pp_unary_ty_def]
    by (intro has_type.Lam has_type.Neg has_type.App has_type.Var)
      (simp_all add: lookup_def)
qed

lemma pp_T4_diagonal_builder_beta:
  "compatible_step beta_contract
    (App pp_T4_diagonal_builder C)
    (pp_T4_diagonal_lambda C)"
proof -
  have step:
    "beta_contract
      (App
        (Lam pp_T4_C_ty
          (Lam Prop
            (Neg
              (App
                (App (Var 1) (Var 0))
                (Var 0)))))
        C)
      (subst0 C
        (Lam Prop
          (Neg
            (App
              (App (Var 1) (Var 0))
              (Var 0)))))"
    by (rule beta_contract.beta)
  show ?thesis
    using step
    by (intro compatible_step.root)
      (simp add: pp_T4_diagonal_builder_def
        pp_T4_diagonal_lambda_def subst0_def shift_def)
qed

lemma pp_T4_diagonal_apply_first_beta:
  "compatible_step beta_contract
    (App (pp_T4_diagonal C) q)
    (App (pp_T4_diagonal_lambda C) q)"
  unfolding pp_T4_diagonal_def
  using pp_T4_diagonal_builder_beta
  by (rule compatible_step.App_left)

lemma pp_T4_diagonal_apply_second_beta:
  "compatible_step beta_contract
    (App (pp_T4_diagonal_lambda C) q)
    (Neg (App (App C q) q))"
proof -
  have step:
    "beta_contract
      (App
        (Lam Prop
          (Neg
            (App
              (App (shift C) (Var 0))
              (Var 0))))
        q)
      (subst0 q
        (Neg
          (App
            (App (shift C) (Var 0))
            (Var 0))))"
    by (rule beta_contract.beta)
  show ?thesis
    using step
    by (intro compatible_step.root)
      (simp add: pp_T4_diagonal_lambda_def subst0_def shift_def
        subst0_shift[of q C, unfolded subst0_def shift_def])
qed

lemma CEV_pp_T4_diagonal_apply_eq:
  assumes C_type: "\<Gamma> \<turnstile> C : pp_T4_C_ty"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop
      (App (pp_T4_diagonal C) q)
      (Neg (App (App C q) q))"
proof -
  let ?D = "pp_T4_diagonal C"
  let ?L = "pp_T4_diagonal_lambda C"
  let ?P = "App (App C q) q"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    using C_type by (rule typed_pp_T4_diagonal)
  have L_type: "\<Gamma> \<turnstile> ?L : pp_unary_ty"
    using C_type by (rule typed_pp_T4_diagonal_lambda)
  have Dq_type: "\<Gamma> \<turnstile> App ?D q : Prop"
    using D_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Lq_type: "\<Gamma> \<turnstile> App ?L q : Prop"
    using L_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Cq_type: "\<Gamma> \<turnstile> App C q : pp_unary_ty"
    using C_type q_type unfolding pp_T4_C_ty_def
    by (rule has_type.App)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using Cq_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have neg_P_type: "\<Gamma> \<turnstile> Neg ?P : Prop"
    using P_type by (rule has_type.Neg)
  have first_iff:
    "\<Gamma> \<turnstile>\<^sub>CEV (App ?D q \<longleftrightarrow>\<^sub>o App ?L q)"
    using Dq_type Lq_type pp_T4_diagonal_apply_first_beta
    by (rule CEV_beta_step)
  have first_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (App ?D q) (App ?L q)"
    using Dq_type Lq_type first_iff
    by (rule CEV_zeroary_equivalence)
  have second_iff:
    "\<Gamma> \<turnstile>\<^sub>CEV (App ?L q \<longleftrightarrow>\<^sub>o Neg ?P)"
    using Lq_type neg_P_type pp_T4_diagonal_apply_second_beta
    by (rule CEV_beta_step)
  have second_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (App ?L q) (Neg ?P)"
    using Lq_type neg_P_type second_iff
    by (rule CEV_zeroary_equivalence)
  show ?thesis
    using Dq_type Lq_type neg_P_type first_eq second_eq
    by (rule CEV_eq_trans_from)
qed

lemma CEV_pp_T4_eq_predicate_apply_eq:
  assumes C_type: "\<Gamma> \<turnstile> C : pp_T4_C_ty"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop
      (App (pp_T4_eq_predicate C) X)
      (Eq pp_unary_ty (pp_T4_diagonal C) X)"
  unfolding pp_T4_eq_predicate_def
  using typed_pp_T4_diagonal[OF C_type] X_type
  by (rule CEV_pp_eq_builder_apply_eq)

lemma pp_T4_false_predicate_beta:
  "compatible_step beta_contract
    (App pp_T4_false_predicate X)
    ObjFalse"
proof -
  have step:
    "beta_contract
      (App (Lam pp_unary_ty ObjFalse) X)
      (subst0 X ObjFalse)"
    by (rule beta_contract.beta)
  show ?thesis
    using step
    by (intro compatible_step.root)
      (simp add: pp_T4_false_predicate_def subst0_def
        ObjFalse_def ObjTrue_def)
qed

lemma CEV_pp_T4_false_predicate_apply_eq:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop (App pp_T4_false_predicate X) ObjFalse"
proof -
  have left_type:
    "\<Gamma> \<turnstile> App pp_T4_false_predicate X : Prop"
    using typed_pp_T4_false_predicate X_type
    unfolding pp_T4_pred_ty_def
    by (rule has_type.App)
  have iff:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App pp_T4_false_predicate X \<longleftrightarrow>\<^sub>o ObjFalse)"
    using left_type typed_ObjFalse pp_T4_false_predicate_beta
    by (rule CEV_beta_step)
  show ?thesis
    using left_type typed_ObjFalse iff
    by (rule CEV_zeroary_equivalence)
qed

subsection \<open>Evaluation respects predicate identity\<close>

definition pp_predicate_eval_at :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_predicate_eval_at \<sigma> x =
    Lam (\<sigma> \<rightarrow>\<^sub>o Prop)
      (App (Var 0) (shift x))"

lemma typed_pp_predicate_eval_at:
  assumes x_type: "\<Gamma> \<turnstile> x : \<sigma>"
  shows "\<Gamma> \<turnstile> pp_predicate_eval_at \<sigma> x :
    (\<sigma> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop"
  unfolding pp_predicate_eval_at_def
  using typed_shift_ctx[OF x_type]
  by (intro has_type.Lam has_type.App has_type.Var)
    (simp add: lookup_def)

lemma pp_predicate_eval_at_beta:
  "compatible_step beta_contract
    (App (pp_predicate_eval_at \<sigma> x) F)
    (App F x)"
proof -
  have step:
    "beta_contract
      (App
        (Lam (\<sigma> \<rightarrow>\<^sub>o Prop)
          (App (Var 0) (shift x)))
        F)
      (subst0 F (App (Var 0) (shift x)))"
    by (rule beta_contract.beta)
  show ?thesis
    using step
    by (intro compatible_step.root)
      (simp add: pp_predicate_eval_at_def subst0_def shift_def
        subst0_shift[of F x, unfolded subst0_def shift_def])
qed

lemma CEV_pp_predicate_eval_at_apply_eq:
  assumes x_type: "\<Gamma> \<turnstile> x : \<sigma>"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop
      (App (pp_predicate_eval_at \<sigma> x) F)
      (App F x)"
proof -
  have left_type:
    "\<Gamma> \<turnstile> App (pp_predicate_eval_at \<sigma> x) F : Prop"
    using typed_pp_predicate_eval_at[OF x_type] F_type
    by (rule has_type.App)
  have right_type: "\<Gamma> \<turnstile> App F x : Prop"
    using F_type x_type by (rule has_type.App)
  have iff:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App (pp_predicate_eval_at \<sigma> x) F
        \<longleftrightarrow>\<^sub>o App F x)"
    using left_type right_type pp_predicate_eval_at_beta
    by (rule CEV_beta_step)
  show ?thesis
    using left_type right_type iff
    by (rule CEV_zeroary_equivalence)
qed

lemma CEV_axiom_from_predicate_eq_at:
  assumes x_type: "\<Gamma> \<turnstile> x : \<sigma>"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
    and G_type: "\<Gamma> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o Prop"
    and FG:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq (\<sigma> \<rightarrow>\<^sub>o Prop) F G"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App F x) (App G x)"
proof -
  let ?E = "pp_predicate_eval_at \<sigma> x"
  have E_type:
    "\<Gamma> \<turnstile> ?E :
      (\<sigma> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop"
    using x_type by (rule typed_pp_predicate_eval_at)
  have EF_type: "\<Gamma> \<turnstile> App ?E F : Prop"
    using E_type F_type by (rule has_type.App)
  have EG_type: "\<Gamma> \<turnstile> App ?E G : Prop"
    using E_type G_type by (rule has_type.App)
  have Fx_type: "\<Gamma> \<turnstile> App F x : Prop"
    using F_type x_type by (rule has_type.App)
  have Gx_type: "\<Gamma> \<turnstile> App G x : Prop"
    using G_type x_type by (rule has_type.App)
  have eval_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?E F) (App ?E G)"
    using E_type F_type G_type FG
    by (rule CEV_axiom_from_eq_app_right)
  have beta_F:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?E F) (App F x)"
    using CEV_pp_predicate_eval_at_apply_eq[OF x_type F_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have beta_G:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?E G) (App G x)"
    using CEV_pp_predicate_eval_at_apply_eq[OF x_type G_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have beta_F_sym:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App F x) (App ?E F)"
    using EF_type Fx_type beta_F
    by (rule CEV_axiom_from_eq_sym)
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App F x) (App ?E G)"
    using Fx_type EF_type EG_type beta_F_sym eval_eq
    by (rule CEV_axiom_from_eq_trans)
  show ?thesis
    using Fx_type EG_type Gx_type step beta_G
    by (rule CEV_axiom_from_eq_trans)
qed

lemma CEV_axiom_eq_sym_plus:
  assumes A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and B_type: "\<Gamma> \<turnstile> B : \<sigma>"
    and AB: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> B A"
proof -
  have local_AB:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> A B"
    using AB by (rule CEV_axiom_from.Theorem)
  have local_BA:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> B A"
    using A_type B_type local_AB by (rule CEV_axiom_from_eq_sym)
  show ?thesis
    using local_BA CEV_axiom_from_empty_iff by blast
qed

lemma CEV_axiom_eq_trans_plus:
  assumes A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and B_type: "\<Gamma> \<turnstile> B : \<sigma>"
    and C_type: "\<Gamma> \<turnstile> C : \<sigma>"
    and AB: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> A B"
    and BC: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> B C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> A C"
proof -
  have local_AB:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> A B"
    using AB by (rule CEV_axiom_from.Theorem)
  have local_BC:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> B C"
    using BC by (rule CEV_axiom_from.Theorem)
  have local_AC:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> A C"
    using A_type B_type C_type local_AB local_BC
    by (rule CEV_axiom_from_eq_trans)
  show ?thesis
    using local_AC CEV_axiom_from_empty_iff by blast
qed

subsection \<open>The diagonal is not its value at the parameter\<close>

theorem CEV_T4_diagonal_neq_value:
  assumes C_type: "\<Gamma> \<turnstile> C : pp_T4_C_ty"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Neg
      (Eq pp_unary_ty
        (pp_T4_diagonal C)
        (App C r))"
proof -
  let ?D = "pp_T4_diagonal C"
  let ?X = "App C r"
  let ?P = "App ?X r"
  let ?H = "Eq pp_unary_ty ?D ?X"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    using C_type by (rule typed_pp_T4_diagonal)
  have X_type: "\<Gamma> \<turnstile> ?X : pp_unary_ty"
    using C_type r_type unfolding pp_T4_C_ty_def
    by (rule has_type.App)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using X_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using D_type X_type by (rule has_type.Eq)
  have d_H:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using H_type by (intro CEV_axiom_from.Assumption) simp
  have value_eq_raw:
    "\<Gamma> ; T ;
      {Eq (Prop \<rightarrow>\<^sub>o Prop) ?D ?X}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?D r) ?P"
    using r_type
      D_type[unfolded pp_unary_ty_def]
      X_type[unfolded pp_unary_ty_def]
      d_H[unfolded pp_unary_ty_def]
    by (rule CEV_axiom_from_predicate_eq_at[where \<sigma> = Prop])
  have value_eq:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?D r) ?P"
    using value_eq_raw by (simp add: pp_unary_ty_def)
  have diagonal:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?D r) (Neg ?P)"
    using CEV_pp_T4_diagonal_apply_eq[OF C_type r_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have value_eq_sym:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?P (App ?D r)"
  proof (rule CEV_axiom_from_eq_sym)
    show "\<Gamma> \<turnstile> App ?D r : Prop"
      using D_type r_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "\<Gamma> \<turnstile> ?P : Prop" by (rule P_type)
    show "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?D r) ?P"
      by (rule value_eq)
  qed
  have fixed:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?P (Neg ?P)"
  proof (rule CEV_axiom_from_eq_trans)
    show "\<Gamma> \<turnstile> ?P : Prop" by (rule P_type)
    show "\<Gamma> \<turnstile> App ?D r : Prop"
      using D_type r_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "\<Gamma> \<turnstile> Neg ?P : Prop"
      using P_type by (rule has_type.Neg)
    show "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?P (App ?D r)"
      by (rule value_eq_sym)
    show "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?D r) (Neg ?P)"
      by (rule diagonal)
  qed
  have not_fixed:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop ?P (Neg ?P))"
    using CEV_no_proposition_identical_to_its_negation[OF P_type]
    by (rule CEV_axiom_from.Theorem)
  have false:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using fixed not_fixed by (rule CEV_axiom_from_contradiction)
  have imp_false:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?H ObjFalse"
    using H_type false by (rule CEV_axiom_from_singleton_imp)
  have to_neg:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp ?H ObjFalse) (Neg ?H)"
    using CEV_proves_imp_false_to_neg[OF H_type]
    by (rule CEV_axiom_proves.Base)
  show ?thesis
    using imp_false to_neg by (rule CEV_axiom_proves.MP)
qed

theorem CEV_T4_witnesses_agree_at_value:
  assumes C_type: "\<Gamma> \<turnstile> C : pp_T4_C_ty"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop
      (App (pp_T4_eq_predicate C) (App C r))
      (App pp_T4_false_predicate (App C r))"
proof -
  let ?D = "pp_T4_diagonal C"
  let ?X = "App C r"
  let ?E = "Eq pp_unary_ty ?D ?X"
  let ?A = "App (pp_T4_eq_predicate C) ?X"
  let ?B = "App pp_T4_false_predicate ?X"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    using C_type by (rule typed_pp_T4_diagonal)
  have X_type: "\<Gamma> \<turnstile> ?X : pp_unary_ty"
    using C_type r_type unfolding pp_T4_C_ty_def
    by (rule has_type.App)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using D_type X_type by (rule has_type.Eq)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using typed_pp_T4_eq_predicate[OF C_type] X_type
    unfolding pp_T4_pred_ty_def
    by (rule has_type.App)
  have B_type: "\<Gamma> \<turnstile> ?B : Prop"
    using typed_pp_T4_false_predicate X_type
    unfolding pp_T4_pred_ty_def
    by (rule has_type.App)
  have A_eq_E:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?A ?E"
    using CEV_pp_T4_eq_predicate_apply_eq[OF C_type X_type]
    by (rule CEV_axiom_proves.Base)
  have not_E: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg ?E"
    using CEV_T4_diagonal_neq_value[OF C_type r_type] .
  have E_eq_false:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?E ObjFalse"
    using E_type not_E by (rule CEV_refuted_imp_eq_ObjFalse)
  have B_eq_false:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?B ObjFalse"
    using CEV_pp_T4_false_predicate_apply_eq[OF X_type]
    by (rule CEV_axiom_proves.Base)
  have false_eq_B:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ObjFalse ?B"
    using B_type typed_ObjFalse B_eq_false
    by (rule CEV_axiom_eq_sym_plus)
  have A_eq_false:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?A ObjFalse"
    using A_type E_type typed_ObjFalse A_eq_E E_eq_false
    by (rule CEV_axiom_eq_trans_plus)
  show ?thesis
    using A_type typed_ObjFalse B_type A_eq_false false_eq_B
    by (rule CEV_axiom_eq_trans_plus)
qed

theorem CEV_T4_witnesses_distinct:
  assumes C_type: "\<Gamma> \<turnstile> C : pp_T4_C_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Neg
      (Eq pp_T4_pred_ty
        (pp_T4_eq_predicate C)
        pp_T4_false_predicate)"
proof -
  let ?D = "pp_T4_diagonal C"
  let ?A = "pp_T4_eq_predicate C"
  let ?B = pp_T4_false_predicate
  let ?E = "Eq pp_unary_ty ?D ?D"
  let ?H = "Eq pp_T4_pred_ty ?A ?B"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    using C_type by (rule typed_pp_T4_diagonal)
  have A_type: "\<Gamma> \<turnstile> ?A : pp_T4_pred_ty"
    using C_type by (rule typed_pp_T4_eq_predicate)
  have B_type: "\<Gamma> \<turnstile> ?B : pp_T4_pred_ty"
    by (rule typed_pp_T4_false_predicate)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using D_type D_type by (rule has_type.Eq)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using A_type B_type by (rule has_type.Eq)
  have d_H:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using H_type by (intro CEV_axiom_from.Assumption) simp
  have at_D_raw:
    "\<Gamma> ; T ;
      {Eq (pp_unary_ty \<rightarrow>\<^sub>o Prop) ?A ?B}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?A ?D) (App ?B ?D)"
    using D_type
      A_type[unfolded pp_T4_pred_ty_def]
      B_type[unfolded pp_T4_pred_ty_def]
      d_H[unfolded pp_T4_pred_ty_def]
    by (rule CEV_axiom_from_predicate_eq_at[
      where \<sigma> = pp_unary_ty])
  have at_D:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?A ?D) (App ?B ?D)"
    using at_D_raw by (simp add: pp_T4_pred_ty_def)
  have A_eval:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?A ?D) ?E"
    using CEV_pp_T4_eq_predicate_apply_eq[OF C_type D_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have B_eval:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?B ?D) ObjFalse"
    using CEV_pp_T4_false_predicate_apply_eq[OF D_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have AD_type: "\<Gamma> \<turnstile> App ?A ?D : Prop"
    using A_type D_type unfolding pp_T4_pred_ty_def
    by (rule has_type.App)
  have BD_type: "\<Gamma> \<turnstile> App ?B ?D : Prop"
    using B_type D_type unfolding pp_T4_pred_ty_def
    by (rule has_type.App)
  have E_eq_AD:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?E (App ?A ?D)"
    using AD_type E_type A_eval
    by (rule CEV_axiom_from_eq_sym)
  have E_eq_BD:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?E (App ?B ?D)"
    using E_type AD_type BD_type E_eq_AD at_D
    by (rule CEV_axiom_from_eq_trans)
  have E_eq_false:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?E ObjFalse"
    using E_type BD_type typed_ObjFalse E_eq_BD B_eval
    by (rule CEV_axiom_from_eq_trans)
  have d_E:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using D_type
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base
      CEV_proves.CE CE_proves.C C_proves.H H_proves.Ref)
  have false:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using E_type typed_ObjFalse d_E E_eq_false
    by (rule CEV_axiom_from_eq_prop_elim)
  have imp_false:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?H ObjFalse"
    using H_type false by (rule CEV_axiom_from_singleton_imp)
  have to_neg:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp ?H ObjFalse) (Neg ?H)"
    using CEV_proves_imp_false_to_neg[OF H_type]
    by (rule CEV_axiom_proves.Base)
  show ?thesis
    using imp_false to_neg by (rule CEV_axiom_proves.MP)
qed

subsection \<open>The exact T4 refutation\<close>

theorem CEV_Goodman_T4_parameter:
  assumes core: "pp_T4_axioms \<subseteq> T"
    and C_type: "\<Gamma> \<turnstile> C : pp_T4_C_ty"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_pure pp_T4_C_ty C)
      (Neg
        (pp_fun_prime_at pp_unary_ty (App C r)))"
proof -
  let ?D = "pp_T4_diagonal C"
  let ?X = "App C r"
  let ?A = "pp_T4_eq_predicate C"
  let ?B = pp_T4_false_predicate
  let ?PC = "pp_pure pp_T4_C_ty C"
  let ?F = "pp_fun_prime_at pp_unary_ty ?X"
  let ?AB = "Eq pp_T4_pred_ty ?A ?B"
  let ?S = "insert ?F {?PC}"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    using C_type by (rule typed_pp_T4_diagonal)
  have X_type: "\<Gamma> \<turnstile> ?X : pp_unary_ty"
    using C_type r_type unfolding pp_T4_C_ty_def
    by (rule has_type.App)
  have A_type: "\<Gamma> \<turnstile> ?A : pp_T4_pred_ty"
    using C_type by (rule typed_pp_T4_eq_predicate)
  have B_type: "\<Gamma> \<turnstile> ?B : pp_T4_pred_ty"
    by (rule typed_pp_T4_false_predicate)
  have PC_type: "\<Gamma> \<turnstile> ?PC : Prop"
    using C_type by (rule typed_pp_pure)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using X_type by (rule typed_pp_fun_prime_at)
  have AB_type: "\<Gamma> \<turnstile> ?AB : Prop"
    using A_type B_type by (rule has_type.Eq)
  have d_PC:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PC"
    using PC_type by (intro CEV_axiom_from.Assumption) simp
  have d_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have pure_D:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?D"
    using core C_type d_PC
    by (rule CEV_axiom_from_T4_pure_diagonal)
  have pure_A:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_T4_pred_ty ?A"
    using core C_type pure_D
    by (rule CEV_axiom_from_T4_pure_eq_predicate)
  have pure_B:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_T4_pred_ty ?B"
    using CEV_T4_pure_false_predicate[OF core]
    by (rule CEV_axiom_from.Theorem)
  have same:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?A ?X) (App ?B ?X)"
    using CEV_T4_witnesses_agree_at_value[OF C_type r_type]
    by (rule CEV_axiom_from.Theorem)
  have AB_raw:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq (pp_unary_ty \<rightarrow>\<^sub>o Prop) ?A ?B"
    using X_type
      A_type[unfolded pp_T4_pred_ty_def]
      B_type[unfolded pp_T4_pred_ty_def]
      d_F
      pure_A[unfolded pp_T4_pred_ty_def]
      pure_B[unfolded pp_T4_pred_ty_def]
      same
    by (rule CEV_axiom_from_fun_prime_at[
      where \<sigma> = pp_unary_ty])
  have d_AB:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?AB"
    using AB_raw by (simp add: pp_T4_pred_ty_def)
  have not_AB:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?AB"
    using CEV_T4_witnesses_distinct[OF C_type]
    by (rule CEV_axiom_from.Theorem)
  have false:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_AB not_AB by (rule CEV_axiom_from_contradiction)
  have F_imp_false:
    "\<Gamma> ; T ; {?PC} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F ObjFalse"
    using F_type false by (rule CEV_axiom_from_deduction)
  have to_neg:
    "\<Gamma> ; T ; {?PC} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?F ObjFalse) (Neg ?F)"
    using CEV_proves_imp_false_to_neg[OF F_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have not_F:
    "\<Gamma> ; T ; {?PC} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?F"
    using F_imp_false to_neg by (rule CEV_axiom_from.MP)
  show ?thesis
    using PC_type not_F by (rule CEV_axiom_from_singleton_imp)
qed

definition pp_T4_no_higher_fun_prime :: "oterm \<Rightarrow> oterm" where
  "pp_T4_no_higher_fun_prime r =
    Forall pp_T4_C_ty
      (Imp
        (pp_pure pp_T4_C_ty (Var 0))
        (Neg
          (pp_fun_prime_at pp_unary_ty
            (App (Var 0) (shift r)))))"

lemma typed_pp_T4_no_higher_fun_prime:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> pp_T4_no_higher_fun_prime r : Prop"
proof -
  have C_type:
    "pp_T4_C_ty # \<Gamma> \<turnstile> Var 0 : pp_T4_C_ty"
    by (rule typed_var0)
  have r_shift:
    "pp_T4_C_ty # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have Cr_type:
    "pp_T4_C_ty # \<Gamma> \<turnstile>
      App (Var 0) (shift r) : pp_unary_ty"
    using C_type r_shift unfolding pp_T4_C_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_T4_no_higher_fun_prime_def
    using typed_pp_pure[OF C_type] typed_pp_fun_prime_at[OF Cr_type]
    by (intro has_type.Forall has_type.Imp has_type.Neg)
qed

theorem CEV_Goodman_T4:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; pp_T4_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_T4_no_higher_fun_prime r"
proof -
  let ?Q =
    "Imp
      (pp_pure pp_T4_C_ty (Var 0))
      (Neg
        (pp_fun_prime_at pp_unary_ty
          (App (Var 0) (shift r))))"
  have C_type:
    "pp_T4_C_ty # \<Gamma> \<turnstile> Var 0 : pp_T4_C_ty"
    by (rule typed_var0)
  have r_shift:
    "pp_T4_C_ty # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have body:
    "pp_T4_C_ty # \<Gamma> ; pp_T4_axioms \<turnstile>\<^sub>CEV\<^sup>+ ?Q"
    using CEV_Goodman_T4_parameter[
      OF subset_refl C_type r_shift]
    .
  have Q_type:
    "pp_T4_C_ty # \<Gamma> \<turnstile> ?Q : Prop"
    using body by (rule CEV_axiom_proves_formula)
  have guarded_raw:
    "pp_T4_C_ty # \<Gamma> ; pp_T4_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue ?Q"
    using typed_ObjTrue body
    by (rule CEV_axiom_imp_of_right)
  have guarded:
    "pp_T4_C_ty # \<Gamma> ; pp_T4_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ObjTrue) ?Q"
    using guarded_raw
    by (simp add: ObjTrue_def shift_def)
  have gen:
    "\<Gamma> ; pp_T4_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue (Forall pp_T4_C_ty ?Q)"
    using typed_ObjTrue Q_type guarded
    by (rule CEV_axiom_proves.Gen)
  have d_true:
    "\<Gamma> ; pp_T4_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjTrue"
    by (rule CEV_axiom_proves_ObjTrue)
  have result:
    "\<Gamma> ; pp_T4_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Forall pp_T4_C_ty ?Q"
    using d_true gen by (rule CEV_axiom_proves.MP)
  show ?thesis
    using result unfolding pp_T4_no_higher_fun_prime_def .
qed

corollary CEV_Goodman_T4_mono:
  assumes core: "pp_T4_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_T4_no_higher_fun_prime r"
  using CEV_Goodman_T4[OF r_type]
  by (rule CEV_axiom_proves_mono[OF _ core])

text \<open>
  This proves a stronger form of Goodman T4.  The theorem quantifies in the
  object language over every pure \<open>C : t \<rightarrow> (t \<rightarrow> t)\<close>; it does not
  require \<open>C\<close> to be a closed syntactic term.  It also does not use PP or
  \<open>fun\<acute>(r)\<close>.  Its exact closed nonlogical stock,
  \<open>pp_T4_axioms\<close>, is the purity schema together with application closure.
\<close>

end
