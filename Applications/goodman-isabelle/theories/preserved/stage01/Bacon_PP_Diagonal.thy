theory Bacon_PP_Diagonal
  imports 
    "Goodman_Legacy_01.Bacon_CEV_Axiom_Extension"
begin

section \<open>The PP diagonal in the axiom extension\<close>

subsection \<open>Closed logical combinators\<close>

definition pp_unary_ty :: otype where
  "pp_unary_ty = Prop \<rightarrow>\<^sub>o Prop"

definition pp_unary_classifier_ty :: otype where
  "pp_unary_classifier_ty = pp_unary_ty \<rightarrow>\<^sub>o Prop"

definition pp_constant_builder :: oterm where
  "pp_constant_builder = Lam Prop (Lam Prop (Var 1))"

definition pp_identity_operator :: oterm where
  "pp_identity_operator = Lam Prop (Var 0)"

definition pp_negation_operator :: oterm where
  "pp_negation_operator = Lam Prop (Neg (Var 0))"

text \<open>
  The closed logical term below sends a classifier \<open>Q\<close> of unary
  propositional operators to the operator
  \<open>\<lambda>p. \<not> Q (\<lambda>q. p)\<close>.
\<close>

definition pp_diagonal_builder :: oterm where
  "pp_diagonal_builder =
    Lam pp_unary_classifier_ty
      (Lam Prop
        (Neg
          (App (Var 1)
            (App pp_constant_builder (Var 0)))))"

definition pp_diagonal_operator :: oterm where
  "pp_diagonal_operator =
    App pp_diagonal_builder (pp_Pure pp_unary_ty)"

definition pp_constant_operator :: "oterm \<Rightarrow> oterm" where
  "pp_constant_operator P = App pp_constant_builder P"

definition pp_diagonal_lambda :: oterm where
  "pp_diagonal_lambda =
    Lam Prop
      (Neg
        (pp_pure pp_unary_ty
          (pp_constant_operator (Var 0))))"

definition pp_possible_constant_purity_body :: oterm where
  "pp_possible_constant_purity_body =
    Conj
      (pp_fun Prop (Var 0))
      (\<diamond>\<^sub>o
        (pp_pure pp_unary_ty
          (pp_constant_operator (Var 0))))"

definition pp_possible_constant_purity :: oterm where
  "pp_possible_constant_purity =
    Exists Prop pp_possible_constant_purity_body"

lemma typed_pp_constant_builder:
  "\<Gamma> \<turnstile> pp_constant_builder :
    Prop \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_constant_builder_def pp_unary_ty_def lookup_def)

lemma typed_pp_identity_operator:
  "\<Gamma> \<turnstile> pp_identity_operator : pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_identity_operator_def pp_unary_ty_def lookup_def)

lemma typed_pp_negation_operator:
  "\<Gamma> \<turnstile> pp_negation_operator : pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_negation_operator_def pp_unary_ty_def lookup_def)

lemma typed_pp_diagonal_builder:
  "\<Gamma> \<turnstile> pp_diagonal_builder :
    pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_diagonal_builder_def pp_unary_classifier_ty_def
      pp_unary_ty_def pp_constant_builder_def lookup_def)

lemma typed_pp_diagonal_operator:
  "\<Gamma> \<turnstile> pp_diagonal_operator : pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_diagonal_operator_def pp_diagonal_builder_def
      pp_unary_classifier_ty_def pp_unary_ty_def pp_Pure_def
      pp_constant_builder_def lookup_def)

lemma typed_pp_constant_operator:
  assumes "\<Gamma> \<turnstile> P : Prop"
  shows "\<Gamma> \<turnstile> pp_constant_operator P : pp_unary_ty"
  unfolding pp_constant_operator_def pp_unary_ty_def
proof (rule has_type.App)
  show "\<Gamma> \<turnstile> pp_constant_builder :
      Prop \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)"
    using typed_pp_constant_builder[of \<Gamma>]
    unfolding pp_unary_ty_def .
  show "\<Gamma> \<turnstile> P : Prop"
    by (rule assms)
qed

lemma typed_pp_diagonal_lambda:
  "\<Gamma> \<turnstile> pp_diagonal_lambda : pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_diagonal_lambda_def pp_unary_ty_def pp_pure_def
      pp_Pure_def pp_constant_operator_def pp_constant_builder_def
      lookup_def)

lemma typed_pp_possible_constant_purity_body:
  "Prop # \<Gamma> \<turnstile> pp_possible_constant_purity_body : Prop"
  by (rule infer_type_sound)
    (simp add: pp_possible_constant_purity_body_def pp_unary_ty_def
      pp_constant_operator_def pp_constant_builder_def pp_pure_def
      pp_Pure_def pp_fun_def pp_Fun_def ObjDiamond_def ObjBox_def
      ObjTrue_def lookup_def)

lemma typed_pp_possible_constant_purity:
  "\<Gamma> \<turnstile> pp_possible_constant_purity : Prop"
  unfolding pp_possible_constant_purity_def
  using typed_pp_possible_constant_purity_body
  by (rule has_type.Exists)

lemma consts_of_pp_constant_builder[simp]:
  "consts_of pp_constant_builder = {}"
  by (simp add: pp_constant_builder_def)

lemma consts_of_pp_identity_operator[simp]:
  "consts_of pp_identity_operator = {}"
  by (simp add: pp_identity_operator_def)

lemma consts_of_pp_negation_operator[simp]:
  "consts_of pp_negation_operator = {}"
  by (simp add: pp_negation_operator_def)

lemma consts_of_pp_diagonal_builder[simp]:
  "consts_of pp_diagonal_builder = {}"
  by (simp add: pp_diagonal_builder_def)

subsection \<open>Application closure as a derived rule\<close>

lemma pp_axiom_application_closed:
  assumes closure: "pp_application_closure \<sigma> \<tau> \<in> T"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and X_type: "\<Gamma> \<turnstile> X : \<sigma>"
    and pure_F:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F"
    and pure_X: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure \<sigma> X"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure \<tau> (App F X)"
proof -
  have closure_type:
    "\<Gamma> \<turnstile> pp_application_closure \<sigma> \<tau> : Prop"
    by (rule infer_type_sound)
      (simp add: pp_application_closure_def pp_pure_def pp_Pure_def
        lookup_def)
  have d_closure:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_application_closure \<sigma> \<tau>"
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
      using closure_type
      unfolding pp_application_closure_def .
  next
    show "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
      by (rule F_type)
  next
    show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>)
          (Forall \<sigma>
            (Imp
              (Conj
                (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Var 1))
                (pp_pure \<sigma> (Var 0)))
              (pp_pure \<tau> (App (Var 1) (Var 0)))))"
      using d_closure
      unfolding pp_application_closure_def .
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
  have d_inner:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Conj
          (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F)
          (pp_pure \<sigma> X))
        (pp_pure \<tau> (App F X))"
  proof -
    have subst_shift:
      "subst (case_nat X Var) (rename Suc F) = F"
      using subst0_shift[of X F]
      unfolding subst0_def shift_def .
    show ?thesis
      using d_inner_raw
      by (simp add: pp_pure_def pp_Pure_def subst0_def shift_def
          subst_shift)
  qed
  have d_pair:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Conj
        (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F)
        (pp_pure \<sigma> X)"
    using pure_F pure_X by (rule CEV_axiom_conj_intro)
  show ?thesis
    using d_pair d_inner by (rule CEV_axiom_proves.MP)
qed

subsection \<open>The diagonal is forced to be pure\<close>

lemma pp_constant_builder_purity_axiom:
  "pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty) pp_constant_builder
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_constant_builder :
      Prop \<rightarrow>\<^sub>o pp_unary_ty"
    by (rule typed_pp_constant_builder)
  show "consts_of pp_constant_builder = {}"
    by simp
  show "pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty) pp_constant_builder =
      pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty) pp_constant_builder"
    by simp
qed

lemma pp_identity_operator_purity_axiom:
  "pp_pure pp_unary_ty pp_identity_operator \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_identity_operator : pp_unary_ty"
    by (rule typed_pp_identity_operator)
  show "consts_of pp_identity_operator = {}"
    by simp
  show "pp_pure pp_unary_ty pp_identity_operator =
      pp_pure pp_unary_ty pp_identity_operator"
    by simp
qed

lemma pp_negation_operator_purity_axiom:
  "pp_pure pp_unary_ty pp_negation_operator \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_negation_operator : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  show "consts_of pp_negation_operator = {}"
    by simp
  show "pp_pure pp_unary_ty pp_negation_operator =
      pp_pure pp_unary_ty pp_negation_operator"
    by simp
qed

lemma pp_diagonal_builder_purity_axiom:
  "pp_pure (pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty)
      pp_diagonal_builder
    \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_diagonal_builder :
      pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty"
    by (rule typed_pp_diagonal_builder)
  show "consts_of pp_diagonal_builder = {}"
    by simp
  show "pp_pure (pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty)
      pp_diagonal_builder =
      pp_pure (pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty)
        pp_diagonal_builder"
    by simp
qed

lemma pp_ObjTrue_purity_axiom:
  "pp_pure Prop ObjTrue \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  show "consts_of ObjTrue = {}"
    by (simp add: ObjTrue_def)
  show "pp_pure Prop ObjTrue = pp_pure Prop ObjTrue"
    by simp
qed

lemma pp_purity_axiom_in_recombination:
  assumes "A \<in> pp_purity_schema"
  shows "A \<in> pp_recombination_PP_axioms"
  using assms
  unfolding pp_recombination_PP_axioms_def
    pp_recombination_background_axioms_def pp_background_axioms_def
  by blast

lemma pp_application_closure_in_recombination:
  "pp_application_closure \<sigma> \<tau> \<in> pp_recombination_PP_axioms"
  unfolding pp_recombination_PP_axioms_def
    pp_recombination_background_axioms_def pp_background_axioms_def
    pp_application_closure_schema_def
  by blast

lemma pp_target_in_recombination:
  "pp_target_PP \<in> pp_recombination_PP_axioms"
  by (rule pp_target_PP_is_assumed_recombination)

theorem pp_diagonal_operator_pure_recombination:
  "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty pp_diagonal_operator"
proof -
  have builder_axiom:
    "pp_pure (pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty)
        pp_diagonal_builder
      \<in> pp_recombination_PP_axioms"
    using pp_diagonal_builder_purity_axiom
    by (rule pp_purity_axiom_in_recombination)
  have builder_pure:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure (pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty)
        pp_diagonal_builder"
    using builder_axiom
      typed_pp_pure[OF typed_pp_diagonal_builder, of \<Gamma>]
    by (rule CEV_axiom_proves.Axiom)
  have classifier_pure:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_classifier_ty (pp_Pure pp_unary_ty)"
  proof -
    have target_type: "\<Gamma> \<turnstile> pp_target_PP : Prop"
      by (rule infer_type_sound)
        (simp add: pp_target_PP_def pp_purity_of_pure_def pp_pure_def
          pp_Pure_def pp_unary_ty_def lookup_def)
    have target:
      "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_target_PP"
      using pp_target_in_recombination target_type
      by (rule CEV_axiom_proves.Axiom)
    show ?thesis
      using target
      by (simp add: pp_target_PP_def pp_purity_of_pure_def
          pp_unary_classifier_ty_def pp_unary_ty_def)
  qed
  have closure:
    "pp_application_closure pp_unary_classifier_ty pp_unary_ty
      \<in> pp_recombination_PP_axioms"
    by (rule pp_application_closure_in_recombination)
  have classifier_type:
    "\<Gamma> \<turnstile> pp_Pure pp_unary_ty : pp_unary_classifier_ty"
    using typed_pp_Pure[of \<Gamma> pp_unary_ty]
    unfolding pp_unary_classifier_ty_def .
  show ?thesis
    unfolding pp_diagonal_operator_def
    using closure
      typed_pp_diagonal_builder[of \<Gamma>]
      classifier_type
      builder_pure classifier_pure
    by (rule pp_axiom_application_closed)
qed

corollary pp_diagonal_operator_pure_full_QLN:
  "\<Gamma> ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty pp_diagonal_operator"
  using pp_diagonal_operator_pure_recombination
    pp_recombination_PP_axioms_subset_full_QLN
  by (rule CEV_axiom_proves_mono)

lemma pp_ObjTrue_pure_recombination:
  "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure Prop ObjTrue"
proof -
  have axiom:
    "pp_pure Prop ObjTrue \<in> pp_recombination_PP_axioms"
    using pp_ObjTrue_purity_axiom
    by (rule pp_purity_axiom_in_recombination)
  show ?thesis
    using axiom typed_pp_pure[OF typed_ObjTrue, of \<Gamma>]
    by (rule CEV_axiom_proves.Axiom)
qed

lemma pp_constant_ObjTrue_pure_recombination:
  "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty (pp_constant_operator ObjTrue)"
proof -
  have builder_axiom:
    "pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty) pp_constant_builder
      \<in> pp_recombination_PP_axioms"
    using pp_constant_builder_purity_axiom
    by (rule pp_purity_axiom_in_recombination)
  have builder_pure:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure (Prop \<rightarrow>\<^sub>o pp_unary_ty) pp_constant_builder"
    using builder_axiom
      typed_pp_pure[OF typed_pp_constant_builder, of \<Gamma>]
    by (rule CEV_axiom_proves.Axiom)
  show ?thesis
    unfolding pp_constant_operator_def
    using pp_application_closure_in_recombination
      typed_pp_constant_builder[of \<Gamma>]
      typed_ObjTrue
      builder_pure
      pp_ObjTrue_pure_recombination
    by (rule pp_axiom_application_closed)
qed

subsection \<open>What Recombination says about the diagonal\<close>

lemma pp_unary_recombination_in_recombination:
  "pp_unary_recombination \<in> pp_recombination_PP_axioms"
  unfolding pp_recombination_PP_axioms_def
    pp_recombination_background_axioms_def
  by blast

lemma shift_pp_diagonal_operator[simp]:
  "shift pp_diagonal_operator = pp_diagonal_operator"
  by (simp add: shift_def pp_diagonal_operator_def pp_diagonal_builder_def
      pp_constant_builder_def pp_Pure_def pp_unary_ty_def
      pp_unary_classifier_ty_def)

lemma pp_diagonal_operator_first_beta:
  "compatible_step beta_contract
    (App pp_diagonal_operator P)
    (App pp_diagonal_lambda P)"
proof (rule compatible_step.App_left)
  show "compatible_step beta_contract
      pp_diagonal_operator pp_diagonal_lambda"
  proof (rule compatible_step.root)
    have step:
      "beta_contract
        (App
          (Lam pp_unary_classifier_ty
            (Lam Prop
              (Neg
                (App (Var 1)
                  (App pp_constant_builder (Var 0))))))
          (pp_Pure pp_unary_ty))
        (subst0 (pp_Pure pp_unary_ty)
          (Lam Prop
            (Neg
              (App (Var 1)
                (App pp_constant_builder (Var 0))))))"
      by (rule beta_contract.beta)
    show "beta_contract pp_diagonal_operator pp_diagonal_lambda"
      using step
      by (simp add: pp_diagonal_operator_def pp_diagonal_builder_def
          pp_diagonal_lambda_def pp_constant_operator_def
          pp_unary_classifier_ty_def pp_unary_ty_def pp_pure_def
          pp_Pure_def subst0_def pp_constant_builder_def)
  qed
qed

lemma pp_diagonal_operator_second_beta:
  "compatible_step beta_contract
    (App pp_diagonal_lambda P)
    (Neg
      (pp_pure pp_unary_ty
        (pp_constant_operator P)))"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam Prop
          (Neg
            (pp_pure pp_unary_ty
              (pp_constant_operator (Var 0)))))
        P)
      (subst0 P
        (Neg
          (pp_pure pp_unary_ty
            (pp_constant_operator (Var 0)))))"
    by (rule beta_contract.beta)
  show "beta_contract
      (App pp_diagonal_lambda P)
      (Neg
        (pp_pure pp_unary_ty
          (pp_constant_operator P)))"
    using step
    by (simp add: pp_diagonal_lambda_def pp_constant_operator_def
        pp_constant_builder_def pp_unary_ty_def pp_pure_def pp_Pure_def
        subst0_def)
qed

lemma pp_diagonal_operator_beta_eta:
  assumes P_type: "\<Gamma> \<turnstile> P : Prop"
  shows "beta_eta_equiv \<Gamma> Prop
    (App pp_diagonal_operator P)
    (Neg
      (pp_pure pp_unary_ty
        (pp_constant_operator P)))"
proof (rule beta_eta_equiv.Trans[
    where N = "App pp_diagonal_lambda P"])
  show "beta_eta_equiv \<Gamma> Prop
      (App pp_diagonal_operator P)
      (App pp_diagonal_lambda P)"
  proof (rule beta_eta_equiv.Beta)
    show "\<Gamma> \<turnstile> App pp_diagonal_operator P : Prop"
      using typed_pp_diagonal_operator[of \<Gamma>] P_type
      unfolding pp_unary_ty_def by auto
  next
    show "\<Gamma> \<turnstile> App pp_diagonal_lambda P : Prop"
      using typed_pp_diagonal_lambda[of \<Gamma>] P_type
      unfolding pp_unary_ty_def by auto
  next
    show "compatible_step beta_contract
        (App pp_diagonal_operator P)
        (App pp_diagonal_lambda P)"
      by (rule pp_diagonal_operator_first_beta)
  qed
next
  show "beta_eta_equiv \<Gamma> Prop
      (App pp_diagonal_lambda P)
      (Neg
        (pp_pure pp_unary_ty
          (pp_constant_operator P)))"
  proof (rule beta_eta_equiv.Beta)
    show "\<Gamma> \<turnstile> App pp_diagonal_lambda P : Prop"
      using typed_pp_diagonal_lambda[of \<Gamma>] P_type
      unfolding pp_unary_ty_def by auto
  next
    show "\<Gamma> \<turnstile>
        Neg
          (pp_pure pp_unary_ty
            (pp_constant_operator P)) : Prop"
      using typed_pp_pure[OF typed_pp_constant_operator[OF P_type]]
      by auto
  next
    show "compatible_step beta_contract
        (App pp_diagonal_lambda P)
        (Neg
          (pp_pure pp_unary_ty
            (pp_constant_operator P)))"
      by (rule pp_diagonal_operator_second_beta)
  qed
qed

lemma CEV_pp_diagonal_operator_imp_not_pure_constant:
  assumes P_type: "\<Gamma> \<turnstile> P : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp
      (App pp_diagonal_operator P)
      (Neg
        (pp_pure pp_unary_ty
          (pp_constant_operator P)))"
proof -
  have app_type: "\<Gamma> \<turnstile> App pp_diagonal_operator P : Prop"
    using typed_pp_diagonal_operator[of \<Gamma>] P_type
    unfolding pp_unary_ty_def by auto
  have neg_type:
    "\<Gamma> \<turnstile>
      Neg
        (pp_pure pp_unary_ty
          (pp_constant_operator P)) : Prop"
    using typed_pp_pure[OF typed_pp_constant_operator[OF P_type]]
    by auto
  have biconditional:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App pp_diagonal_operator P
        \<longleftrightarrow>\<^sub>o
       Neg
        (pp_pure pp_unary_ty
          (pp_constant_operator P)))"
    using pp_diagonal_operator_beta_eta[OF P_type]
    by (rule CEV_beta_eta_equiv)
  show ?thesis
    using app_type neg_type biconditional
    by (rule CEV_beta_left_imp)
qed

lemma pp_diagonal_recombination_instance:
  assumes R_type: "\<Gamma> \<turnstile> R : Prop"
  shows "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure pp_unary_ty pp_diagonal_operator)
        (pp_fun Prop R))
      (Imp
        (\<box>\<^sub>o (App pp_diagonal_operator R))
        (Forall Prop
          (App (shift pp_diagonal_operator) (Var 0))))"
proof -
  have qln_type: "\<Gamma> \<turnstile> pp_unary_recombination : Prop"
    by (rule infer_type_sound)
      (simp add: pp_unary_recombination_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)
  have d_qln:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_unary_recombination"
    using pp_unary_recombination_in_recombination qln_type
    by (rule CEV_axiom_proves.Axiom)
  have diagonal_type_raw:
    "\<Gamma> \<turnstile> pp_diagonal_operator : Prop \<rightarrow>\<^sub>o Prop"
    using typed_pp_diagonal_operator[of \<Gamma>]
    unfolding pp_unary_ty_def .
  have d_outer_raw:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      subst0 pp_diagonal_operator
        (Forall Prop
          (Imp
            (Conj
              (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
              (pp_fun Prop (Var 0)))
            (Imp
              (\<box>\<^sub>o (App (Var 1) (Var 0)))
              (Forall Prop (App (Var 2) (Var 0))))))"
  proof (rule CEV_axiom_UI_typed)
    show "\<Gamma> \<turnstile>
        Forall (Prop \<rightarrow>\<^sub>o Prop)
          (Forall Prop
            (Imp
              (Conj
                (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
                (pp_fun Prop (Var 0)))
              (Imp
                (\<box>\<^sub>o (App (Var 1) (Var 0)))
                (Forall Prop (App (Var 2) (Var 0)))))) : Prop"
      using qln_type unfolding pp_unary_recombination_def .
  next
    show "\<Gamma> \<turnstile> pp_diagonal_operator : Prop \<rightarrow>\<^sub>o Prop"
      by (rule diagonal_type_raw)
  next
    show "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Forall (Prop \<rightarrow>\<^sub>o Prop)
          (Forall Prop
            (Imp
              (Conj
                (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
                (pp_fun Prop (Var 0)))
              (Imp
                (\<box>\<^sub>o (App (Var 1) (Var 0)))
                (Forall Prop (App (Var 2) (Var 0))))))"
      using d_qln unfolding pp_unary_recombination_def .
  qed
  have d_outer:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty pp_diagonal_operator)
            (pp_fun Prop (Var 0)))
          (Imp
            (\<box>\<^sub>o (App pp_diagonal_operator (Var 0)))
            (Forall Prop
              (App (shift pp_diagonal_operator) (Var 0)))))"
    using d_outer_raw
    by (simp add: pp_unary_ty_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def subst0_def shift_def
        pp_diagonal_operator_def pp_diagonal_builder_def
        pp_constant_builder_def pp_unary_classifier_ty_def
        One_nat_def numeral_2_eq_2)
  have outer_type:
    "\<Gamma> \<turnstile>
      Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty pp_diagonal_operator)
            (pp_fun Prop (Var 0)))
          (Imp
            (\<box>\<^sub>o (App pp_diagonal_operator (Var 0)))
            (Forall Prop
              (App (shift pp_diagonal_operator) (Var 0))))) : Prop"
    using CEV_axiom_proves_formula[OF d_outer] .
  have d_inner_raw:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      subst0 R
        (Imp
          (Conj
            (pp_pure pp_unary_ty pp_diagonal_operator)
            (pp_fun Prop (Var 0)))
          (Imp
            (\<box>\<^sub>o (App pp_diagonal_operator (Var 0)))
            (Forall Prop
              (App (shift pp_diagonal_operator) (Var 0)))))"
    using outer_type R_type d_outer by (rule CEV_axiom_UI_typed)
  show ?thesis
    using d_inner_raw
    by (simp add: pp_unary_ty_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def subst0_def shift_def
        pp_diagonal_operator_def pp_diagonal_builder_def
        pp_constant_builder_def pp_unary_classifier_ty_def)
qed

lemma pp_diagonal_recombination_from_fundamental:
  assumes R_type: "\<Gamma> \<turnstile> R : Prop"
    and fundamental:
      "\<Gamma> ; pp_recombination_PP_axioms ; S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun Prop R"
  shows "\<Gamma> ; pp_recombination_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Imp
      (\<box>\<^sub>o (App pp_diagonal_operator R))
      (Forall Prop (App (shift pp_diagonal_operator) (Var 0)))"
proof -
  have pure_Gamma:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty pp_diagonal_operator"
    by (rule pp_diagonal_operator_pure_recombination)
  have pure_local:
    "\<Gamma> ; pp_recombination_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty pp_diagonal_operator"
    using pure_Gamma by (rule CEV_axiom_from.Theorem)
  have pair:
    "\<Gamma> ; pp_recombination_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty pp_diagonal_operator)
        (pp_fun Prop R)"
    using pure_local fundamental by (rule CEV_axiom_from_conj_intro)
  have qln_instance:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Conj
          (pp_pure pp_unary_ty pp_diagonal_operator)
          (pp_fun Prop R))
        (Imp
          (\<box>\<^sub>o (App pp_diagonal_operator R))
          (Forall Prop
            (App (shift pp_diagonal_operator) (Var 0))))"
    using R_type by (rule pp_diagonal_recombination_instance)
  have qln_instance_local:
    "\<Gamma> ; pp_recombination_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj
          (pp_pure pp_unary_ty pp_diagonal_operator)
          (pp_fun Prop R))
        (Imp
          (\<box>\<^sub>o (App pp_diagonal_operator R))
          (Forall Prop
            (App (shift pp_diagonal_operator) (Var 0))))"
    using qln_instance by (rule CEV_axiom_from.Theorem)
  show ?thesis
    using pair qln_instance_local by (rule CEV_axiom_from.MP)
qed

lemma pp_diagonal_local_contradiction:
  assumes R_type: "\<Gamma> \<turnstile> R : Prop"
    and fundamental:
      "\<Gamma> ; pp_recombination_PP_axioms ; S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun Prop R"
    and necessary_diagonal:
      "\<Gamma> ; pp_recombination_PP_axioms ; S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          (\<box>\<^sub>o (App pp_diagonal_operator R))"
  shows "\<Gamma> ; pp_recombination_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
proof -
  have recombination:
    "\<Gamma> ; pp_recombination_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (\<box>\<^sub>o (App pp_diagonal_operator R))
        (Forall Prop
          (App (shift pp_diagonal_operator) (Var 0)))"
    using R_type fundamental
    by (rule pp_diagonal_recombination_from_fundamental)
  have universal:
    "\<Gamma> ; pp_recombination_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall Prop
        (App (shift pp_diagonal_operator) (Var 0))"
    using necessary_diagonal recombination by (rule CEV_axiom_from.MP)
  have universal_type:
    "\<Gamma> \<turnstile>
      Forall Prop
        (App (shift pp_diagonal_operator) (Var 0)) : Prop"
    using universal by (rule CEV_axiom_from_formula)
  have diagonal_true_raw:
    "\<Gamma> ; pp_recombination_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 ObjTrue
        (App (shift pp_diagonal_operator) (Var 0))"
    using universal_type typed_ObjTrue universal
    by (rule CEV_axiom_from_UI_typed)
  have diagonal_true:
    "\<Gamma> ; pp_recombination_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      App pp_diagonal_operator ObjTrue"
    using diagonal_true_raw
    by (simp add: subst0_def shift_def ObjTrue_def
        pp_diagonal_operator_def pp_diagonal_builder_def
        pp_constant_builder_def pp_Pure_def pp_unary_ty_def
        pp_unary_classifier_ty_def)
  have beta_imp:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (App pp_diagonal_operator ObjTrue)
        (Neg
          (pp_pure pp_unary_ty
            (pp_constant_operator ObjTrue)))"
  proof (rule CEV_axiom_proves.Base)
    show "\<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (App pp_diagonal_operator ObjTrue)
          (Neg
            (pp_pure pp_unary_ty
              (pp_constant_operator ObjTrue)))"
      using typed_ObjTrue
      by (rule CEV_pp_diagonal_operator_imp_not_pure_constant)
  qed
  have beta_imp_local:
    "\<Gamma> ; pp_recombination_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (App pp_diagonal_operator ObjTrue)
        (Neg
          (pp_pure pp_unary_ty
            (pp_constant_operator ObjTrue)))"
    using beta_imp by (rule CEV_axiom_from.Theorem)
  have not_pure_constant:
    "\<Gamma> ; pp_recombination_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg
        (pp_pure pp_unary_ty
          (pp_constant_operator ObjTrue))"
    using diagonal_true beta_imp_local by (rule CEV_axiom_from.MP)
  have pure_constant:
    "\<Gamma> ; pp_recombination_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty
        (pp_constant_operator ObjTrue)"
    using pp_constant_ObjTrue_pure_recombination
    by (rule CEV_axiom_from.Theorem)
  show ?thesis
    using pure_constant not_pure_constant
    by (rule CEV_axiom_from_contradiction)
qed

theorem pp_fundamental_forces_diagonal_nonnecessity:
  assumes R_type: "\<Gamma> \<turnstile> R : Prop"
  shows "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun Prop R)
      (Imp
        (\<box>\<^sub>o (App pp_diagonal_operator R))
        ObjFalse)"
proof -
  let ?F = "pp_fun Prop R"
  let ?N = "\<box>\<^sub>o (App pp_diagonal_operator R)"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using R_type by (rule typed_pp_fun)
  have N_type: "\<Gamma> \<turnstile> ?N : Prop"
    using typed_pp_diagonal_operator[of \<Gamma>] R_type
    unfolding pp_unary_ty_def by (auto intro: typed_ObjBox)
  have F_local:
    "\<Gamma> ; pp_recombination_PP_axioms ; {?F, ?N}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have N_local:
    "\<Gamma> ; pp_recombination_PP_axioms ; {?F, ?N}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?N"
    using N_type by (intro CEV_axiom_from.Assumption) simp
  have contradiction:
    "\<Gamma> ; pp_recombination_PP_axioms ; {?F, ?N}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using R_type F_local N_local
    by (rule pp_diagonal_local_contradiction)
  have discharge_N:
    "\<Gamma> ; pp_recombination_PP_axioms ; {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?N ObjFalse"
  proof (rule CEV_axiom_from_deduction[OF N_type])
    show "\<Gamma> ; pp_recombination_PP_axioms ; insert ?N {?F}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
      using contradiction by (simp add: insert_commute)
  qed
  have discharge_F:
    "\<Gamma> ; pp_recombination_PP_axioms ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F (Imp ?N ObjFalse)"
    using F_type discharge_N by (rule CEV_axiom_from_deduction)
  show ?thesis
    using discharge_F CEV_axiom_from_empty_iff by blast
qed

lemma pp_diagonal_box_beta_eta:
  assumes P_type: "\<Gamma> \<turnstile> P : Prop"
  shows "beta_eta_equiv \<Gamma> Prop
    (\<box>\<^sub>o (App pp_diagonal_operator P))
    (\<box>\<^sub>o
      (Neg
        (pp_pure pp_unary_ty
          (pp_constant_operator P))))"
proof (rule beta_eta_equiv.Trans[
    where N = "\<box>\<^sub>o (App pp_diagonal_lambda P)"])
  show "beta_eta_equiv \<Gamma> Prop
      (\<box>\<^sub>o (App pp_diagonal_operator P))
      (\<box>\<^sub>o (App pp_diagonal_lambda P))"
  proof (rule beta_eta_equiv.Beta)
    show "\<Gamma> \<turnstile> \<box>\<^sub>o (App pp_diagonal_operator P) : Prop"
      using typed_pp_diagonal_operator[of \<Gamma>] P_type
      unfolding pp_unary_ty_def by (auto intro: typed_ObjBox)
  next
    show "\<Gamma> \<turnstile> \<box>\<^sub>o (App pp_diagonal_lambda P) : Prop"
      using typed_pp_diagonal_lambda[of \<Gamma>] P_type
      unfolding pp_unary_ty_def by (auto intro: typed_ObjBox)
  next
    show "compatible_step beta_contract
        (\<box>\<^sub>o (App pp_diagonal_operator P))
        (\<box>\<^sub>o (App pp_diagonal_lambda P))"
      unfolding ObjBox_def
      using pp_diagonal_operator_first_beta
      by (rule compatible_step.Eq_left)
  qed
next
  show "beta_eta_equiv \<Gamma> Prop
      (\<box>\<^sub>o (App pp_diagonal_lambda P))
      (\<box>\<^sub>o
        (Neg
          (pp_pure pp_unary_ty
            (pp_constant_operator P))))"
  proof (rule beta_eta_equiv.Beta)
    show "\<Gamma> \<turnstile> \<box>\<^sub>o (App pp_diagonal_lambda P) : Prop"
      using typed_pp_diagonal_lambda[of \<Gamma>] P_type
      unfolding pp_unary_ty_def by (auto intro: typed_ObjBox)
  next
    show "\<Gamma> \<turnstile>
        \<box>\<^sub>o
          (Neg
            (pp_pure pp_unary_ty
              (pp_constant_operator P))) : Prop"
      using typed_pp_pure[OF typed_pp_constant_operator[OF P_type]]
      by (auto intro: typed_ObjBox)
  next
    show "compatible_step beta_contract
        (\<box>\<^sub>o (App pp_diagonal_lambda P))
        (\<box>\<^sub>o
          (Neg
            (pp_pure pp_unary_ty
              (pp_constant_operator P))))"
      unfolding ObjBox_def
      using pp_diagonal_operator_second_beta
      by (rule compatible_step.Eq_left)
  qed
qed

lemma CEV_pp_not_pure_constant_box_imp_diagonal_box:
  assumes P_type: "\<Gamma> \<turnstile> P : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp
      (\<box>\<^sub>o
        (Neg
          (pp_pure pp_unary_ty
            (pp_constant_operator P))))
      (\<box>\<^sub>o (App pp_diagonal_operator P))"
proof -
  have diagonal_box_type:
    "\<Gamma> \<turnstile> \<box>\<^sub>o (App pp_diagonal_operator P) : Prop"
    using typed_pp_diagonal_operator[of \<Gamma>] P_type
    unfolding pp_unary_ty_def by (auto intro: typed_ObjBox)
  have pure_box_type:
    "\<Gamma> \<turnstile>
      \<box>\<^sub>o
        (Neg
          (pp_pure pp_unary_ty
            (pp_constant_operator P))) : Prop"
    using typed_pp_pure[OF typed_pp_constant_operator[OF P_type]]
    by (auto intro: typed_ObjBox)
  have biconditional:
    "\<Gamma> \<turnstile>\<^sub>CEV
      ((\<box>\<^sub>o (App pp_diagonal_operator P))
        \<longleftrightarrow>\<^sub>o
       (\<box>\<^sub>o
        (Neg
          (pp_pure pp_unary_ty
            (pp_constant_operator P)))))"
    using pp_diagonal_box_beta_eta[OF P_type]
    by (rule CEV_beta_eta_equiv)
  show ?thesis
    using diagonal_box_type pure_box_type biconditional
    by (rule CEV_beta_right_imp)
qed

theorem pp_fundamental_forces_possible_constant_purity:
  assumes R_type: "\<Gamma> \<turnstile> R : Prop"
  shows "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun Prop R)
      (\<diamond>\<^sub>o
        (pp_pure pp_unary_ty
          (pp_constant_operator R)))"
proof -
  let ?F = "pp_fun Prop R"
  let ?B =
    "\<box>\<^sub>o
      (Neg
        (pp_pure pp_unary_ty
          (pp_constant_operator R)))"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using R_type by (rule typed_pp_fun)
  have B_type: "\<Gamma> \<turnstile> ?B : Prop"
    using typed_pp_pure[OF typed_pp_constant_operator[OF R_type]]
    by (auto intro: typed_ObjBox)
  have F_local:
    "\<Gamma> ; pp_recombination_PP_axioms ; {?F, ?B}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have B_local:
    "\<Gamma> ; pp_recombination_PP_axioms ; {?F, ?B}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?B"
    using B_type by (intro CEV_axiom_from.Assumption) simp
  have bridge:
    "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?B (\<box>\<^sub>o (App pp_diagonal_operator R))"
  proof (rule CEV_axiom_proves.Base)
    show "\<Gamma> \<turnstile>\<^sub>CEV
        Imp ?B (\<box>\<^sub>o (App pp_diagonal_operator R))"
      using R_type
      by (rule CEV_pp_not_pure_constant_box_imp_diagonal_box)
  qed
  have bridge_local:
    "\<Gamma> ; pp_recombination_PP_axioms ; {?F, ?B}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?B (\<box>\<^sub>o (App pp_diagonal_operator R))"
    using bridge by (rule CEV_axiom_from.Theorem)
  have diagonal_box:
    "\<Gamma> ; pp_recombination_PP_axioms ; {?F, ?B}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (App pp_diagonal_operator R)"
    using B_local bridge_local by (rule CEV_axiom_from.MP)
  have contradiction:
    "\<Gamma> ; pp_recombination_PP_axioms ; {?F, ?B}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using R_type F_local diagonal_box
    by (rule pp_diagonal_local_contradiction)
  have imp_false:
    "\<Gamma> ; pp_recombination_PP_axioms ; {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?B ObjFalse"
  proof (rule CEV_axiom_from_deduction[OF B_type])
    show "\<Gamma> ; pp_recombination_PP_axioms ; insert ?B {?F}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
      using contradiction by (simp add: insert_commute)
  qed
  have to_neg:
    "\<Gamma> ; pp_recombination_PP_axioms ; {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?B ObjFalse) (Neg ?B)"
    using CEV_proves_imp_false_to_neg[OF B_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have possible_local:
    "\<Gamma> ; pp_recombination_PP_axioms ; {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<diamond>\<^sub>o
        (pp_pure pp_unary_ty
          (pp_constant_operator R))"
    using imp_false to_neg
    unfolding ObjDiamond_def
    by (rule CEV_axiom_from.MP)
  have discharged:
    "\<Gamma> ; pp_recombination_PP_axioms ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F
        (\<diamond>\<^sub>o
          (pp_pure pp_unary_ty
            (pp_constant_operator R)))"
    using F_type possible_local by (rule CEV_axiom_from_deduction)
  show ?thesis
    using discharged CEV_axiom_from_empty_iff by blast
qed

corollary pp_fundamental_forces_possible_constant_purity_full_QLN:
  assumes "\<Gamma> \<turnstile> R : Prop"
  shows "\<Gamma> ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun Prop R)
      (\<diamond>\<^sub>o
        (pp_pure pp_unary_ty
          (pp_constant_operator R)))"
  using pp_fundamental_forces_possible_constant_purity[OF assms]
    pp_recombination_PP_axioms_subset_full_QLN
  by (rule CEV_axiom_proves_mono)

theorem pp_some_fundamental_has_possible_constant_purity:
  "[] ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_possible_constant_purity"
proof -
  let ?U =
    "Conj
      (pp_fun Prop (Var 0))
      (Forall Prop
        (Imp
          (pp_fun Prop (Var 0))
          (Eq Prop (Var 0) (Var 1))))"
  have U_type: "[Prop] \<turnstile> ?U : Prop"
    by (rule infer_type_sound)
      (simp add: pp_fun_def pp_Fun_def lookup_def)
  have U_local:
    "[Prop] ; pp_recombination_PP_axioms ; {?U}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?U"
  proof (rule CEV_axiom_from.Assumption)
    show "?U \<in> {?U}"
      by simp
    show "[Prop] \<turnstile> ?U : Prop"
      by (rule U_type)
  qed
  have fundamental_local:
    "[Prop] ; pp_recombination_PP_axioms ; {?U}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun Prop (Var 0)"
    using U_local by (rule CEV_axiom_from_conj_left)
  have possible:
    "[Prop] ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (pp_fun Prop (Var 0))
        (\<diamond>\<^sub>o
          (pp_pure pp_unary_ty
            (pp_constant_operator (Var 0))))"
    using pp_fundamental_forces_possible_constant_purity[
      of "[Prop]" "Var 0"]
    by simp
  have possible_local:
    "[Prop] ; pp_recombination_PP_axioms ; {?U}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<diamond>\<^sub>o
        (pp_pure pp_unary_ty
          (pp_constant_operator (Var 0)))"
  proof -
    have lifted:
      "[Prop] ; pp_recombination_PP_axioms ; {?U}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp
          (pp_fun Prop (Var 0))
          (\<diamond>\<^sub>o
            (pp_pure pp_unary_ty
              (pp_constant_operator (Var 0))))"
      using possible by (rule CEV_axiom_from.Theorem)
    show ?thesis
      using fundamental_local lifted by (rule CEV_axiom_from.MP)
  qed
  have pair_local:
    "[Prop] ; pp_recombination_PP_axioms ; {?U}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_possible_constant_purity_body"
    using fundamental_local possible_local
    unfolding pp_possible_constant_purity_body_def
    by (rule CEV_axiom_from_conj_intro)
  have eg:
    "[Prop] \<turnstile>\<^sub>CEV
      Imp
        pp_possible_constant_purity_body
        pp_possible_constant_purity"
  proof -
    have raw:
      "[Prop] \<turnstile>\<^sub>H
        Imp
          (subst0 (Var 0) pp_possible_constant_purity_body)
          (Exists Prop pp_possible_constant_purity_body)"
    proof (rule H_proves.EG)
      show "Prop # [Prop] \<turnstile>
          pp_possible_constant_purity_body : Prop"
        by (rule typed_pp_possible_constant_purity_body)
      show "[Prop] \<turnstile> Var 0 : Prop"
        by simp
    qed
    have raw_cev:
      "[Prop] \<turnstile>\<^sub>CEV
        Imp
          (subst0 (Var 0) pp_possible_constant_purity_body)
          (Exists Prop pp_possible_constant_purity_body)"
      using raw
      by (intro CEV_proves.CE CE_proves.C C_proves.H)
    show ?thesis
      using raw_cev
      by (simp add: pp_possible_constant_purity_def
          pp_possible_constant_purity_body_def pp_constant_operator_def
          pp_constant_builder_def pp_unary_ty_def pp_pure_def
          pp_Pure_def pp_fun_def pp_Fun_def ObjDiamond_def ObjBox_def
          ObjTrue_def subst0_def)
  qed
  have eg_local:
    "[Prop] ; pp_recombination_PP_axioms ; {?U}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        pp_possible_constant_purity_body
        pp_possible_constant_purity"
    using eg
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have existential_local:
    "[Prop] ; pp_recombination_PP_axioms ; {?U}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_possible_constant_purity"
    using pair_local eg_local by (rule CEV_axiom_from.MP)
  have witness_imp:
    "[Prop] ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?U (shift pp_possible_constant_purity)"
  proof -
    have unshifted:
      "[Prop] ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?U pp_possible_constant_purity"
      using U_type existential_local
      by (rule CEV_axiom_from_singleton_imp)
    show ?thesis
      using unshifted
      by (simp add: shift_def pp_possible_constant_purity_def
          pp_possible_constant_purity_body_def pp_constant_operator_def
          pp_constant_builder_def pp_unary_ty_def pp_pure_def
          pp_Pure_def pp_fun_def pp_Fun_def ObjDiamond_def ObjBox_def
          ObjTrue_def)
  qed
  have eliminate_unique:
    "[] ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (pp_unique_fundamental Prop)
        pp_possible_constant_purity"
  proof (unfold pp_unique_fundamental_def, rule CEV_axiom_proves.Inst)
    show "[Prop] \<turnstile> ?U : Prop"
      by (rule U_type)
  next
    show "[] \<turnstile> pp_possible_constant_purity : Prop"
      by (rule typed_pp_possible_constant_purity)
  next
    show "[Prop] ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?U (shift pp_possible_constant_purity)"
      by (rule witness_imp)
  qed
  have unique:
    "[] ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_unique_fundamental Prop"
    using pp_unique_fundamental_is_assumed_recombination
      typed_pp_unique_fundamental
    by (rule CEV_axiom_proves.Axiom)
  show ?thesis
    unfolding pp_possible_constant_purity_def[symmetric]
    using unique eliminate_unique by (rule CEV_axiom_proves.MP)
qed

corollary pp_some_fundamental_has_possible_constant_purity_full_QLN:
  "[] ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_possible_constant_purity"
  using pp_some_fundamental_has_possible_constant_purity
    pp_recombination_PP_axioms_subset_full_QLN
  by (rule CEV_axiom_proves_mono)

text \<open>
  Thus the diagonal operator is already forced by PP, the logical-purity
  schema, and application closure.  Recombination then proves, uniformly in
  any proposition \<open>R\<close>, that if \<open>R\<close> is fundamental, the diagonal cannot
  be necessary at \<open>R\<close>.  This is a theorem of the axiom extension, with no
  rigid witness assumption and no use of Exhaustion.

  More sharply, the theory proves that a fundamental \<open>R\<close> makes it possible
  for the constant operator \<open>K R\<close> to be pure.  This is the exact syntactic
  counterpart of the nonactual-world certificate required by the semantic
  diagonal analysis.

  It is still not a contradiction.  The existential statement that some
  proposition is fundamental supplies only a temporary witness, and the
  possibility just obtained need not be a possibility at which that same
  entity is fundamental.  Results depending on the witness cannot be fed into
  theorem-level Necessitation.  Any proof that closes Goodman's question must
  either bridge this modal witness gap without adding witness rigidity or
  construct a model in which the displayed shift of roles is realized.
\<close>

end
