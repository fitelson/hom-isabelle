theory Bacon_PP_Goodman_Granularity_QLN
  imports
    
    "Goodman_Legacy_Granularity.Bacon_PP_Goodman_Granularity"
    "Goodman_Legacy_Central_Stock.Bacon_PP_QSS_Recombination_Bridge"
begin

section \<open>The QLN granularity condition in the object language\<close>

text \<open>
  The biconditional in Goodman's proposed condition is the truth-functional
  biconditional, not equality at the proposition type.  We therefore use two
  closed builders.  Given a unary operator \<open>Z\<close>, the first returns the
  operator \<open>p \<mapsto> (Zp \<longleftrightarrow> p)\<close>; the second returns its pointwise
  negation.
\<close>

definition pp_agreement_operator_builder :: oterm where
  "pp_agreement_operator_builder =
    Lam pp_unary_ty
      (Lam Prop
        (App (Var 1) (Var 0) \<longleftrightarrow>\<^sub>o Var 0))"

definition pp_agreement_operator :: "oterm \<Rightarrow> oterm" where
  "pp_agreement_operator Z = App pp_agreement_operator_builder Z"

definition pp_disagreement_operator_builder :: oterm where
  "pp_disagreement_operator_builder =
    Lam pp_unary_ty
      (Lam Prop
        (Neg (App (Var 1) (Var 0) \<longleftrightarrow>\<^sub>o Var 0)))"

definition pp_disagreement_operator :: "oterm \<Rightarrow> oterm" where
  "pp_disagreement_operator Z = App pp_disagreement_operator_builder Z"

definition pp_QLN_granularity_at :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_QLN_granularity_at Z r =
    Disj
      (\<box>\<^sub>o (App (pp_agreement_operator Z) r))
      (\<box>\<^sub>o (App (pp_disagreement_operator Z) r))"

definition pp_QLN_truth_uniform_at :: "oterm \<Rightarrow> oterm" where
  "pp_QLN_truth_uniform_at Z =
    Disj
      (Forall Prop
        (App (shift (pp_agreement_operator Z)) (Var 0)))
      (Forall Prop
        (App (shift (pp_disagreement_operator Z)) (Var 0)))"

definition pp_QLN_granularity :: "oterm \<Rightarrow> oterm" where
  "pp_QLN_granularity r =
    Forall pp_unary_ty
      (Imp
        (pp_group_member (Var 0))
        (pp_QLN_granularity_at (Var 0) (shift r)))"

lemma typed_pp_agreement_operator_builder:
  "\<Gamma> \<turnstile> pp_agreement_operator_builder :
    pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_agreement_operator_builder_def pp_unary_ty_def
      lookup_def)

lemma typed_pp_agreement_operator:
  assumes "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_agreement_operator Z : pp_unary_ty"
  unfolding pp_agreement_operator_def
  using typed_pp_agreement_operator_builder assms
  by (rule has_type.App)

lemma typed_pp_disagreement_operator_builder:
  "\<Gamma> \<turnstile> pp_disagreement_operator_builder :
    pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_disagreement_operator_builder_def pp_unary_ty_def
      lookup_def)

lemma typed_pp_disagreement_operator:
  assumes "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_disagreement_operator Z : pp_unary_ty"
  unfolding pp_disagreement_operator_def
  using typed_pp_disagreement_operator_builder assms
  by (rule has_type.App)

lemma typed_pp_QLN_granularity_at:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> pp_QLN_granularity_at Z r : Prop"
proof -
  have agreement_type:
    "\<Gamma> \<turnstile> pp_agreement_operator Z : Prop \<rightarrow>\<^sub>o Prop"
    using typed_pp_agreement_operator[OF Z_type]
    unfolding pp_unary_ty_def .
  have disagreement_type:
    "\<Gamma> \<turnstile> pp_disagreement_operator Z : Prop \<rightarrow>\<^sub>o Prop"
    using typed_pp_disagreement_operator[OF Z_type]
    unfolding pp_unary_ty_def .
  show ?thesis
    unfolding pp_QLN_granularity_at_def
    using agreement_type disagreement_type r_type
    by (intro has_type.Disj typed_ObjBox has_type.App)
qed

lemma typed_pp_QLN_truth_uniform_at:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_QLN_truth_uniform_at Z : Prop"
proof -
  have agreement_shift:
    "Prop # \<Gamma> \<turnstile> shift (pp_agreement_operator Z) :
      Prop \<rightarrow>\<^sub>o Prop"
    using typed_shift_ctx[OF typed_pp_agreement_operator[OF Z_type]]
    unfolding pp_unary_ty_def .
  have disagreement_shift:
    "Prop # \<Gamma> \<turnstile> shift (pp_disagreement_operator Z) :
      Prop \<rightarrow>\<^sub>o Prop"
    using typed_shift_ctx[OF typed_pp_disagreement_operator[OF Z_type]]
    unfolding pp_unary_ty_def .
  show ?thesis
    unfolding pp_QLN_truth_uniform_at_def
    using agreement_shift disagreement_shift typed_var0
    by (intro has_type.Disj has_type.Forall has_type.App)
qed

lemma typed_pp_QLN_granularity:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> pp_QLN_granularity r : Prop"
  unfolding pp_QLN_granularity_def
  using typed_pp_group_member[of "pp_unary_ty # \<Gamma>" "Var 0"]
    typed_pp_QLN_granularity_at[
      of "pp_unary_ty # \<Gamma>" "Var 0" "shift r"]
    typed_shift_ctx[OF r_type]
  by (intro has_type.Forall has_type.Imp has_type.Var)
    (simp_all add: lookup_def)

lemma pp_agreement_operator_beta:
  "compatible_step beta_contract
    (pp_agreement_operator Z)
    (Lam Prop
      (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0))"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty
          (Lam Prop
            (App (Var 1) (Var 0) \<longleftrightarrow>\<^sub>o Var 0))) Z)
      (subst0 Z
        (Lam Prop
          (App (Var 1) (Var 0) \<longleftrightarrow>\<^sub>o Var 0)))"
    by (rule beta_contract.beta)
  show "beta_contract
      (pp_agreement_operator Z)
      (Lam Prop
        (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0))"
    using step
    by (simp add: pp_agreement_operator_def
      pp_agreement_operator_builder_def subst0_def shift_def)
qed

lemma pp_agreement_operator_apply_beta:
  "compatible_step beta_contract
    (App
      (Lam Prop
        (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0)) p)
    (App Z p \<longleftrightarrow>\<^sub>o p)"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam Prop
          (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0)) p)
      (subst0 p
        (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0))"
    by (rule beta_contract.beta)
  have Z_inv:
    "subst (case_nat p Var) (shift Z) = Z"
    using subst0_shift[of p Z]
    unfolding subst0_def .
  show "beta_contract
      (App
        (Lam Prop
          (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0)) p)
      (App Z p \<longleftrightarrow>\<^sub>o p)"
    using step Z_inv by (simp add: subst0_def)
qed

lemma pp_disagreement_operator_beta:
  "compatible_step beta_contract
    (pp_disagreement_operator Z)
    (Lam Prop
      (Neg (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0)))"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty
          (Lam Prop
            (Neg (App (Var 1) (Var 0) \<longleftrightarrow>\<^sub>o Var 0)))) Z)
      (subst0 Z
        (Lam Prop
          (Neg (App (Var 1) (Var 0) \<longleftrightarrow>\<^sub>o Var 0))))"
    by (rule beta_contract.beta)
  show "beta_contract
      (pp_disagreement_operator Z)
      (Lam Prop
        (Neg (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0)))"
    using step
    by (simp add: pp_disagreement_operator_def
      pp_disagreement_operator_builder_def subst0_def shift_def)
qed

lemma pp_disagreement_operator_apply_beta:
  "compatible_step beta_contract
    (App
      (Lam Prop
        (Neg (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0))) p)
    (Neg (App Z p \<longleftrightarrow>\<^sub>o p))"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam Prop
          (Neg (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0))) p)
      (subst0 p
        (Neg (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0)))"
    by (rule beta_contract.beta)
  have Z_inv:
    "subst (case_nat p Var) (shift Z) = Z"
    using subst0_shift[of p Z]
    unfolding subst0_def .
  show "beta_contract
      (App
        (Lam Prop
          (Neg (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0))) p)
      (Neg (App Z p \<longleftrightarrow>\<^sub>o p))"
    using step Z_inv by (simp add: subst0_def)
qed

text \<open>
  These beta certificates verify that \<open>pp_QLN_granularity_at Z r\<close>
  is exactly
  \<open>\<box>(Zr \<longleftrightarrow> r) \<or> \<box>\<not>(Zr \<longleftrightarrow> r)\<close>, modulo conversion.
\<close>

subsection \<open>Unary Exhaustion in an arbitrary axiom extension\<close>

lemma CEV_axiom_unary_exhaustion_instance:
  assumes exhaustion: "pp_unary_exhaustion \<in> T"
    and F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure pp_unary_ty F)
        (pp_fun Prop r))
      (Imp
        (Forall Prop (App (shift F) (Var 0)))
        (\<box>\<^sub>o (App F r)))"
proof -
  have qln_type: "\<Gamma> \<turnstile> pp_unary_exhaustion : Prop"
    by (rule infer_type_sound)
      (simp add: pp_unary_exhaustion_def pp_pure_def pp_Pure_def
        pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)
  have d_qln: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_unary_exhaustion"
    using exhaustion qln_type by (rule CEV_axiom_proves.Axiom)
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
              (Forall Prop (App (Var 2) (Var 0)))
              (\<box>\<^sub>o (App (Var 1) (Var 0))))))"
    using qln_type F_raw d_qln
    unfolding pp_unary_exhaustion_def
    by (rule CEV_axiom_UI_typed)
  have d_outer:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift F))
            (pp_fun Prop (Var 0)))
          (Imp
            (Forall Prop (App (shift (shift F)) (Var 0)))
            (\<box>\<^sub>o (App (shift F) (Var 0)))))"
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
            (Forall Prop (App (shift (shift F)) (Var 0)))
            (\<box>\<^sub>o (App (shift F) (Var 0))))) : Prop"
    using d_outer by (rule CEV_axiom_proves_formula)
  have d_inner_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 r
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift F))
            (pp_fun Prop (Var 0)))
          (Imp
            (Forall Prop (App (shift (shift F)) (Var 0)))
            (\<box>\<^sub>o (App (shift F) (Var 0)))))"
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

lemma CEV_axiom_unary_QLN_instance:
  assumes recombination: "pp_unary_recombination \<in> T"
    and exhaustion: "pp_unary_exhaustion \<in> T"
    and F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure pp_unary_ty F)
        (pp_fun Prop r))
      ((\<box>\<^sub>o (App F r)) \<longleftrightarrow>\<^sub>o
        Forall Prop (App (shift F) (Var 0)))"
proof -
  let ?A = "Conj (pp_pure pp_unary_ty F) (pp_fun Prop r)"
  let ?B = "\<box>\<^sub>o (App F r)"
  let ?C = "Forall Prop (App (shift F) (Var 0))"
  have F_raw: "\<Gamma> \<turnstile> F : Prop \<rightarrow>\<^sub>o Prop"
    using F_type unfolding pp_unary_ty_def .
  have pure_type: "\<Gamma> \<turnstile> pp_pure pp_unary_ty F : Prop"
    using F_type by (rule typed_pp_pure)
  have fun_type: "\<Gamma> \<turnstile> pp_fun Prop r : Prop"
    using r_type by (rule typed_pp_fun)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using pure_type fun_type by (rule has_type.Conj)
  have B_type: "\<Gamma> \<turnstile> ?B : Prop"
    using F_raw r_type by (intro typed_ObjBox has_type.App)
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using typed_shift_ctx[OF F_raw] typed_var0
    by (intro has_type.Forall has_type.App)
  have BC: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?A (Imp ?B ?C)"
    using recombination F_type r_type
    by (rule CEV_axiom_unary_recombination_instance)
  have CB: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?A (Imp ?C ?B)"
    using exhaustion F_type r_type
    by (rule CEV_axiom_unary_exhaustion_instance)
  have taut:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp ?A (Imp ?B ?C))
        (Imp (Imp ?A (Imp ?C ?B))
          (Imp ?A (?B \<longleftrightarrow>\<^sub>o ?C)))"
  proof (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.H H_proves.PC)
    have formula_type:
      "\<Gamma> \<turnstile>
        Imp (Imp ?A (Imp ?B ?C))
          (Imp (Imp ?A (Imp ?C ?B))
            (Imp ?A (?B \<longleftrightarrow>\<^sub>o ?C))) : Prop"
      using pure_type fun_type B_type C_type
      by (intro has_type.Imp has_type.Conj)
    show "prop_tautology \<Gamma>
      (Imp (Imp ?A (Imp ?B ?C))
        (Imp (Imp ?A (Imp ?C ?B))
          (Imp ?A (?B \<longleftrightarrow>\<^sub>o ?C))))"
      unfolding prop_tautology_def
      using formula_type by auto
  qed
  have tail:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp ?A (Imp ?C ?B))
        (Imp ?A (?B \<longleftrightarrow>\<^sub>o ?C))"
    using BC taut by (rule CEV_axiom_proves.MP)
  show ?thesis
    using CB tail by (rule CEV_axiom_proves.MP)
qed

subsection \<open>Purity of the agreement constructions\<close>

lemma pp_agreement_operator_builder_purity_axiom:
  "pp_pure (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty)
      pp_agreement_operator_builder \<in> pp_T6_core_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
proof (intro UnI1 CollectI exI conjI)
  show "[] \<turnstile> pp_agreement_operator_builder :
      pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
    by (rule typed_pp_agreement_operator_builder)
  show "consts_of pp_agreement_operator_builder = {}"
    by (simp add: pp_agreement_operator_builder_def)
qed simp

lemma pp_disagreement_operator_builder_purity_axiom:
  "pp_pure (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty)
      pp_disagreement_operator_builder \<in> pp_T6_core_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
proof (intro UnI1 CollectI exI conjI)
  show "[] \<turnstile> pp_disagreement_operator_builder :
      pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
    by (rule typed_pp_disagreement_operator_builder)
  show "consts_of pp_disagreement_operator_builder = {}"
    by (simp add: pp_disagreement_operator_builder_def)
qed simp

lemma CEV_axiom_from_pure_agreement_operator:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and pure_Z:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Z"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_unary_ty (pp_agreement_operator Z)"
proof -
  let ?bty = "pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
  have builder_in:
    "pp_pure ?bty pp_agreement_operator_builder \<in> T"
    using pp_agreement_operator_builder_purity_axiom core by blast
  have builder_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure ?bty pp_agreement_operator_builder"
    using builder_in
      typed_pp_pure[OF typed_pp_agreement_operator_builder]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  have closure:
    "pp_application_closure pp_unary_ty pp_unary_ty \<in> T"
    using pp_T6_application_closure_axiom core by blast
  show ?thesis
    unfolding pp_agreement_operator_def
    using closure typed_pp_agreement_operator_builder Z_type
      builder_pure pure_Z
    by (rule pp_axiom_application_closed_from)
qed

lemma CEV_axiom_from_pure_disagreement_operator:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and pure_Z:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Z"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_unary_ty (pp_disagreement_operator Z)"
proof -
  let ?bty = "pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
  have builder_in:
    "pp_pure ?bty pp_disagreement_operator_builder \<in> T"
    using pp_disagreement_operator_builder_purity_axiom core by blast
  have builder_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure ?bty pp_disagreement_operator_builder"
    using builder_in
      typed_pp_pure[OF typed_pp_disagreement_operator_builder]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  have closure:
    "pp_application_closure pp_unary_ty pp_unary_ty \<in> T"
    using pp_T6_application_closure_axiom core by blast
  show ?thesis
    unfolding pp_disagreement_operator_def
    using closure typed_pp_disagreement_operator_builder Z_type
      builder_pure pure_Z
    by (rule pp_axiom_application_closed_from)
qed

lemma pp_T6_core_subset_full_QLN_PP_granularity:
  "pp_T6_core_PP_axioms \<subseteq> pp_full_QLN_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def pp_full_QLN_PP_axioms_def
    pp_full_QLN_background_axioms_def
    pp_recombination_background_axioms_def pp_background_axioms_def
  by blast

lemma pp_unary_recombination_in_full_QLN_PP:
  "pp_unary_recombination \<in> pp_full_QLN_PP_axioms"
  unfolding pp_full_QLN_PP_axioms_def
    pp_full_QLN_background_axioms_def
    pp_recombination_background_axioms_def by blast

lemma pp_unary_exhaustion_in_full_QLN_PP:
  "pp_unary_exhaustion \<in> pp_full_QLN_PP_axioms"
  unfolding pp_full_QLN_PP_axioms_def
    pp_full_QLN_background_axioms_def pp_exhaustion_axioms_def
  by blast

subsection \<open>The exact granularity reduction\<close>

theorem CEV_axiom_from_QLN_granularity_iff_truth_uniform:
  assumes recombination: "pp_unary_recombination \<in> T"
    and exhaustion: "pp_unary_exhaustion \<in> T"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and pure_agreement:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty (pp_agreement_operator Z)"
    and pure_disagreement:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty (pp_disagreement_operator Z)"
    and fun_r:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun Prop r"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    (pp_QLN_granularity_at Z r \<longleftrightarrow>\<^sub>o
      pp_QLN_truth_uniform_at Z)"
proof -
  let ?F = "pp_agreement_operator Z"
  let ?G = "pp_disagreement_operator Z"
  let ?BF = "\<box>\<^sub>o (App ?F r)"
  let ?AF = "Forall Prop (App (shift ?F) (Var 0))"
  let ?BG = "\<box>\<^sub>o (App ?G r)"
  let ?AG = "Forall Prop (App (shift ?G) (Var 0))"
  have F_type: "\<Gamma> \<turnstile> ?F : pp_unary_ty"
    using Z_type by (rule typed_pp_agreement_operator)
  have G_type: "\<Gamma> \<turnstile> ?G : pp_unary_ty"
    using Z_type by (rule typed_pp_disagreement_operator)
  have pure_F_type: "\<Gamma> \<turnstile> pp_pure pp_unary_ty ?F : Prop"
    using F_type by (rule typed_pp_pure)
  have pure_G_type: "\<Gamma> \<turnstile> pp_pure pp_unary_ty ?G : Prop"
    using G_type by (rule typed_pp_pure)
  have fun_type: "\<Gamma> \<turnstile> pp_fun Prop r : Prop"
    using r_type by (rule typed_pp_fun)
  have antecedent_F:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_pure pp_unary_ty ?F) (pp_fun Prop r)"
    using pure_agreement fun_r by (rule CEV_axiom_from_conj_intro)
  have antecedent_G:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_pure pp_unary_ty ?G) (pp_fun Prop r)"
    using pure_disagreement fun_r by (rule CEV_axiom_from_conj_intro)
  have qln_F:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Conj (pp_pure pp_unary_ty ?F) (pp_fun Prop r))
        (?BF \<longleftrightarrow>\<^sub>o ?AF)"
    using recombination exhaustion F_type r_type
    by (rule CEV_axiom_unary_QLN_instance)
  have qln_G:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Conj (pp_pure pp_unary_ty ?G) (pp_fun Prop r))
        (?BG \<longleftrightarrow>\<^sub>o ?AG)"
    using recombination exhaustion G_type r_type
    by (rule CEV_axiom_unary_QLN_instance)
  have d_F:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?BF \<longleftrightarrow>\<^sub>o ?AF)"
    using antecedent_F CEV_axiom_from.Theorem[OF qln_F]
    by (rule CEV_axiom_from.MP)
  have d_G:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?BG \<longleftrightarrow>\<^sub>o ?AG)"
    using antecedent_G CEV_axiom_from.Theorem[OF qln_G]
    by (rule CEV_axiom_from.MP)
  have BF_type: "\<Gamma> \<turnstile> ?BF : Prop"
    using F_type[unfolded pp_unary_ty_def] r_type
    by (intro typed_ObjBox has_type.App)
  have BG_type: "\<Gamma> \<turnstile> ?BG : Prop"
    using G_type[unfolded pp_unary_ty_def] r_type
    by (intro typed_ObjBox has_type.App)
  have AF_type: "\<Gamma> \<turnstile> ?AF : Prop"
    using typed_shift_ctx[OF F_type[unfolded pp_unary_ty_def]]
      typed_var0
    by (intro has_type.Forall has_type.App)
  have AG_type: "\<Gamma> \<turnstile> ?AG : Prop"
    using typed_shift_ctx[OF G_type[unfolded pp_unary_ty_def]]
      typed_var0
    by (intro has_type.Forall has_type.App)
  have taut:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (?BF \<longleftrightarrow>\<^sub>o ?AF)
        (Imp (?BG \<longleftrightarrow>\<^sub>o ?AG)
          (Disj ?BF ?BG \<longleftrightarrow>\<^sub>o Disj ?AF ?AG))"
  proof (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base
      CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
    have formula_type:
      "\<Gamma> \<turnstile>
        Imp (?BF \<longleftrightarrow>\<^sub>o ?AF)
          (Imp (?BG \<longleftrightarrow>\<^sub>o ?AG)
            (Disj ?BF ?BG \<longleftrightarrow>\<^sub>o Disj ?AF ?AG)) : Prop"
      using BF_type AF_type BG_type AG_type
      by (intro has_type.Imp has_type.Conj has_type.Disj)
    show "prop_tautology \<Gamma>
      (Imp (?BF \<longleftrightarrow>\<^sub>o ?AF)
        (Imp (?BG \<longleftrightarrow>\<^sub>o ?AG)
          (Disj ?BF ?BG \<longleftrightarrow>\<^sub>o Disj ?AF ?AG)))"
      unfolding prop_tautology_def
      using formula_type by auto
  qed
  have tail:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (?BG \<longleftrightarrow>\<^sub>o ?AG)
        (Disj ?BF ?BG \<longleftrightarrow>\<^sub>o Disj ?AF ?AG)"
    using d_F taut by (rule CEV_axiom_from.MP)
  have result:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (Disj ?BF ?BG \<longleftrightarrow>\<^sub>o Disj ?AF ?AG)"
    using d_G tail by (rule CEV_axiom_from.MP)
  show ?thesis
    using result
    by (simp add: pp_QLN_granularity_at_def
      pp_QLN_truth_uniform_at_def)
qed

corollary CEV_full_QLN_PP_granularity_iff_truth_uniform:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and pure_Z:
      "\<Gamma> ; pp_full_QLN_PP_axioms ; S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Z"
    and fun_r:
      "\<Gamma> ; pp_full_QLN_PP_axioms ; S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun Prop r"
  shows "\<Gamma> ; pp_full_QLN_PP_axioms ; S
    \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (pp_QLN_granularity_at Z r \<longleftrightarrow>\<^sub>o
        pp_QLN_truth_uniform_at Z)"
proof (rule CEV_axiom_from_QLN_granularity_iff_truth_uniform)
  show "pp_unary_recombination \<in> pp_full_QLN_PP_axioms"
    by (rule pp_unary_recombination_in_full_QLN_PP)
  show "pp_unary_exhaustion \<in> pp_full_QLN_PP_axioms"
    by (rule pp_unary_exhaustion_in_full_QLN_PP)
  show "\<Gamma> \<turnstile> Z : pp_unary_ty" by (rule Z_type)
  show "\<Gamma> \<turnstile> r : Prop" by (rule r_type)
  show "\<Gamma> ; pp_full_QLN_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty (pp_agreement_operator Z)"
    using pp_T6_core_subset_full_QLN_PP_granularity Z_type pure_Z
    by (rule CEV_axiom_from_pure_agreement_operator)
  show "\<Gamma> ; pp_full_QLN_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty (pp_disagreement_operator Z)"
    using pp_T6_core_subset_full_QLN_PP_granularity Z_type pure_Z
    by (rule CEV_axiom_from_pure_disagreement_operator)
  show "\<Gamma> ; pp_full_QLN_PP_axioms ; S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun Prop r"
    by (rule fun_r)
qed

text \<open>
  This is the advertised test.  Full QLN and the established purity closure do
  not turn the granularity condition into a weaker intermediate principle:
  they turn it into the pointwise disjunction saying that \<open>Z\<close> preserves
  truth everywhere or reverses truth everywhere.  The first universal is
  definitionally \<open>pp_truth_preserving Z\<close> after beta conversion.  The
  second is classically equivalent, point by point, to
  \<open>pp_truth_flipping Z\<close>.  Hence, for pure reversible \<open>Z\<close>, the proposed
  premise is exactly TU in the full QLN setting.

  PP supplies the purity of the two constructed operators, but no additional
  axiom currently supplies either disjunct.  Proving the condition from PP
  would therefore be a proof of TU, not an independent granularity lemma.
\<close>

text \<open>
  Thus both directions required for the granularity test are available as
  explicit CEV+ derivations.  What remains is not a missing QLN step: it is
  the proposed noncontingency disjunction itself.
\<close>

end
