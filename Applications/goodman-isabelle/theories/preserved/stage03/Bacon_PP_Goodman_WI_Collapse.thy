theory Bacon_PP_Goodman_WI_Collapse
  imports 
    "Goodman_Legacy_03.Bacon_PP_Goodman_Biconditional_Classification"
begin

section \<open>Goodman T1: WI collapses to Inv\<close>

definition pp_biconditional_member :: "oterm \<Rightarrow> oterm" where
  "pp_biconditional_member Z =
    Exists Prop
      (Conj
        (pp_pure Prop (Var 0))
        (Eq pp_unary_ty
          (shift Z)
          (pp_biconditional_operator (Var 0))))"

definition pp_WI :: oterm where
  "pp_WI =
    Forall pp_unary_ty
      (Imp
        (pp_group_member (Var 0))
        (pp_biconditional_member (Var 0)))"

definition pp_T1_WI_axioms :: "oterm set" where
  "pp_T1_WI_axioms = insert pp_WI pp_T1_axioms"

lemma typed_pp_biconditional_member:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_biconditional_member Z : Prop"
proof -
  have Z_shift:
    "Prop # \<Gamma> \<turnstile> shift Z : pp_unary_ty"
    using Z_type by (rule typed_shift_ctx)
  have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have op_type:
    "Prop # \<Gamma> \<turnstile>
      pp_biconditional_operator (Var 0) : pp_unary_ty"
    using v_type by (rule typed_pp_biconditional_operator)
  show ?thesis
    unfolding pp_biconditional_member_def
    using typed_pp_pure[OF v_type] Z_shift op_type
    by (intro has_type.Exists has_type.Conj has_type.Eq)
qed

lemma typed_pp_WI:
  "\<Gamma> \<turnstile> pp_WI : Prop"
  unfolding pp_WI_def
  using typed_pp_group_member[
      of "pp_unary_ty # \<Gamma>" "Var 0"]
    typed_pp_biconditional_member[
      of "pp_unary_ty # \<Gamma>" "Var 0"]
  by (intro has_type.Forall has_type.Imp has_type.Var)
    (simp_all add: lookup_def)

lemma pp_WI_in_T1_WI_axioms:
  "pp_WI \<in> pp_T1_WI_axioms"
  unfolding pp_T1_WI_axioms_def by simp

lemma pp_T1_axioms_subset_T1_WI_axioms:
  "pp_T1_axioms \<subseteq> pp_T1_WI_axioms"
  unfolding pp_T1_WI_axioms_def by blast

theorem CEV_Goodman_T1_biconditional_member_classification:
  assumes T1: "pp_T1_axioms \<subseteq> T"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_biconditional_member Z)
      (Disj
        (Eq pp_unary_ty Z pp_identity_operator)
        (Eq pp_unary_ty Z pp_negation_operator))"
proof -
  let ?Q =
    "Disj
      (Eq pp_unary_ty Z pp_identity_operator)
      (Eq pp_unary_ty Z pp_negation_operator)"
  let ?A = "Var 0"
  let ?ZA =
    "Eq pp_unary_ty
      (shift Z)
      (pp_biconditional_operator ?A)"
  let ?body = "Conj (pp_pure Prop ?A) ?ZA"
  let ?AI =
    "Eq pp_unary_ty
      (pp_biconditional_operator ?A)
      pp_identity_operator"
  let ?AN =
    "Eq pp_unary_ty
      (pp_biconditional_operator ?A)
      pp_negation_operator"
  let ?ZI =
    "Eq pp_unary_ty (shift Z) pp_identity_operator"
  let ?ZN =
    "Eq pp_unary_ty (shift Z) pp_negation_operator"
  let ?QT = "Disj ?ZI ?ZN"
  have A_type: "Prop # \<Gamma> \<turnstile> ?A : Prop"
    by (rule typed_var0)
  have Z_shift:
    "Prop # \<Gamma> \<turnstile> shift Z : pp_unary_ty"
    using Z_type by (rule typed_shift_ctx)
  have op_type:
    "Prop # \<Gamma> \<turnstile>
      pp_biconditional_operator ?A : pp_unary_ty"
    using A_type by (rule typed_pp_biconditional_operator)
  have body_type: "Prop # \<Gamma> \<turnstile> ?body : Prop"
    using typed_pp_pure[OF A_type] Z_shift op_type
    by (intro has_type.Conj has_type.Eq)
  have Q_type: "\<Gamma> \<turnstile> ?Q : Prop"
    using Z_type typed_pp_identity_operator typed_pp_negation_operator
    by (intro has_type.Disj has_type.Eq)
  have bound:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?body (shift ?Q)"
  proof -
    have d_body:
      "Prop # \<Gamma> ; T ; {?body}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?body"
      using body_type
      by (intro CEV_axiom_from.Assumption) simp
    have d_pure:
      "Prop # \<Gamma> ; T ; {?body}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop ?A"
      using d_body by (rule CEV_axiom_from_conj_left)
    have d_ZA:
      "Prop # \<Gamma> ; T ; {?body}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?ZA"
      using d_body by (rule CEV_axiom_from_conj_right)
    have classification:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (pp_pure Prop ?A) (Disj ?AI ?AN)"
      using CEV_Goodman_T1_biconditional_operator_classification[
        OF T1 A_type] .
    have d_class:
      "Prop # \<Gamma> ; T ; {?body}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Disj ?AI ?AN"
      using d_pure CEV_axiom_from.Theorem[OF classification]
      by (rule CEV_axiom_from.MP)
    have AI_imp:
      "Prop # \<Gamma> ; T ; {?body}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?AI ?QT"
    proof -
      have AI_type: "Prop # \<Gamma> \<turnstile> ?AI : Prop"
        using op_type typed_pp_identity_operator by (rule has_type.Eq)
      have d_AI:
        "Prop # \<Gamma> ; T ; insert ?AI {?body}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?AI"
        using AI_type by (intro CEV_axiom_from.Assumption) simp
      have d_ZA':
        "Prop # \<Gamma> ; T ; insert ?AI {?body}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?ZA"
        using d_ZA by (rule CEV_axiom_from_mono) simp
      have d_ZI:
        "Prop # \<Gamma> ; T ; insert ?AI {?body}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?ZI"
        using Z_shift op_type typed_pp_identity_operator d_ZA' d_AI
        by (rule CEV_axiom_from_eq_trans)
      have d_QT:
        "Prop # \<Gamma> ; T ; insert ?AI {?body}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?QT"
        using d_ZI
      proof -
        have ZI_type: "Prop # \<Gamma> \<turnstile> ?ZI : Prop"
          using Z_shift typed_pp_identity_operator by (rule has_type.Eq)
        have ZN_type: "Prop # \<Gamma> \<turnstile> ?ZN : Prop"
          using Z_shift typed_pp_negation_operator by (rule has_type.Eq)
        have taut:
          "Prop # \<Gamma> \<turnstile>\<^sub>CEV Imp ?ZI ?QT"
          using ZI_type ZN_type
          by (intro CEV_proves.CE CE_proves.C C_proves.H
              H_proves.PC prop_tautology_disj_left_intro)
        show ?thesis
          using d_ZI
            CEV_axiom_from.Theorem[
              OF CEV_axiom_proves.Base[OF taut]]
          by (rule CEV_axiom_from.MP)
      qed
      show ?thesis
        using AI_type d_QT by (rule CEV_axiom_from_deduction)
    qed
    have AN_imp:
      "Prop # \<Gamma> ; T ; {?body}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?AN ?QT"
    proof -
      have AN_type: "Prop # \<Gamma> \<turnstile> ?AN : Prop"
        using op_type typed_pp_negation_operator by (rule has_type.Eq)
      have d_AN:
        "Prop # \<Gamma> ; T ; insert ?AN {?body}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?AN"
        using AN_type by (intro CEV_axiom_from.Assumption) simp
      have d_ZA':
        "Prop # \<Gamma> ; T ; insert ?AN {?body}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?ZA"
        using d_ZA by (rule CEV_axiom_from_mono) simp
      have d_ZN:
        "Prop # \<Gamma> ; T ; insert ?AN {?body}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?ZN"
        using Z_shift op_type typed_pp_negation_operator d_ZA' d_AN
        by (rule CEV_axiom_from_eq_trans)
      have d_QT:
        "Prop # \<Gamma> ; T ; insert ?AN {?body}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?QT"
        using d_ZN
      proof -
        have ZI_type: "Prop # \<Gamma> \<turnstile> ?ZI : Prop"
          using Z_shift typed_pp_identity_operator by (rule has_type.Eq)
        have ZN_type: "Prop # \<Gamma> \<turnstile> ?ZN : Prop"
          using Z_shift typed_pp_negation_operator by (rule has_type.Eq)
        have taut:
          "Prop # \<Gamma> \<turnstile>\<^sub>CEV Imp ?ZN ?QT"
          using ZI_type ZN_type
          by (intro CEV_proves.CE CE_proves.C C_proves.H
              H_proves.PC prop_tautology_disj_right_intro)
        show ?thesis
          using d_ZN
            CEV_axiom_from.Theorem[
              OF CEV_axiom_proves.Base[OF taut]]
          by (rule CEV_axiom_from.MP)
      qed
      show ?thesis
        using AN_type d_QT by (rule CEV_axiom_from_deduction)
    qed
    have finish:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        Imp (Disj ?AI ?AN)
          (Imp (Imp ?AI ?QT)
            (Imp (Imp ?AN ?QT) ?QT))"
    proof (rule CEV_prop_tautology)
      have AI_type: "Prop # \<Gamma> \<turnstile> ?AI : Prop"
        using op_type typed_pp_identity_operator by (rule has_type.Eq)
      have AN_type: "Prop # \<Gamma> \<turnstile> ?AN : Prop"
        using op_type typed_pp_negation_operator by (rule has_type.Eq)
      have QT_type: "Prop # \<Gamma> \<turnstile> ?QT : Prop"
        using Z_shift typed_pp_identity_operator
          typed_pp_negation_operator
        by (intro has_type.Disj has_type.Eq)
      show "prop_tautology (Prop # \<Gamma>)
        (Imp (Disj ?AI ?AN)
          (Imp (Imp ?AI ?QT)
            (Imp (Imp ?AN ?QT) ?QT)))"
        unfolding prop_tautology_def
        using AI_type AN_type QT_type
        by (auto simp: prop_eval.simps)
    qed
    have d_finish:
      "Prop # \<Gamma> ; T ; {?body}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Imp (Disj ?AI ?AN)
            (Imp (Imp ?AI ?QT)
              (Imp (Imp ?AN ?QT) ?QT))"
      using finish
      by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
    have s1:
      "Prop # \<Gamma> ; T ; {?body}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Imp (Imp ?AI ?QT)
            (Imp (Imp ?AN ?QT) ?QT)"
      using d_class d_finish by (rule CEV_axiom_from.MP)
    have s2:
      "Prop # \<Gamma> ; T ; {?body}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Imp (Imp ?AN ?QT) ?QT"
      using AI_imp s1 by (rule CEV_axiom_from.MP)
    have d_QT:
      "Prop # \<Gamma> ; T ; {?body}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?QT"
      using AN_imp s2 by (rule CEV_axiom_from.MP)
    have body_imp:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?body ?QT"
      using body_type d_QT by (rule CEV_axiom_from_singleton_imp)
    show ?thesis
      using body_imp
      by (simp add: shift_def pp_unary_ty_def
        pp_identity_operator_def pp_negation_operator_def)
  qed
  have eliminated:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Exists Prop ?body) ?Q"
    using body_type Q_type bound
    by (rule CEV_axiom_proves.Inst)
  show ?thesis
    using eliminated
    unfolding pp_biconditional_member_def .
qed

lemma pp_T1_identity_purity_axiom:
  "pp_pure pp_unary_ty pp_identity_operator \<in> pp_T1_axioms"
  unfolding pp_T1_axioms_def
  using pp_identity_operator_purity_axiom by blast

lemma CEV_group_member_of_pure_self_inverse:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and pure_Z:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty Z"
    and involution:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Eq pp_unary_ty
          (pp_compose Z Z)
          pp_identity_operator"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_group_member Z"
proof -
  let ?body =
    "Conj
      (pp_pure pp_unary_ty (Var 0))
      (Conj
        (Eq pp_unary_ty
          (pp_compose (shift Z) (Var 0))
          pp_identity_operator)
        (Eq pp_unary_ty
          (pp_compose (Var 0) (shift Z))
          pp_identity_operator))"
  have equations:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Conj
        (Eq pp_unary_ty
          (pp_compose Z Z)
          pp_identity_operator)
        (Eq pp_unary_ty
          (pp_compose Z Z)
          pp_identity_operator)"
    using involution involution by (rule CEV_axiom_conj_intro)
  have witness:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Conj
        (pp_pure pp_unary_ty Z)
        (Conj
          (Eq pp_unary_ty
            (pp_compose Z Z)
            pp_identity_operator)
          (Eq pp_unary_ty
            (pp_compose Z Z)
            pp_identity_operator))"
    using pure_Z equations by (rule CEV_axiom_conj_intro)
  have body_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?body : Prop"
  proof -
    have Z_shift:
      "pp_unary_ty # \<Gamma> \<turnstile> shift Z : pp_unary_ty"
      using Z_type by (rule typed_shift_ctx)
    have v_type:
      "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
      by (rule typed_var0)
    have Zv_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_compose (shift Z) (Var 0) : pp_unary_ty"
      using Z_shift v_type by (rule typed_pp_compose)
    have vZ_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_compose (Var 0) (shift Z) : pp_unary_ty"
      using v_type Z_shift by (rule typed_pp_compose)
    show ?thesis
      using typed_pp_pure[OF v_type] Zv_type vZ_type
        typed_pp_identity_operator
      by (intro has_type.Conj has_type.Eq)
  qed
  have eg_raw:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (subst0 Z ?body) (Exists pp_unary_ty ?body)"
    using body_type Z_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.EG)
  have subst_left:
    "subst (case_nat Z Var)
      (pp_compose (shift Z) (Var 0)) =
      pp_compose Z Z"
    by (simp add: pp_compose_def subst_lift_shift)
  have subst_right:
    "subst (case_nat Z Var)
      (pp_compose (Var 0) (shift Z)) =
      pp_compose Z Z"
    by (simp add: pp_compose_def subst_lift_shift)
  have subst_id:
    "subst (case_nat Z Var) pp_identity_operator =
      pp_identity_operator"
    by (simp add: pp_identity_operator_def)
  have eg:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Conj
          (pp_pure pp_unary_ty Z)
          (Conj
            (Eq pp_unary_ty
              (pp_compose Z Z)
              pp_identity_operator)
            (Eq pp_unary_ty
              (pp_compose Z Z)
              pp_identity_operator)))
        (pp_reversible Z)"
    using eg_raw
    unfolding pp_reversible_def
    by (intro CEV_axiom_proves.Base)
      (simp add: subst0_def pp_pure_def pp_Pure_def
        subst_left subst_right subst_id)
  have reversible:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_reversible Z"
    using witness eg by (rule CEV_axiom_proves.MP)
  show ?thesis
    unfolding pp_group_member_def
    using pure_Z reversible by (rule CEV_axiom_conj_intro)
qed

theorem pp_identity_operator_group_member_T1:
  assumes T1: "pp_T1_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_group_member pp_identity_operator"
proof -
  have pure:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty pp_identity_operator"
  proof -
    have core:
      "\<Gamma> ; pp_T1_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty pp_identity_operator"
      using pp_T1_identity_purity_axiom
        typed_pp_pure[OF typed_pp_identity_operator]
      by (rule CEV_axiom_proves.Axiom)
    show ?thesis
      using core T1 by (rule CEV_axiom_proves_mono)
  qed
  have involution:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq pp_unary_ty
        (pp_compose pp_identity_operator pp_identity_operator)
        pp_identity_operator"
    using CEV_pp_compose_left_identity[
      OF typed_pp_identity_operator]
    by (rule CEV_axiom_proves.Base)
  show ?thesis
    using typed_pp_identity_operator pure involution
    by (rule CEV_group_member_of_pure_self_inverse)
qed

theorem pp_negation_operator_group_member_T1:
  assumes T1: "pp_T1_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_group_member pp_negation_operator"
proof -
  have pure:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty pp_negation_operator"
  proof -
    have core:
      "\<Gamma> ; pp_T1_axioms \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty pp_negation_operator"
      using pp_T1_negation_purity_axiom
        typed_pp_pure[OF typed_pp_negation_operator]
      by (rule CEV_axiom_proves.Axiom)
    show ?thesis
      using core T1 by (rule CEV_axiom_proves_mono)
  qed
  have involution:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq pp_unary_ty
        (pp_compose pp_negation_operator pp_negation_operator)
        pp_identity_operator"
    using CEV_pp_negation_involution
    by (rule CEV_axiom_proves.Base)
  show ?thesis
    using typed_pp_negation_operator pure involution
    by (rule CEV_group_member_of_pure_self_inverse)
qed

definition pp_group_member_predicate :: oterm where
  "pp_group_member_predicate =
    Lam pp_unary_ty (pp_group_member (Var 0))"

lemma typed_pp_group_member_predicate:
  "\<Gamma> \<turnstile> pp_group_member_predicate :
    pp_unary_ty \<rightarrow>\<^sub>o Prop"
  unfolding pp_group_member_predicate_def
  using typed_pp_group_member[
    of "pp_unary_ty # \<Gamma>" "Var 0"]
  by (intro has_type.Lam has_type.Var)
    (simp add: lookup_def)

lemma pp_group_member_predicate_beta:
  "compatible_step beta_contract
    (App pp_group_member_predicate Z)
    (pp_group_member Z)"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty (pp_group_member (Var 0)))
        Z)
      (subst0 Z (pp_group_member (Var 0)))"
    by (rule beta_contract.beta)
  show "beta_contract
    (App pp_group_member_predicate Z)
    (pp_group_member Z)"
    using step
    unfolding pp_group_member_predicate_def
      pp_group_member_def pp_reversible_def
      pp_compose_def pp_pure_def pp_Pure_def
    by (simp add: subst0_def subst_lift_shift
      pp_identity_operator_def)
qed

lemma CEV_axiom_from_group_member_transport:
  assumes A_type: "\<Gamma> \<turnstile> A : pp_unary_ty"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and d_eq:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty A B"
    and d_group_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_group_member A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_group_member B"
proof -
  let ?P = pp_group_member_predicate
  have P_type:
    "\<Gamma> \<turnstile> ?P : pp_unary_ty \<rightarrow>\<^sub>o Prop"
    by (rule typed_pp_group_member_predicate)
  have PA_type:
    "\<Gamma> \<turnstile> App ?P A : Prop"
    using P_type A_type by (rule has_type.App)
  have PB_type:
    "\<Gamma> \<turnstile> App ?P B : Prop"
    using P_type B_type by (rule has_type.App)
  have GA_type: "\<Gamma> \<turnstile> pp_group_member A : Prop"
    using A_type by (rule typed_pp_group_member)
  have GB_type: "\<Gamma> \<turnstile> pp_group_member B : Prop"
    using B_type by (rule typed_pp_group_member)
  have ll:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Eq pp_unary_ty A B)
        (Imp (App ?P A) (App ?P B))"
    using A_type B_type P_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have d_ll:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Eq pp_unary_ty A B)
        (Imp (App ?P A) (App ?P B))"
    using ll
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_app_imp:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (App ?P A) (App ?P B)"
    using d_eq d_ll by (rule CEV_axiom_from.MP)
  have beta_A:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App ?P A \<longleftrightarrow>\<^sub>o pp_group_member A)"
    using PA_type GA_type pp_group_member_predicate_beta
    by (rule CEV_beta_step)
  have GA_to_PA:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (pp_group_member A) (App ?P A)"
    using PA_type GA_type beta_A by (rule CEV_beta_right_imp)
  have d_PA:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App ?P A"
    using d_group_A
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[OF GA_to_PA]]
    by (rule CEV_axiom_from.MP)
  have d_PB:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App ?P B"
    using d_PA d_app_imp by (rule CEV_axiom_from.MP)
  have beta_B:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App ?P B \<longleftrightarrow>\<^sub>o pp_group_member B)"
    using PB_type GB_type pp_group_member_predicate_beta
    by (rule CEV_beta_step)
  have PB_to_GB:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (App ?P B) (pp_group_member B)"
    using PB_type GB_type beta_B by (rule CEV_beta_left_imp)
  show ?thesis
    using d_PB
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[OF PB_to_GB]]
    by (rule CEV_axiom_from.MP)
qed

theorem CEV_Goodman_T1_WI_collapses_to_Inv:
  assumes axioms: "pp_T1_WI_axioms \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_Inv"
proof -
  have T1: "pp_T1_axioms \<subseteq> T"
    using axioms pp_T1_axioms_subset_T1_WI_axioms by blast
  have WI_in: "pp_WI \<in> T"
    using axioms pp_WI_in_T1_WI_axioms by blast
  let ?Z = "Var 0"
  let ?G = "pp_group_member ?Z"
  let ?M = "pp_biconditional_member ?Z"
  let ?ZI =
    "Eq pp_unary_ty ?Z pp_identity_operator"
  let ?ZN =
    "Eq pp_unary_ty ?Z pp_negation_operator"
  let ?D = "Disj ?ZI ?ZN"
  let ?Q = "?G \<longleftrightarrow>\<^sub>o ?D"
  have Z_type: "[pp_unary_ty] \<turnstile> ?Z : pp_unary_ty"
    by (rule typed_var0)
  have G_type: "[pp_unary_ty] \<turnstile> ?G : Prop"
    using Z_type by (rule typed_pp_group_member)
  have M_type: "[pp_unary_ty] \<turnstile> ?M : Prop"
    using Z_type by (rule typed_pp_biconditional_member)
  have ZI_type: "[pp_unary_ty] \<turnstile> ?ZI : Prop"
    using Z_type typed_pp_identity_operator by (rule has_type.Eq)
  have ZN_type: "[pp_unary_ty] \<turnstile> ?ZN : Prop"
    using Z_type typed_pp_negation_operator by (rule has_type.Eq)
  have D_type: "[pp_unary_ty] \<turnstile> ?D : Prop"
    using ZI_type ZN_type by (rule has_type.Disj)
  have Q_type: "[pp_unary_ty] \<turnstile> ?Q : Prop"
    using G_type D_type by (intro has_type.Conj has_type.Imp)
  have d_WI:
    "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_WI"
    using WI_in typed_pp_WI by (rule CEV_axiom_proves.Axiom)
  have d_WI_forall:
    "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall pp_unary_ty
        (Imp
          (pp_group_member (Var 0))
          (pp_biconditional_member (Var 0)))"
    using d_WI unfolding pp_WI_def .
  have WI_body_type:
    "[pp_unary_ty, pp_unary_ty] \<turnstile>
      Imp
        (pp_group_member (Var 0))
        (pp_biconditional_member (Var 0)) : Prop"
    using typed_pp_group_member[
        OF typed_var0[
          where \<sigma> = pp_unary_ty
            and \<Gamma> = "[pp_unary_ty]"]]
      typed_pp_biconditional_member[
        OF typed_var0[
          where \<sigma> = pp_unary_ty
            and \<Gamma> = "[pp_unary_ty]"]]
    by (rule has_type.Imp)
  have d_WI_instance:
    "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?G ?M"
  proof -
    have raw:
      "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+
        subst0 ?Z
          (Imp
            (pp_group_member (Var 0))
            (pp_biconditional_member (Var 0)))"
      using WI_body_type Z_type d_WI_forall
      by (rule CEV_axiom_UI)
    show ?thesis
      using raw
      by (simp add: subst0_def pp_group_member_def
        pp_reversible_def pp_compose_def
        pp_biconditional_member_def
        pp_biconditional_operator_def
        pp_biconditional_builder_def
        pp_pure_def pp_Pure_def
        pp_identity_operator_def subst_lift_shift)
  qed
  have member_class:
    "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?M ?D"
    using CEV_Goodman_T1_biconditional_member_classification[
      OF T1 Z_type] .
  have G_to_D:
    "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?G ?D"
  proof -
    have d_G:
      "[pp_unary_ty] ; T ; {?G}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?G"
      using G_type
      by (intro CEV_axiom_from.Assumption) simp
    have d_M:
      "[pp_unary_ty] ; T ; {?G}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?M"
      using d_G CEV_axiom_from.Theorem[OF d_WI_instance]
      by (rule CEV_axiom_from.MP)
    have d_D:
      "[pp_unary_ty] ; T ; {?G}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?D"
      using d_M CEV_axiom_from.Theorem[OF member_class]
      by (rule CEV_axiom_from.MP)
    show ?thesis
      using G_type d_D by (rule CEV_axiom_from_singleton_imp)
  qed
  have group_I:
    "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_group_member pp_identity_operator"
    using pp_identity_operator_group_member_T1[OF T1] .
  have group_N:
    "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_group_member pp_negation_operator"
    using pp_negation_operator_group_member_T1[OF T1] .
  have D_to_G:
    "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?D ?G"
  proof -
    have d_D:
      "[pp_unary_ty] ; T ; {?D}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?D"
      using D_type
      by (intro CEV_axiom_from.Assumption) simp
    have ZI_imp:
      "[pp_unary_ty] ; T ; {?D}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?ZI ?G"
    proof -
      have d_ZI:
        "[pp_unary_ty] ; T ; insert ?ZI {?D}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?ZI"
        using ZI_type
        by (intro CEV_axiom_from.Assumption) simp
      have d_IZ:
        "[pp_unary_ty] ; T ; insert ?ZI {?D}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
            Eq pp_unary_ty pp_identity_operator ?Z"
        using Z_type typed_pp_identity_operator d_ZI
        by (rule CEV_axiom_from_eq_sym)
      have d_group_I:
        "[pp_unary_ty] ; T ; insert ?ZI {?D}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
            pp_group_member pp_identity_operator"
        using group_I by (rule CEV_axiom_from.Theorem)
      have d_G:
        "[pp_unary_ty] ; T ; insert ?ZI {?D}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?G"
        using typed_pp_identity_operator Z_type d_IZ d_group_I
        by (rule CEV_axiom_from_group_member_transport)
      show ?thesis
        using ZI_type d_G by (rule CEV_axiom_from_deduction)
    qed
    have ZN_imp:
      "[pp_unary_ty] ; T ; {?D}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?ZN ?G"
    proof -
      have d_ZN:
        "[pp_unary_ty] ; T ; insert ?ZN {?D}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?ZN"
        using ZN_type
        by (intro CEV_axiom_from.Assumption) simp
      have d_NZ:
        "[pp_unary_ty] ; T ; insert ?ZN {?D}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
            Eq pp_unary_ty pp_negation_operator ?Z"
        using Z_type typed_pp_negation_operator d_ZN
        by (rule CEV_axiom_from_eq_sym)
      have d_group_N:
        "[pp_unary_ty] ; T ; insert ?ZN {?D}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
            pp_group_member pp_negation_operator"
        using group_N by (rule CEV_axiom_from.Theorem)
      have d_G:
        "[pp_unary_ty] ; T ; insert ?ZN {?D}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?G"
        using typed_pp_negation_operator Z_type d_NZ d_group_N
        by (rule CEV_axiom_from_group_member_transport)
      show ?thesis
        using ZN_type d_G by (rule CEV_axiom_from_deduction)
    qed
    have finish:
      "[pp_unary_ty] \<turnstile>\<^sub>CEV
        Imp ?D
          (Imp (Imp ?ZI ?G)
            (Imp (Imp ?ZN ?G) ?G))"
    proof (rule CEV_prop_tautology)
      show "prop_tautology [pp_unary_ty]
        (Imp ?D
          (Imp (Imp ?ZI ?G)
            (Imp (Imp ?ZN ?G) ?G)))"
        unfolding prop_tautology_def
        using ZI_type ZN_type G_type D_type
        by (auto simp: prop_eval.simps)
    qed
    have d_finish:
      "[pp_unary_ty] ; T ; {?D}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Imp ?D
            (Imp (Imp ?ZI ?G)
              (Imp (Imp ?ZN ?G) ?G))"
      using finish
      by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
    have s1:
      "[pp_unary_ty] ; T ; {?D}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Imp (Imp ?ZI ?G)
            (Imp (Imp ?ZN ?G) ?G)"
      using d_D d_finish by (rule CEV_axiom_from.MP)
    have s2:
      "[pp_unary_ty] ; T ; {?D}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Imp (Imp ?ZN ?G) ?G"
      using ZI_imp s1 by (rule CEV_axiom_from.MP)
    have d_G:
      "[pp_unary_ty] ; T ; {?D}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?G"
      using ZN_imp s2 by (rule CEV_axiom_from.MP)
    show ?thesis
      using D_type d_G by (rule CEV_axiom_from_singleton_imp)
  qed
  have body:
    "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+ ?Q"
    using G_to_D D_to_G by (rule CEV_axiom_conj_intro)
  have guarded:
    "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue ?Q"
    using typed_ObjTrue body by (rule CEV_axiom_imp_of_right)
  have generalized_imp:
    "[] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue (Forall pp_unary_ty ?Q)"
  proof (rule CEV_axiom_proves.Gen)
    show "[] \<turnstile> ObjTrue : Prop"
      by (rule typed_ObjTrue)
    show "[pp_unary_ty] \<turnstile> ?Q : Prop"
      by (rule Q_type)
    show "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ObjTrue) ?Q"
      using guarded by (simp add: ObjTrue_def shift_def)
  qed
  have d_true: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjTrue"
    by (rule CEV_axiom_proves_ObjTrue)
  have generalized:
    "[] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall pp_unary_ty ?Q"
    using d_true generalized_imp by (rule CEV_axiom_proves.MP)
  show ?thesis
    using generalized unfolding pp_Inv_def .
qed

end
