theory Bacon_PP_Goodman_Biconditional_Classification
  imports 
    "Goodman_Legacy_03.Bacon_PP_Goodman_Pure_Proposition_Triviality"
begin

section \<open>Goodman T1: classification of biconditional operators\<close>

definition pp_biconditional_builder :: oterm where
  "pp_biconditional_builder =
    Lam Prop
      (Lam Prop
        (Var 0 \<longleftrightarrow>\<^sub>o Var 1))"

definition pp_biconditional_operator :: "oterm \<Rightarrow> oterm" where
  "pp_biconditional_operator A =
    App pp_biconditional_builder A"

lemma typed_pp_biconditional_builder:
  "\<Gamma> \<turnstile> pp_biconditional_builder :
    Prop \<rightarrow>\<^sub>o pp_unary_ty"
  unfolding pp_biconditional_builder_def pp_unary_ty_def
  by (intro has_type.Lam has_type.Conj has_type.Imp has_type.Var)
    (simp_all add: lookup_def)

lemma typed_pp_biconditional_operator:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> pp_biconditional_operator A : pp_unary_ty"
  unfolding pp_biconditional_operator_def
  using typed_pp_biconditional_builder A_type
  by (rule has_type.App)

lemma pp_biconditional_operator_first_beta:
  "compatible_step beta_contract
    (pp_biconditional_operator A)
    (Lam Prop (Var 0 \<longleftrightarrow>\<^sub>o shift A))"
proof -
  have step:
    "beta_contract
      (App pp_biconditional_builder A)
      (subst0 A
        (Lam Prop (Var 0 \<longleftrightarrow>\<^sub>o Var 1)))"
    unfolding pp_biconditional_builder_def
    by (rule beta_contract.beta)
  show ?thesis
    using step
    by (intro compatible_step.root)
      (simp add: pp_biconditional_operator_def subst0_def shift_def)
qed

lemma pp_biconditional_operator_second_beta:
  "compatible_step beta_contract
    (App
      (Lam Prop (Var 0 \<longleftrightarrow>\<^sub>o shift A))
      p)
    (p \<longleftrightarrow>\<^sub>o A)"
proof -
  have step:
    "beta_contract
      (App
        (Lam Prop (Var 0 \<longleftrightarrow>\<^sub>o shift A))
        p)
      (subst0 p (Var 0 \<longleftrightarrow>\<^sub>o shift A))"
    by (rule beta_contract.beta)
  show ?thesis
    using step
    by (intro compatible_step.root)
      (simp add: subst0_def)
qed

lemma CEV_pp_biconditional_operator_apply:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    (App (pp_biconditional_operator A) p
      \<longleftrightarrow>\<^sub>o
      (p \<longleftrightarrow>\<^sub>o A))"
proof -
  let ?L = "Lam Prop (Var 0 \<longleftrightarrow>\<^sub>o shift A)"
  have op_type:
    "\<Gamma> \<turnstile> pp_biconditional_operator A : pp_unary_ty"
    using A_type by (rule typed_pp_biconditional_operator)
  have L_type: "\<Gamma> \<turnstile> ?L : pp_unary_ty"
    unfolding pp_unary_ty_def
    using typed_shift_ctx[OF A_type]
    by (intro has_type.Lam has_type.Conj has_type.Imp has_type.Var)
      (simp_all add: lookup_def)
  have left_type:
    "\<Gamma> \<turnstile> App (pp_biconditional_operator A) p : Prop"
    using op_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have middle_type: "\<Gamma> \<turnstile> App ?L p : Prop"
    using L_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have right_type:
    "\<Gamma> \<turnstile> (p \<longleftrightarrow>\<^sub>o A) : Prop"
    using p_type A_type by (intro has_type.Conj has_type.Imp)
  have first:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App (pp_biconditional_operator A) p
        \<longleftrightarrow>\<^sub>o App ?L p)"
    using left_type middle_type
      compatible_step.App_left[
        OF pp_biconditional_operator_first_beta]
    by (rule CEV_beta_step)
  have second:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App ?L p \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o A))"
    using middle_type right_type
      pp_biconditional_operator_second_beta
    by (rule CEV_beta_step)
  show ?thesis
    using left_type middle_type right_type first second
    by (rule CEV_biconditional_trans)
qed

lemma CEV_biconditional_with_ObjTrue:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    ((p \<longleftrightarrow>\<^sub>o ObjTrue) \<longleftrightarrow>\<^sub>o p)"
proof -
  let ?I = "p \<longleftrightarrow>\<^sub>o ObjTrue"
  have I_type: "\<Gamma> \<turnstile> ?I : Prop"
    using p_type typed_ObjTrue
    by (intro has_type.Conj has_type.Imp)
  have left_to_right: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?I p"
  proof -
    have local_I: "CEV_from \<Gamma> ?I ?I"
      using I_type by (rule CEV_from.Assumption)
    have right_imp:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp ?I (Imp ObjTrue p)"
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
        (auto simp: prop_tautology_def prop_eval.simps
          intro: p_type typed_ObjTrue)
    have local_true_imp_p: "CEV_from \<Gamma> ?I (Imp ObjTrue p)"
      using local_I CEV_from.Theorem[OF right_imp]
      by (rule CEV_from.MP)
    have local_true: "CEV_from \<Gamma> ?I ObjTrue"
      using CEV_proves_ObjTrue by (rule CEV_from.Theorem)
    have local_p: "CEV_from \<Gamma> ?I p"
      using local_true local_true_imp_p by (rule CEV_from.MP)
    show ?thesis
      using local_p I_type by (rule CEV_from_deduction)
  qed
  have right_to_left: "\<Gamma> \<turnstile>\<^sub>CEV Imp p ?I"
  proof -
    have local_p: "CEV_from \<Gamma> p p"
      using p_type by (rule CEV_from.Assumption)
    have p_imp_true: "\<Gamma> \<turnstile>\<^sub>CEV Imp p ObjTrue"
      using p_type CEV_proves_ObjTrue
      by (rule CEV_imp_of_right_theorem)
    have taut:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp p (Imp ObjTrue p)"
      using p_type typed_ObjTrue by (rule CEV_taut_imp)
    have local_true_imp_p: "CEV_from \<Gamma> p (Imp ObjTrue p)"
      using local_p CEV_from.Theorem[OF taut]
      by (rule CEV_from.MP)
    have intro:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Imp p ObjTrue)
          (Imp (Imp ObjTrue p) ?I)"
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
        (auto simp: prop_tautology_def prop_eval.simps
          intro: p_type typed_ObjTrue I_type)
    have local_step:
      "CEV_from \<Gamma> p (Imp (Imp ObjTrue p) ?I)"
      using CEV_from.Theorem[OF p_imp_true]
        CEV_from.Theorem[OF intro]
      by (rule CEV_from.MP)
    have local_I: "CEV_from \<Gamma> p ?I"
      using local_true_imp_p local_step by (rule CEV_from.MP)
    show ?thesis
      using local_I p_type by (rule CEV_from_deduction)
  qed
  show ?thesis
    using left_to_right right_to_left by (rule CEV_conj_intro)
qed

lemma CEV_biconditional_with_ObjFalse:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    ((p \<longleftrightarrow>\<^sub>o ObjFalse) \<longleftrightarrow>\<^sub>o Neg p)"
proof -
  let ?I = "p \<longleftrightarrow>\<^sub>o ObjFalse"
  have I_type: "\<Gamma> \<turnstile> ?I : Prop"
    using p_type typed_ObjFalse
    by (intro has_type.Conj has_type.Imp)
  have false_imp_p: "\<Gamma> \<turnstile>\<^sub>CEV Imp ObjFalse p"
  proof -
    have taut:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp ObjTrue (Imp ObjFalse p)"
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
        (auto simp: prop_tautology_def prop_eval.simps ObjFalse_def
          intro: p_type typed_ObjTrue)
    show ?thesis
      using CEV_proves_ObjTrue taut by (rule CEV_proves.MP)
  qed
  have left_to_right: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?I (Neg p)"
  proof -
    have neg_type: "\<Gamma> \<turnstile> Neg p : Prop"
      using p_type by (rule has_type.Neg)
    have left:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp ?I (Imp p ObjFalse)"
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
        (auto simp: prop_tautology_def prop_eval.simps
          intro: p_type typed_ObjFalse)
    have convert:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp p ObjFalse) (Neg p)"
      using p_type by (rule CEV_proves_imp_false_to_neg)
    have taut:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (Imp ?I (Imp p ObjFalse))
          (Imp
            (Imp (Imp p ObjFalse) (Neg p))
            (Imp ?I (Neg p)))"
    proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
      have formula_type:
        "\<Gamma> \<turnstile>
          Imp
            (Imp ?I (Imp p ObjFalse))
            (Imp
              (Imp (Imp p ObjFalse) (Neg p))
              (Imp ?I (Neg p))) : Prop"
        using I_type p_type typed_ObjFalse neg_type
        by (intro has_type.Imp)
      moreover have
        "\<forall>v. prop_eval v
          (Imp
            (Imp ?I (Imp p ObjFalse))
            (Imp
              (Imp (Imp p ObjFalse) (Neg p))
              (Imp ?I (Neg p))))"
        apply (simp only: prop_eval.simps)
        by blast
      ultimately show
        "prop_tautology \<Gamma>
          (Imp
            (Imp ?I (Imp p ObjFalse))
            (Imp
              (Imp (Imp p ObjFalse) (Neg p))
              (Imp ?I (Neg p))))"
        unfolding prop_tautology_def by blast
    qed
    have step:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (Imp (Imp p ObjFalse) (Neg p))
          (Imp ?I (Neg p))"
      using left taut by (rule CEV_proves.MP)
    show ?thesis
      using convert step by (rule CEV_proves.MP)
  qed
  have right_to_left: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Neg p) ?I"
  proof -
    have neg_type: "\<Gamma> \<turnstile> Neg p : Prop"
      using p_type by (rule has_type.Neg)
    have local_neg: "CEV_from \<Gamma> (Neg p) (Neg p)"
      using neg_type by (rule CEV_from.Assumption)
    have explosion:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp (Neg p) (Imp p ObjFalse)"
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
        (auto simp: prop_tautology_def prop_eval.simps
          intro: p_type typed_ObjFalse)
    have local_p_imp_false:
      "CEV_from \<Gamma> (Neg p) (Imp p ObjFalse)"
      using local_neg CEV_from.Theorem[OF explosion]
      by (rule CEV_from.MP)
    have intro:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Imp p ObjFalse)
          (Imp (Imp ObjFalse p) ?I)"
    proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
      have formula_type:
        "\<Gamma> \<turnstile>
          Imp (Imp p ObjFalse)
            (Imp (Imp ObjFalse p) ?I) : Prop"
        using p_type typed_ObjFalse I_type
        by (intro has_type.Imp)
      moreover have
        "\<forall>v. prop_eval v
          (Imp (Imp p ObjFalse)
            (Imp (Imp ObjFalse p) ?I))"
        apply (simp only: prop_eval.simps)
        by blast
      ultimately show
        "prop_tautology \<Gamma>
          (Imp (Imp p ObjFalse)
            (Imp (Imp ObjFalse p) ?I))"
        unfolding prop_tautology_def by blast
    qed
    have local_step:
      "CEV_from \<Gamma> (Neg p) (Imp (Imp ObjFalse p) ?I)"
      using local_p_imp_false CEV_from.Theorem[OF intro]
      by (rule CEV_from.MP)
    have local_I: "CEV_from \<Gamma> (Neg p) ?I"
      using CEV_from.Theorem[OF false_imp_p] local_step
      by (rule CEV_from.MP)
    show ?thesis
      using local_I neg_type by (rule CEV_from_deduction)
  qed
  show ?thesis
    using left_to_right right_to_left by (rule CEV_conj_intro)
qed

lemma CEV_pp_biconditional_ObjTrue_eq_identity:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (pp_biconditional_operator ObjTrue)
      pp_identity_operator"
proof -
  have left_op_type:
    "\<Gamma> \<turnstile> pp_biconditional_operator ObjTrue :
      Prop \<rightarrow>\<^sub>o Prop"
    using typed_pp_biconditional_operator[OF typed_ObjTrue]
    by (simp add: pp_unary_ty_def)
  have right_op_type:
    "\<Gamma> \<turnstile> pp_identity_operator : Prop \<rightarrow>\<^sub>o Prop"
    using typed_pp_identity_operator
    by (simp add: pp_unary_ty_def)
  have op_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Eq (Prop \<rightarrow>\<^sub>o Prop)
        (pp_biconditional_operator ObjTrue)
        pp_identity_operator"
  proof (rule CEV_unary_equivalence[
      OF left_op_type right_op_type])
  let ?v = "Var 0"
  have v_type: "Prop # \<Gamma> \<turnstile> ?v : Prop"
    by (rule typed_var0)
  have left_type:
    "Prop # \<Gamma> \<turnstile>
      App (pp_biconditional_operator ObjTrue) ?v : Prop"
    using typed_pp_biconditional_operator[OF typed_ObjTrue] v_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have middle_type:
    "Prop # \<Gamma> \<turnstile> (?v \<longleftrightarrow>\<^sub>o ObjTrue) : Prop"
    using v_type typed_ObjTrue by (intro has_type.Conj has_type.Imp)
  have right_type:
    "Prop # \<Gamma> \<turnstile> App pp_identity_operator ?v : Prop"
    using typed_pp_identity_operator v_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have first:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (pp_biconditional_operator ObjTrue) ?v
        \<longleftrightarrow>\<^sub>o
        (?v \<longleftrightarrow>\<^sub>o ObjTrue))"
    using CEV_pp_biconditional_operator_apply[OF typed_ObjTrue v_type] .
  have second:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      ((?v \<longleftrightarrow>\<^sub>o ObjTrue) \<longleftrightarrow>\<^sub>o ?v)"
    using v_type by (rule CEV_biconditional_with_ObjTrue)
  have id_beta:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App pp_identity_operator ?v \<longleftrightarrow>\<^sub>o ?v)"
    using v_type by (rule CEV_pp_identity_apply)
  have v_id:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (?v \<longleftrightarrow>\<^sub>o App pp_identity_operator ?v)"
    using right_type v_type id_beta by (rule CEV_biconditional_sym)
  have first_two:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (pp_biconditional_operator ObjTrue) ?v
        \<longleftrightarrow>\<^sub>o ?v)"
    using left_type middle_type v_type first second
    by (rule CEV_biconditional_trans)
  have final:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (pp_biconditional_operator ObjTrue) ?v
        \<longleftrightarrow>\<^sub>o App pp_identity_operator ?v)"
    using left_type v_type right_type first_two v_id
    by (rule CEV_biconditional_trans)
  show "Prop # \<Gamma> \<turnstile>\<^sub>CEV
    (App (shift (pp_biconditional_operator ObjTrue)) (Var 0)
      \<longleftrightarrow>\<^sub>o
      App (shift pp_identity_operator) (Var 0))"
    using final
    by (simp add: shift_def pp_biconditional_operator_def
      pp_biconditional_builder_def pp_identity_operator_def
      ObjTrue_def)
  qed
  show ?thesis
    using op_eq by (simp add: pp_unary_ty_def)
qed

lemma CEV_pp_biconditional_ObjFalse_eq_negation:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (pp_biconditional_operator ObjFalse)
      pp_negation_operator"
proof -
  have left_op_type:
    "\<Gamma> \<turnstile> pp_biconditional_operator ObjFalse :
      Prop \<rightarrow>\<^sub>o Prop"
    using typed_pp_biconditional_operator[OF typed_ObjFalse]
    by (simp add: pp_unary_ty_def)
  have right_op_type:
    "\<Gamma> \<turnstile> pp_negation_operator : Prop \<rightarrow>\<^sub>o Prop"
    using typed_pp_negation_operator
    by (simp add: pp_unary_ty_def)
  have op_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Eq (Prop \<rightarrow>\<^sub>o Prop)
        (pp_biconditional_operator ObjFalse)
        pp_negation_operator"
  proof (rule CEV_unary_equivalence[
      OF left_op_type right_op_type])
  let ?v = "Var 0"
  have v_type: "Prop # \<Gamma> \<turnstile> ?v : Prop"
    by (rule typed_var0)
  have left_type:
    "Prop # \<Gamma> \<turnstile>
      App (pp_biconditional_operator ObjFalse) ?v : Prop"
    using typed_pp_biconditional_operator[OF typed_ObjFalse] v_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have middle_type:
    "Prop # \<Gamma> \<turnstile> (?v \<longleftrightarrow>\<^sub>o ObjFalse) : Prop"
    using v_type typed_ObjFalse by (intro has_type.Conj has_type.Imp)
  have neg_type: "Prop # \<Gamma> \<turnstile> Neg ?v : Prop"
    using v_type by (rule has_type.Neg)
  have right_type:
    "Prop # \<Gamma> \<turnstile> App pp_negation_operator ?v : Prop"
    using typed_pp_negation_operator v_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have first:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (pp_biconditional_operator ObjFalse) ?v
        \<longleftrightarrow>\<^sub>o
        (?v \<longleftrightarrow>\<^sub>o ObjFalse))"
    using CEV_pp_biconditional_operator_apply[OF typed_ObjFalse v_type] .
  have second:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      ((?v \<longleftrightarrow>\<^sub>o ObjFalse) \<longleftrightarrow>\<^sub>o Neg ?v)"
    using v_type by (rule CEV_biconditional_with_ObjFalse)
  have neg_beta_eq:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      Eq Prop (App pp_negation_operator ?v) (Neg ?v)"
    using v_type by (rule CEV_pp_negation_apply_eq)
  have neg_beta:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App pp_negation_operator ?v \<longleftrightarrow>\<^sub>o Neg ?v)"
    using right_type neg_type neg_beta_eq
    by (rule CEV_eq_prop_biconditional)
  have neg_app:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (Neg ?v \<longleftrightarrow>\<^sub>o App pp_negation_operator ?v)"
    using right_type neg_type neg_beta
    by (rule CEV_biconditional_sym)
  have first_two:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (pp_biconditional_operator ObjFalse) ?v
        \<longleftrightarrow>\<^sub>o Neg ?v)"
    using left_type middle_type neg_type first second
    by (rule CEV_biconditional_trans)
  have final:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (pp_biconditional_operator ObjFalse) ?v
        \<longleftrightarrow>\<^sub>o App pp_negation_operator ?v)"
    using left_type neg_type right_type first_two neg_app
    by (rule CEV_biconditional_trans)
  show "Prop # \<Gamma> \<turnstile>\<^sub>CEV
    (App (shift (pp_biconditional_operator ObjFalse)) (Var 0)
      \<longleftrightarrow>\<^sub>o
      App (shift pp_negation_operator) (Var 0))"
    using final
    by (simp add: shift_def pp_biconditional_operator_def
      pp_biconditional_builder_def pp_negation_operator_def
      ObjFalse_def ObjTrue_def)
  qed
  show ?thesis
    using op_eq by (simp add: pp_unary_ty_def)
qed

lemma CEV_axiom_biconditional_operator_eq_transport:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Eq Prop A B)
      (Eq pp_unary_ty
        (pp_biconditional_operator A)
        (pp_biconditional_operator B))"
proof -
  let ?E = "Eq Prop A B"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using A_type B_type by (rule has_type.Eq)
  have d_E:
    "\<Gamma> ; T ; {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using E_type by (intro CEV_axiom_from.Assumption) simp
  have d_ops:
    "\<Gamma> ; T ; {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty
        (pp_biconditional_operator A)
        (pp_biconditional_operator B)"
    unfolding pp_biconditional_operator_def
    using typed_pp_biconditional_builder A_type B_type d_E
    by (rule CEV_axiom_from_eq_app_right)
  show ?thesis
    using E_type d_ops by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_Goodman_T1_biconditional_operator_classification:
  assumes T1: "pp_T1_axioms \<subseteq> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_pure Prop A)
      (Disj
        (Eq pp_unary_ty
          (pp_biconditional_operator A)
          pp_identity_operator)
        (Eq pp_unary_ty
          (pp_biconditional_operator A)
          pp_negation_operator))"
proof -
  let ?P = "pp_pure Prop A"
  let ?ET = "Eq Prop A ObjTrue"
  let ?EF = "Eq Prop A ObjFalse"
  let ?OT =
    "Eq pp_unary_ty
      (pp_biconditional_operator A)
      pp_identity_operator"
  let ?OF =
    "Eq pp_unary_ty
      (pp_biconditional_operator A)
      pp_negation_operator"
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using A_type by (rule typed_pp_pure)
  have d_P:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have d_extreme:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Disj ?ET ?EF"
  proof -
    have d:
      "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_proposition_extreme A"
      using d_P
        CEV_axiom_from.Theorem[
          OF CEV_Goodman_T1_parameter[OF T1 A_type]]
      by (rule CEV_axiom_from.MP)
    show ?thesis
      using d unfolding pp_proposition_extreme_def .
  qed
  have ET_to_ops:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?ET
        (Eq pp_unary_ty
          (pp_biconditional_operator A)
          (pp_biconditional_operator ObjTrue))"
    using CEV_axiom_biconditional_operator_eq_transport[
      OF A_type typed_ObjTrue]
    by (rule CEV_axiom_from.Theorem)
  have op_true_eq:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty
        (pp_biconditional_operator ObjTrue)
        pp_identity_operator"
    using CEV_pp_biconditional_ObjTrue_eq_identity
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have ET_to_OT:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?ET ?OT"
  proof -
    have ET_type: "\<Gamma> \<turnstile> ?ET : Prop"
      using A_type typed_ObjTrue by (rule has_type.Eq)
    have d_ET:
      "\<Gamma> ; T ; insert ?ET {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?ET"
      using ET_type by (intro CEV_axiom_from.Assumption) simp
    have ops:
      "\<Gamma> ; T ; insert ?ET {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (pp_biconditional_operator A)
          (pp_biconditional_operator ObjTrue)"
      using d_ET
        CEV_axiom_from_mono[OF ET_to_ops, of "insert ?ET {?P}"]
      by (rule CEV_axiom_from.MP) simp
    have final:
      "\<Gamma> ; T ; insert ?ET {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?OT"
      using typed_pp_biconditional_operator[OF A_type]
        typed_pp_biconditional_operator[OF typed_ObjTrue]
        typed_pp_identity_operator ops
        CEV_axiom_from_mono[OF op_true_eq, of "insert ?ET {?P}"]
      by (rule CEV_axiom_from_eq_trans) simp
    show ?thesis
      using ET_type final by (rule CEV_axiom_from_deduction)
  qed
  have EF_to_ops:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?EF
        (Eq pp_unary_ty
          (pp_biconditional_operator A)
          (pp_biconditional_operator ObjFalse))"
    using CEV_axiom_biconditional_operator_eq_transport[
      OF A_type typed_ObjFalse]
    by (rule CEV_axiom_from.Theorem)
  have op_false_eq:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty
        (pp_biconditional_operator ObjFalse)
        pp_negation_operator"
    using CEV_pp_biconditional_ObjFalse_eq_negation
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have EF_to_OF:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?EF ?OF"
  proof -
    have EF_type: "\<Gamma> \<turnstile> ?EF : Prop"
      using A_type typed_ObjFalse by (rule has_type.Eq)
    have d_EF:
      "\<Gamma> ; T ; insert ?EF {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?EF"
      using EF_type by (intro CEV_axiom_from.Assumption) simp
    have ops:
      "\<Gamma> ; T ; insert ?EF {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (pp_biconditional_operator A)
          (pp_biconditional_operator ObjFalse)"
      using d_EF
        CEV_axiom_from_mono[OF EF_to_ops, of "insert ?EF {?P}"]
      by (rule CEV_axiom_from.MP) simp
    have final:
      "\<Gamma> ; T ; insert ?EF {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?OF"
      using typed_pp_biconditional_operator[OF A_type]
        typed_pp_biconditional_operator[OF typed_ObjFalse]
        typed_pp_negation_operator ops
        CEV_axiom_from_mono[OF op_false_eq, of "insert ?EF {?P}"]
      by (rule CEV_axiom_from_eq_trans) simp
    show ?thesis
      using EF_type final by (rule CEV_axiom_from_deduction)
  qed
  have finish:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Disj ?ET ?EF)
        (Imp (Imp ?ET ?OT)
          (Imp (Imp ?EF ?OF)
            (Disj ?OT ?OF)))"
  proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
    have ET_type: "\<Gamma> \<turnstile> ?ET : Prop"
      using A_type typed_ObjTrue by (rule has_type.Eq)
    have EF_type: "\<Gamma> \<turnstile> ?EF : Prop"
      using A_type typed_ObjFalse by (rule has_type.Eq)
    have OT_type: "\<Gamma> \<turnstile> ?OT : Prop"
      using typed_pp_biconditional_operator[OF A_type]
        typed_pp_identity_operator
      by (rule has_type.Eq)
    have OF_type: "\<Gamma> \<turnstile> ?OF : Prop"
      using typed_pp_biconditional_operator[OF A_type]
        typed_pp_negation_operator
      by (rule has_type.Eq)
    show "prop_tautology \<Gamma>
      (Imp (Disj ?ET ?EF)
        (Imp (Imp ?ET ?OT)
          (Imp (Imp ?EF ?OF)
            (Disj ?OT ?OF))))"
      unfolding prop_tautology_def
      using A_type typed_ObjTrue typed_ObjFalse
        typed_pp_biconditional_operator[OF A_type]
        typed_pp_identity_operator typed_pp_negation_operator
        ET_type EF_type OT_type OF_type
      by (auto simp: prop_eval.simps)
  qed
  have d_finish:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Disj ?ET ?EF)
        (Imp (Imp ?ET ?OT)
          (Imp (Imp ?EF ?OF)
            (Disj ?OT ?OF)))"
    using finish
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have s1:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?ET ?OT)
        (Imp (Imp ?EF ?OF)
          (Disj ?OT ?OF))"
    using d_extreme d_finish by (rule CEV_axiom_from.MP)
  have s2:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?EF ?OF) (Disj ?OT ?OF)"
    using ET_to_OT s1 by (rule CEV_axiom_from.MP)
  have d_class:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Disj ?OT ?OF"
    using EF_to_OF s2 by (rule CEV_axiom_from.MP)
  show ?thesis
    using P_type d_class by (rule CEV_axiom_from_singleton_imp)
qed

end
