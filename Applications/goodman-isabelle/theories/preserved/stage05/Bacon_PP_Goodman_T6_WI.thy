theory Bacon_PP_Goodman_T6_WI
  imports
    
    "Goodman_Legacy_05.Bacon_PP_Goodman_T6_TU"
    "Goodman_Legacy_03.Bacon_PP_Goodman_WI_Collapse"
begin

section \<open>Goodman T6 from WI\<close>

text \<open>
  WI already entails truth-uniformity, without Exhaustion or the stronger
  T1 stock.  If a reversible pure operator is extensionally
  \<open>\<lambda>p. p \<longleftrightarrow> A\<close>, excluded middle on \<open>A\<close> makes it
  truth-preserving when \<open>A\<close> and truth-flipping when \<open>\<not>A\<close>.
\<close>

definition pp_truth_uniform :: "oterm \<Rightarrow> oterm" where
  "pp_truth_uniform Z =
    Disj (pp_truth_preserving Z) (pp_truth_flipping Z)"

definition pp_truth_uniform_predicate :: oterm where
  "pp_truth_uniform_predicate =
    Lam pp_unary_ty (pp_truth_uniform (Var 0))"

definition pp_T6_WI_axioms :: "oterm set" where
  "pp_T6_WI_axioms =
    insert pp_WI
      (insert pp_L2
        (insert pp_exists_fun_prime pp_T6_core_PP_axioms))"

lemma typed_pp_truth_uniform:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_truth_uniform Z : Prop"
  unfolding pp_truth_uniform_def
  using typed_pp_truth_preserving[OF Z_type]
    typed_pp_truth_flipping[OF Z_type]
  by (rule has_type.Disj)

lemma typed_pp_truth_uniform_predicate:
  "\<Gamma> \<turnstile> pp_truth_uniform_predicate :
    pp_unary_ty \<rightarrow>\<^sub>o Prop"
  unfolding pp_truth_uniform_predicate_def
  using typed_pp_truth_uniform[
      OF typed_var0[
        where \<sigma> = pp_unary_ty and \<Gamma> = "\<Gamma>"]]
  by (rule has_type.Lam)

lemma subst_pp_truth_uniform[simp]:
  "subst s (pp_truth_uniform Z) =
    pp_truth_uniform (subst s Z)"
  by (simp add: pp_truth_uniform_def)

lemma rename_pp_truth_uniform[simp]:
  "rename r (pp_truth_uniform Z) =
    pp_truth_uniform (rename r Z)"
  by (simp add: pp_truth_uniform_def)

lemma shift_pp_truth_uniform[simp]:
  "shift (pp_truth_uniform Z) =
    pp_truth_uniform (shift Z)"
  by (simp add: shift_def)

lemma pp_truth_uniform_predicate_beta:
  "compatible_step beta_contract
    (App pp_truth_uniform_predicate Z)
    (pp_truth_uniform Z)"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam pp_unary_ty (pp_truth_uniform (Var 0)))
        Z)
      (subst0 Z (pp_truth_uniform (Var 0)))"
    by (rule beta_contract.beta)
  show "beta_contract
    (App pp_truth_uniform_predicate Z)
    (pp_truth_uniform Z)"
    using step
    by (simp add: pp_truth_uniform_predicate_def subst0_def)
qed

lemma CEV_pp_truth_uniform_predicate_beta_eq:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop
      (App pp_truth_uniform_predicate Z)
      (pp_truth_uniform Z)"
proof -
  have app_type:
    "\<Gamma> \<turnstile> App pp_truth_uniform_predicate Z : Prop"
    using typed_pp_truth_uniform_predicate Z_type
    by (rule has_type.App)
  have uniform_type:
    "\<Gamma> \<turnstile> pp_truth_uniform Z : Prop"
    using Z_type by (rule typed_pp_truth_uniform)
  have beta:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App pp_truth_uniform_predicate Z
        \<longleftrightarrow>\<^sub>o pp_truth_uniform Z)"
    using app_type uniform_type pp_truth_uniform_predicate_beta
    by (rule CEV_beta_step)
  show ?thesis
    using app_type uniform_type beta
    by (rule CEV_zeroary_equivalence)
qed

lemma CEV_axiom_from_truth_uniform_transport:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and W_type: "\<Gamma> \<turnstile> W : pp_unary_ty"
    and d_eq:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty Z W"
    and d_uniform_W:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_truth_uniform W"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_truth_uniform Z"
proof -
  let ?P = pp_truth_uniform_predicate
  let ?UZ = "pp_truth_uniform Z"
  let ?UW = "pp_truth_uniform W"
  have P_type:
    "\<Gamma> \<turnstile> ?P : pp_unary_ty \<rightarrow>\<^sub>o Prop"
    by (rule typed_pp_truth_uniform_predicate)
  have PZ_type: "\<Gamma> \<turnstile> App ?P Z : Prop"
    using P_type Z_type by (rule has_type.App)
  have PW_type: "\<Gamma> \<turnstile> App ?P W : Prop"
    using P_type W_type by (rule has_type.App)
  have UZ_type: "\<Gamma> \<turnstile> ?UZ : Prop"
    using Z_type by (rule typed_pp_truth_uniform)
  have UW_type: "\<Gamma> \<turnstile> ?UW : Prop"
    using W_type by (rule typed_pp_truth_uniform)
  have d_PZ_PW:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?P Z) (App ?P W)"
    using P_type Z_type W_type d_eq
    by (rule CEV_axiom_from_eq_app_right)
  have d_beta_Z:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?P Z) ?UZ"
    using CEV_pp_truth_uniform_predicate_beta_eq[OF Z_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_beta_W:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?P W) ?UW"
    using CEV_pp_truth_uniform_predicate_beta_eq[OF W_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_UZ_PZ:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?UZ (App ?P Z)"
    using PZ_type UZ_type d_beta_Z
    by (rule CEV_axiom_from_eq_sym)
  have d_UZ_PW:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?UZ (App ?P W)"
    using UZ_type PZ_type PW_type d_UZ_PZ d_PZ_PW
    by (rule CEV_axiom_from_eq_trans)
  have d_UZ_UW:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?UZ ?UW"
    using UZ_type PW_type UW_type d_UZ_PW d_beta_W
    by (rule CEV_axiom_from_eq_trans)
  have d_UW_UZ:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?UW ?UZ"
    using UZ_type UW_type d_UZ_UW
    by (rule CEV_axiom_from_eq_sym)
  show ?thesis
    using UW_type UZ_type d_uniform_W d_UW_UZ
    by (rule CEV_axiom_from_eq_prop_elim)
qed

subsection \<open>Every biconditional operator is truth-uniform\<close>

lemma shift_pp_biconditional_operator_T6_WI[simp]:
  "shift (pp_biconditional_operator A) =
    pp_biconditional_operator (shift A)"
  by (simp add: shift_def pp_biconditional_operator_def
      pp_biconditional_builder_def)

lemma prop_tautology_T6_WI_preserving:
  assumes X_type: "\<Gamma> \<turnstile> X : Prop"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "prop_tautology \<Gamma>
    (Imp
      (X \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o A))
      (Imp A (X \<longleftrightarrow>\<^sub>o p)))"
proof -
  have formula_type:
    "\<Gamma> \<turnstile>
      Imp
        (X \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o A))
        (Imp A (X \<longleftrightarrow>\<^sub>o p)) : Prop"
    using X_type p_type A_type
    by (intro has_type.Imp has_type.Conj)
  have eval:
    "\<forall>v. prop_eval v
      (Imp
        (X \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o A))
        (Imp A (X \<longleftrightarrow>\<^sub>o p)))"
  proof
    fix v
    show "prop_eval v
      (Imp
        (X \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o A))
        (Imp A (X \<longleftrightarrow>\<^sub>o p)))"
      apply (simp only: prop_eval.simps)
      by blast
  qed
  show ?thesis
    unfolding prop_tautology_def
    using formula_type eval by blast
qed

lemma prop_tautology_T6_WI_flipping:
  assumes X_type: "\<Gamma> \<turnstile> X : Prop"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "prop_tautology \<Gamma>
    (Imp
      (X \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o A))
      (Imp (Neg A) (X \<longleftrightarrow>\<^sub>o Neg p)))"
proof -
  have formula_type:
    "\<Gamma> \<turnstile>
      Imp
        (X \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o A))
        (Imp (Neg A) (X \<longleftrightarrow>\<^sub>o Neg p)) : Prop"
    using X_type p_type A_type
    by (intro has_type.Imp has_type.Conj has_type.Neg)
  have eval:
    "\<forall>v. prop_eval v
      (Imp
        (X \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o A))
        (Imp (Neg A) (X \<longleftrightarrow>\<^sub>o Neg p)))"
  proof
    fix v
    show "prop_eval v
      (Imp
        (X \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o A))
        (Imp (Neg A) (X \<longleftrightarrow>\<^sub>o Neg p)))"
      apply (simp only: prop_eval.simps)
      by blast
  qed
  show ?thesis
    unfolding prop_tautology_def
    using formula_type eval by blast
qed

lemma prop_tautology_T6_WI_excluded_middle:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "prop_tautology \<Gamma> (Disj A (Neg A))"
proof -
  have formula_type: "\<Gamma> \<turnstile> Disj A (Neg A) : Prop"
    using A_type by (intro has_type.Disj has_type.Neg)
  have eval: "\<forall>v. prop_eval v (Disj A (Neg A))"
  proof
    fix v
    show "prop_eval v (Disj A (Neg A))"
      apply (simp only: prop_eval.simps)
      by blast
  qed
  show ?thesis
    unfolding prop_tautology_def
    using formula_type eval by blast
qed

lemma prop_tautology_T6_WI_combine:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and P_type: "\<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "prop_tautology \<Gamma>
    (Imp (Imp A P)
      (Imp (Imp (Neg A) Q)
        (Imp (Disj A (Neg A)) (Disj P Q))))"
proof -
  have formula_type:
    "\<Gamma> \<turnstile>
      Imp (Imp A P)
        (Imp (Imp (Neg A) Q)
          (Imp (Disj A (Neg A)) (Disj P Q))) : Prop"
    using A_type P_type Q_type
    by (intro has_type.Imp has_type.Disj has_type.Neg)
  have eval:
    "\<forall>v. prop_eval v
      (Imp (Imp A P)
        (Imp (Imp (Neg A) Q)
          (Imp (Disj A (Neg A)) (Disj P Q))))"
  proof
    fix v
    show "prop_eval v
      (Imp (Imp A P)
        (Imp (Imp (Neg A) Q)
          (Imp (Disj A (Neg A)) (Disj P Q))))"
      apply (simp only: prop_eval.simps)
      by blast
  qed
  show ?thesis
    unfolding prop_tautology_def
    using formula_type eval by blast
qed

lemma CEV_axiom_biconditional_operator_truth_uniform:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_truth_uniform (pp_biconditional_operator A)"
proof -
  let ?Z = "pp_biconditional_operator A"
  let ?TP = "pp_truth_preserving ?Z"
  let ?TF = "pp_truth_flipping ?Z"
  have Z_type: "\<Gamma> \<turnstile> ?Z : pp_unary_ty"
    using A_type by (rule typed_pp_biconditional_operator)
  have TP_type: "\<Gamma> \<turnstile> ?TP : Prop"
    using Z_type by (rule typed_pp_truth_preserving)
  have TF_type: "\<Gamma> \<turnstile> ?TF : Prop"
    using Z_type by (rule typed_pp_truth_flipping)
  have preserve:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A ?TP"
  proof -
    let ?p = "Var 0"
    let ?As = "shift A"
    let ?Zs = "shift ?Z"
    let ?Zp = "App ?Zs ?p"
    let ?middle = "?p \<longleftrightarrow>\<^sub>o ?As"
    have As_type: "Prop # \<Gamma> \<turnstile> ?As : Prop"
      using A_type by (rule typed_shift_ctx)
    have p_type: "Prop # \<Gamma> \<turnstile> ?p : Prop"
      by (rule typed_var0)
    have Zs_type: "Prop # \<Gamma> \<turnstile> ?Zs : pp_unary_ty"
      using Z_type by (rule typed_shift_ctx)
    have Zp_type: "Prop # \<Gamma> \<turnstile> ?Zp : Prop"
      using Zs_type p_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have middle_type: "Prop # \<Gamma> \<turnstile> ?middle : Prop"
      using p_type As_type by (intro has_type.Conj has_type.Imp)
    have beta:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (?Zp \<longleftrightarrow>\<^sub>o ?middle)"
      using CEV_pp_biconditional_operator_apply[
        OF As_type p_type]
      by (simp only: shift_pp_biconditional_operator_T6_WI)
    have taut:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (?Zp \<longleftrightarrow>\<^sub>o ?middle)
          (Imp ?As (?Zp \<longleftrightarrow>\<^sub>o ?p))"
    proof (rule CEV_prop_tautology)
      show "prop_tautology (Prop # \<Gamma>)
        (Imp
          (?Zp \<longleftrightarrow>\<^sub>o ?middle)
          (Imp ?As (?Zp \<longleftrightarrow>\<^sub>o ?p)))"
        using Zp_type p_type As_type
        by (rule prop_tautology_T6_WI_preserving)
    qed
    have body:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?As (?Zp \<longleftrightarrow>\<^sub>o ?p)"
      using CEV_axiom_proves.Base[OF beta]
        CEV_axiom_proves.Base[OF taut]
      by (rule CEV_axiom_proves.MP)
    have generalized:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp A
          (Forall Prop
            (App (shift ?Z) (Var 0)
              \<longleftrightarrow>\<^sub>o Var 0))"
    proof (rule CEV_axiom_proves.Gen)
      show "\<Gamma> \<turnstile> A : Prop" by (rule A_type)
      show "Prop # \<Gamma> \<turnstile>
        (App (shift ?Z) (Var 0)
          \<longleftrightarrow>\<^sub>o Var 0) : Prop"
        using Zp_type p_type
        by (intro has_type.Conj has_type.Imp)
      show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (shift A)
          (App (shift ?Z) (Var 0)
            \<longleftrightarrow>\<^sub>o Var 0)"
        by (rule body)
    qed
    show ?thesis
      using generalized unfolding pp_truth_preserving_def .
  qed
  have flip:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Neg A) ?TF"
  proof -
    let ?p = "Var 0"
    let ?As = "shift A"
    let ?Zs = "shift ?Z"
    let ?Zp = "App ?Zs ?p"
    let ?middle = "?p \<longleftrightarrow>\<^sub>o ?As"
    have As_type: "Prop # \<Gamma> \<turnstile> ?As : Prop"
      using A_type by (rule typed_shift_ctx)
    have p_type: "Prop # \<Gamma> \<turnstile> ?p : Prop"
      by (rule typed_var0)
    have Zs_type: "Prop # \<Gamma> \<turnstile> ?Zs : pp_unary_ty"
      using Z_type by (rule typed_shift_ctx)
    have Zp_type: "Prop # \<Gamma> \<turnstile> ?Zp : Prop"
      using Zs_type p_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have middle_type: "Prop # \<Gamma> \<turnstile> ?middle : Prop"
      using p_type As_type by (intro has_type.Conj has_type.Imp)
    have neg_p_type: "Prop # \<Gamma> \<turnstile> Neg ?p : Prop"
      using p_type by (rule has_type.Neg)
    have beta:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (?Zp \<longleftrightarrow>\<^sub>o ?middle)"
      using CEV_pp_biconditional_operator_apply[
        OF As_type p_type]
      by (simp only: shift_pp_biconditional_operator_T6_WI)
    have taut:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (?Zp \<longleftrightarrow>\<^sub>o ?middle)
          (Imp (Neg ?As)
            (?Zp \<longleftrightarrow>\<^sub>o Neg ?p))"
    proof (rule CEV_prop_tautology)
      show "prop_tautology (Prop # \<Gamma>)
        (Imp
          (?Zp \<longleftrightarrow>\<^sub>o ?middle)
          (Imp (Neg ?As)
            (?Zp \<longleftrightarrow>\<^sub>o Neg ?p)))"
        using Zp_type p_type As_type
        by (rule prop_tautology_T6_WI_flipping)
    qed
    have body:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Neg ?As) (?Zp \<longleftrightarrow>\<^sub>o Neg ?p)"
      using CEV_axiom_proves.Base[OF beta]
        CEV_axiom_proves.Base[OF taut]
      by (rule CEV_axiom_proves.MP)
    have generalized:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Neg A)
          (Forall Prop
            (App (shift ?Z) (Var 0)
              \<longleftrightarrow>\<^sub>o Neg (Var 0)))"
    proof (rule CEV_axiom_proves.Gen)
      show "\<Gamma> \<turnstile> Neg A : Prop"
        using A_type by (rule has_type.Neg)
      show "Prop # \<Gamma> \<turnstile>
        (App (shift ?Z) (Var 0)
          \<longleftrightarrow>\<^sub>o Neg (Var 0)) : Prop"
        using Zp_type neg_p_type
        by (intro has_type.Conj has_type.Imp)
      show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (shift (Neg A))
          (App (shift ?Z) (Var 0)
            \<longleftrightarrow>\<^sub>o Neg (Var 0))"
        using body by (simp add: shift_def)
    qed
    show ?thesis
      using generalized unfolding pp_truth_flipping_def .
  qed
  have excluded:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Disj A (Neg A)"
  proof (rule CEV_axiom_proves.Base, rule CEV_prop_tautology)
    show "prop_tautology \<Gamma> (Disj A (Neg A))"
      using A_type by (rule prop_tautology_T6_WI_excluded_middle)
  qed
  have combine:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp A ?TP)
        (Imp (Imp (Neg A) ?TF)
          (Imp (Disj A (Neg A)) (Disj ?TP ?TF)))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp (Imp A ?TP)
        (Imp (Imp (Neg A) ?TF)
          (Imp (Disj A (Neg A)) (Disj ?TP ?TF))))"
      using A_type TP_type TF_type
      by (rule prop_tautology_T6_WI_combine)
  qed
  have s1:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp (Neg A) ?TF)
        (Imp (Disj A (Neg A)) (Disj ?TP ?TF))"
    using preserve CEV_axiom_proves.Base[OF combine]
    by (rule CEV_axiom_proves.MP)
  have s2:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Disj A (Neg A)) (Disj ?TP ?TF)"
    using flip s1 by (rule CEV_axiom_proves.MP)
  have result:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Disj ?TP ?TF"
    using excluded s2 by (rule CEV_axiom_proves.MP)
  show ?thesis
    using result unfolding pp_truth_uniform_def .
qed

subsection \<open>WI entails TU over every axiom extension\<close>

theorem CEV_axiom_WI_implies_TU:
  assumes WI_in: "pp_WI \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_TU"
proof -
  let ?Z = "Var 0"
  let ?G = "pp_group_member ?Z"
  let ?M = "pp_biconditional_member ?Z"
  let ?U = "pp_truth_uniform ?Z"
  have Z_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Z : pp_unary_ty"
    by (rule typed_var0)
  have G_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?G : Prop"
    using Z_type by (rule typed_pp_group_member)
  have M_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?M : Prop"
    using Z_type by (rule typed_pp_biconditional_member)
  have U_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?U : Prop"
    using Z_type by (rule typed_pp_truth_uniform)
  have d_WI:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_WI"
    using WI_in typed_pp_WI
    by (rule CEV_axiom_proves.Axiom)
  have WI_body_type:
    "pp_unary_ty # pp_unary_ty # \<Gamma> \<turnstile>
      Imp
        (pp_group_member (Var 0))
        (pp_biconditional_member (Var 0)) : Prop"
    using typed_pp_group_member[
        OF typed_var0[
          where \<sigma> = pp_unary_ty
            and \<Gamma> = "pp_unary_ty # \<Gamma>"]]
      typed_pp_biconditional_member[
        OF typed_var0[
          where \<sigma> = pp_unary_ty
            and \<Gamma> = "pp_unary_ty # \<Gamma>"]]
    by (rule has_type.Imp)
  have d_WI_instance:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?G ?M"
  proof -
    have raw:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        subst0 ?Z
          (Imp
            (pp_group_member (Var 0))
            (pp_biconditional_member (Var 0)))"
      using WI_body_type Z_type d_WI
      unfolding pp_WI_def
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
  have member_to_uniform:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?M ?U"
  proof -
    let ?A = "Var 0"
    let ?Zs = "shift ?Z"
    let ?Op = "pp_biconditional_operator ?A"
    let ?E = "Eq pp_unary_ty ?Zs ?Op"
    let ?B = "Conj (pp_pure Prop ?A) ?E"
    have A_type:
      "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?A : Prop"
      by (rule typed_var0)
    have Zs_type:
      "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?Zs : pp_unary_ty"
      using Z_type by (rule typed_shift_ctx)
    have Op_type:
      "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?Op : pp_unary_ty"
      using A_type by (rule typed_pp_biconditional_operator)
    have E_type:
      "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?E : Prop"
      using Zs_type Op_type by (rule has_type.Eq)
    have B_type:
      "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?B : Prop"
      using typed_pp_pure[OF A_type] E_type
      by (rule has_type.Conj)
    have d_B:
      "Prop # pp_unary_ty # \<Gamma> ; T ; {?B}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?B"
      using B_type
      by (intro CEV_axiom_from.Assumption) simp
    have d_E:
      "Prop # pp_unary_ty # \<Gamma> ; T ; {?B}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
      using d_B by (rule CEV_axiom_from_conj_right)
    have op_uniform:
      "Prop # pp_unary_ty # \<Gamma> ; T
        \<turnstile>\<^sub>CEV\<^sup>+ pp_truth_uniform ?Op"
      using A_type
      by (rule CEV_axiom_biconditional_operator_truth_uniform)
    have d_op_uniform:
      "Prop # pp_unary_ty # \<Gamma> ; T ; {?B}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_truth_uniform ?Op"
      using op_uniform by (rule CEV_axiom_from.Theorem)
    have d_Zs_uniform:
      "Prop # pp_unary_ty # \<Gamma> ; T ; {?B}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_truth_uniform ?Zs"
      using Zs_type Op_type d_E d_op_uniform
      by (rule CEV_axiom_from_truth_uniform_transport)
    have bound:
      "Prop # pp_unary_ty # \<Gamma> ; T
        \<turnstile>\<^sub>CEV\<^sup>+
          Imp ?B (shift ?U)"
    proof -
      have d_shift_U:
        "Prop # pp_unary_ty # \<Gamma> ; T ; {?B}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s shift ?U"
        using d_Zs_uniform by simp
      show ?thesis
        using B_type d_shift_U
        by (rule CEV_axiom_from_singleton_imp)
    qed
    have eliminated:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Exists Prop ?B) ?U"
    proof (rule CEV_axiom_proves.Inst)
      show "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?B : Prop"
        by (rule B_type)
      show "pp_unary_ty # \<Gamma> \<turnstile> ?U : Prop"
        by (rule U_type)
      show "Prop # pp_unary_ty # \<Gamma> ; T
        \<turnstile>\<^sub>CEV\<^sup>+ Imp ?B (shift ?U)"
        by (rule bound)
    qed
    show ?thesis
      using eliminated unfolding pp_biconditional_member_def .
  qed
  have body:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?G ?U"
  proof -
    have d_G:
      "pp_unary_ty # \<Gamma> ; T ; {?G}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?G"
      using G_type
      by (intro CEV_axiom_from.Assumption) simp
    have d_M:
      "pp_unary_ty # \<Gamma> ; T ; {?G}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?M"
      using d_G CEV_axiom_from.Theorem[OF d_WI_instance]
      by (rule CEV_axiom_from.MP)
    have d_U:
      "pp_unary_ty # \<Gamma> ; T ; {?G}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?U"
      using d_M CEV_axiom_from.Theorem[OF member_to_uniform]
      by (rule CEV_axiom_from.MP)
    show ?thesis
      using G_type d_U by (rule CEV_axiom_from_singleton_imp)
  qed
  have guarded:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue (Imp ?G ?U)"
    using typed_ObjTrue body by (rule CEV_axiom_imp_of_right)
  have generalized_imp:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue (Forall pp_unary_ty (Imp ?G ?U))"
  proof (rule CEV_axiom_proves.Gen)
    show "\<Gamma> \<turnstile> ObjTrue : Prop"
      by (rule typed_ObjTrue)
    show "pp_unary_ty # \<Gamma> \<turnstile> Imp ?G ?U : Prop"
      using G_type U_type by (rule has_type.Imp)
    show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ObjTrue) (Imp ?G ?U)"
      using guarded by (simp add: ObjTrue_def shift_def)
  qed
  have d_true: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjTrue"
    by (rule CEV_axiom_proves_ObjTrue)
  have generalized:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall pp_unary_ty (Imp ?G ?U)"
    using d_true generalized_imp
    by (rule CEV_axiom_proves.MP)
  show ?thesis
    using generalized
    unfolding pp_TU_def pp_truth_uniform_def .
qed

subsection \<open>Axiom translation and the WI contradiction\<close>

lemma CEV_axiom_proves_translate:
  assumes derivation: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ A"
    and translate:
      "\<And>\<Delta> B.
        B \<in> U \<Longrightarrow>
        \<Delta> \<turnstile> B : Prop \<Longrightarrow>
        \<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  using derivation translate
proof (induction rule: CEV_axiom_proves.induct)
  case (Axiom B U \<Delta>)
  show ?case
    using Axiom.hyps by (rule Axiom.prems)
next
  case (Base \<Delta> B U)
  show ?case
    using Base.hyps by (rule CEV_axiom_proves.Base)
next
  case (VectorEquivalence \<Delta> F \<sigma>s G U)
  have IH:
    "\<sigma>s @ \<Delta> ; T
      \<turnstile>\<^sub>CEV\<^sup>+ zeta_body \<sigma>s F G"
    using VectorEquivalence.prems
    by (rule VectorEquivalence.IH)
  show ?case
    using VectorEquivalence.hyps(1,2) IH
    by (rule CEV_axiom_proves.VectorEquivalence)
next
  case (MP \<Delta> U B C)
  have d_B: "\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
    using MP.prems by (rule MP.IH(1))
  have d_imp: "\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp B C"
    using MP.prems by (rule MP.IH(2))
  show ?case
    using d_B d_imp by (rule CEV_axiom_proves.MP)
next
  case (Gen \<Delta> P \<sigma> Q U)
  have IH:
    "\<sigma> # \<Delta> ; T
      \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift P) Q"
    using Gen.prems by (rule Gen.IH)
  show ?case
    using Gen.hyps(1,2) IH
    by (rule CEV_axiom_proves.Gen)
next
  case (Inst \<sigma> \<Delta> P Q U)
  have IH:
    "\<sigma> # \<Delta> ; T
      \<turnstile>\<^sub>CEV\<^sup>+ Imp P (shift Q)"
    using Inst.prems by (rule Inst.IH)
  show ?case
    using Inst.hyps(1,2) IH
    by (rule CEV_axiom_proves.Inst)
qed

theorem CEV_Goodman_T6_WI:
  "[] ; pp_T6_WI_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof (rule CEV_axiom_proves_translate[
    OF CEV_Goodman_T6_TU])
  fix \<Delta> B
  assume B_in: "B \<in> pp_T6_TU_axioms"
    and B_type: "\<Delta> \<turnstile> B : Prop"
  show "\<Delta> ; pp_T6_WI_axioms \<turnstile>\<^sub>CEV\<^sup>+ B"
  proof (cases "B = pp_TU")
    case True
    have WI_in: "pp_WI \<in> pp_T6_WI_axioms"
      unfolding pp_T6_WI_axioms_def by blast
    have "\<Delta> ; pp_T6_WI_axioms
      \<turnstile>\<^sub>CEV\<^sup>+ pp_TU"
      using WI_in by (rule CEV_axiom_WI_implies_TU)
    then show ?thesis
      using True by simp
  next
    case False
    have "B \<in> pp_T6_WI_axioms"
      using B_in False
      unfolding pp_T6_TU_axioms_def pp_T6_WI_axioms_def
      by blast
    then show ?thesis
      using B_type by (rule CEV_axiom_proves.Axiom)
  qed
qed

corollary CEV_Goodman_T6_WI_mono:
  assumes "pp_T6_WI_axioms \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  using CEV_Goodman_T6_WI assms
  by (rule CEV_axiom_proves_mono)

end
