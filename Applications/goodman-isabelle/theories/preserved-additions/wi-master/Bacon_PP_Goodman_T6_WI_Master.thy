theory Bacon_PP_Goodman_T6_WI_Master
  imports 
    "Goodman_Legacy_05.Bacon_PP_Goodman_T6_WI"
begin

section \<open>Goodman's advertised T6-WI master family\<close>

text \<open>
  Goodman writes \<open>d = Dr\<close> and, for pure propositions \<open>A\<close>,
  \<open>a\<^sub>A = D(d \<longleftrightarrow> A)\<close>.  The advertised master equation is

    \<open>a\<^sub>A \<longleftrightarrow> \<forall>C (Pure(C) \<longrightarrow>
      (a\<^sub>C \<longleftrightarrow> \<not>A))\<close>.

  We first isolate the logical content of that family for an arbitrary
  proposition-indexed operator \<open>a\<close>.  This keeps the propositional
  inconsistency separate from the harder derivation of the equation from
  WI, L2, and the liar matrix.
\<close>

definition pp_T6_WI_master_at ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_T6_WI_master_at a A =
    (App a A \<longleftrightarrow>\<^sub>o
      Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
            Neg (shift A))))"

definition pp_T6_WI_master_family :: "oterm \<Rightarrow> oterm" where
  "pp_T6_WI_master_family a =
    Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (pp_T6_WI_master_at (shift a) (Var 0)))"

definition pp_T6_WI_a :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_T6_WI_a r A =
    App pp_T6_liar
      (App (pp_biconditional_operator A)
        (App pp_T6_liar r))"

definition pp_T6_WI_diagonal_point ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_T6_WI_diagonal_point r A =
    App (pp_biconditional_operator A)
      (App pp_T6_liar r)"

definition pp_T6_WI_comparison_operator ::
    "oterm \<Rightarrow> oterm" where
  "pp_T6_WI_comparison_operator A =
    pp_compose
      (pp_biconditional_operator A)
      pp_T6_liar"

definition pp_T6_WI_collision_operator ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_T6_WI_collision_operator A E =
    pp_compose
      (pp_T6_WI_comparison_operator A)
      (pp_biconditional_operator E)"

definition pp_T6_WI_a_operator :: "oterm \<Rightarrow> oterm" where
  "pp_T6_WI_a_operator r =
    Lam Prop (pp_T6_WI_a (shift r) (Var 0))"

definition pp_T6_WI_advertised_master :: "oterm \<Rightarrow> oterm" where
  "pp_T6_WI_advertised_master r =
    pp_T6_WI_master_family (pp_T6_WI_a_operator r)"

definition pp_T6_WI_advertised_master_claim :: oterm where
  "pp_T6_WI_advertised_master_claim =
    Forall Prop
      (Imp
        (pp_fun_prime (Var 0))
        (pp_T6_WI_advertised_master (Var 0)))"

lemma typed_pp_T6_WI_master_at:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> pp_T6_WI_master_at a A : Prop"
proof -
  have aA_type: "\<Gamma> \<turnstile> App a A : Prop"
    using a_type A_type by (rule has_type.App)
  have a_shift_type:
    "Prop # \<Gamma> \<turnstile> shift a : Prop \<rightarrow>\<^sub>o Prop"
    using a_type by (rule typed_shift_ctx)
  have A_shift_type: "Prop # \<Gamma> \<turnstile> shift A : Prop"
    using A_type by (rule typed_shift_ctx)
  have C_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have pure_C_type:
    "Prop # \<Gamma> \<turnstile> pp_pure Prop (Var 0) : Prop"
    using C_type by (rule typed_pp_pure)
  have aC_type: "Prop # \<Gamma> \<turnstile> App (shift a) (Var 0) : Prop"
    using a_shift_type C_type by (rule has_type.App)
  have matrix_type:
    "Prop # \<Gamma> \<turnstile>
      Imp
        (pp_pure Prop (Var 0))
        (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
          Neg (shift A)) : Prop"
    using pure_C_type aC_type A_shift_type
    by (intro has_type.Imp has_type.Conj has_type.Neg)
  have rhs_type:
    "\<Gamma> \<turnstile>
      Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
            Neg (shift A))) : Prop"
    using matrix_type by (rule has_type.Forall)
  show ?thesis
    unfolding pp_T6_WI_master_at_def
    using aA_type rhs_type
    by (intro has_type.Conj has_type.Imp)
qed

lemma typed_pp_T6_WI_master_family:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile> pp_T6_WI_master_family a : Prop"
proof -
  have a_shift_type:
    "Prop # \<Gamma> \<turnstile> shift a : Prop \<rightarrow>\<^sub>o Prop"
    using a_type by (rule typed_shift_ctx)
  have A_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  show ?thesis
    unfolding pp_T6_WI_master_family_def
    using typed_pp_pure[OF A_type]
      typed_pp_T6_WI_master_at[OF a_shift_type A_type]
    by (intro has_type.Forall has_type.Imp)
qed

lemma typed_pp_T6_WI_a:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> pp_T6_WI_a r A : Prop"
proof -
  have D_type: "\<Gamma> \<turnstile> pp_T6_liar : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have d_type: "\<Gamma> \<turnstile> App pp_T6_liar r : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have B_type:
    "\<Gamma> \<turnstile> pp_biconditional_operator A : pp_unary_ty"
    using A_type by (rule typed_pp_biconditional_operator)
  have Bd_type:
    "\<Gamma> \<turnstile>
      App (pp_biconditional_operator A) (App pp_T6_liar r) : Prop"
    using B_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_T6_WI_a_def
    using D_type Bd_type unfolding pp_unary_ty_def
    by (rule has_type.App)
qed

lemma typed_pp_T6_WI_diagonal_point:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> pp_T6_WI_diagonal_point r A : Prop"
  unfolding pp_T6_WI_diagonal_point_def
  using typed_pp_biconditional_operator[OF A_type]
    has_type.App[
      OF typed_pp_T6_liar[unfolded pp_unary_ty_def] r_type]
  unfolding pp_unary_ty_def
  by (rule has_type.App)

lemma typed_pp_T6_WI_comparison_operator:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> pp_T6_WI_comparison_operator A : pp_unary_ty"
  unfolding pp_T6_WI_comparison_operator_def
  using typed_pp_biconditional_operator[OF A_type] typed_pp_T6_liar
  by (rule typed_pp_compose)

lemma typed_pp_T6_WI_collision_operator:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and E_type: "\<Gamma> \<turnstile> E : Prop"
  shows "\<Gamma> \<turnstile>
    pp_T6_WI_collision_operator A E : pp_unary_ty"
  unfolding pp_T6_WI_collision_operator_def
  using typed_pp_T6_WI_comparison_operator[OF A_type]
    typed_pp_biconditional_operator[OF E_type]
  by (rule typed_pp_compose)

lemma pp_T6_WI_a_as_liar_at_point:
  "pp_T6_WI_a r A =
    App pp_T6_liar (pp_T6_WI_diagonal_point r A)"
  by (simp add: pp_T6_WI_a_def pp_T6_WI_diagonal_point_def)

lemma typed_pp_T6_WI_a_operator:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> pp_T6_WI_a_operator r : Prop \<rightarrow>\<^sub>o Prop"
proof -
  have r_shift_type: "Prop # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have A_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  show ?thesis
    unfolding pp_T6_WI_a_operator_def
    using typed_pp_T6_WI_a[OF r_shift_type A_type]
    by (rule has_type.Lam)
qed

lemma pp_T6_WI_a_operator_beta:
  "compatible_step beta_contract
    (App (pp_T6_WI_a_operator r) A)
    (pp_T6_WI_a r A)"
proof -
  have step:
    "beta_contract
      (App
        (Lam Prop (pp_T6_WI_a (shift r) (Var 0)))
        A)
      (subst0 A (pp_T6_WI_a (shift r) (Var 0)))"
    by (rule beta_contract.beta)
  show ?thesis
    using step
    unfolding pp_T6_WI_a_operator_def
    by (intro compatible_step.root)
      (simp add: pp_T6_WI_a_def pp_T6_liar_def
        pp_biconditional_operator_def pp_biconditional_builder_def
        pp_fun_prime_def pp_pure_def pp_Pure_def
        subst0_def subst0_shift[of A r, unfolded subst0_def]
        shift_by_def shift_ren_def eval_nat_numeral)
qed

lemma CEV_pp_T6_WI_a_operator_apply_eq:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop
      (App (pp_T6_WI_a_operator r) A)
      (pp_T6_WI_a r A)"
proof -
  have left_type:
    "\<Gamma> \<turnstile> App (pp_T6_WI_a_operator r) A : Prop"
    using typed_pp_T6_WI_a_operator[OF r_type] A_type
    by (rule has_type.App)
  have right_type: "\<Gamma> \<turnstile> pp_T6_WI_a r A : Prop"
    using r_type A_type by (rule typed_pp_T6_WI_a)
  have iff:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App (pp_T6_WI_a_operator r) A
        \<longleftrightarrow>\<^sub>o pp_T6_WI_a r A)"
    using left_type right_type pp_T6_WI_a_operator_beta
    by (rule CEV_beta_step)
  show ?thesis
    using left_type right_type iff
    by (rule CEV_zeroary_equivalence)
qed

lemma shift_pp_T6_WI_a_operator[simp]:
  "shift (pp_T6_WI_a_operator r) =
    pp_T6_WI_a_operator (shift r)"
  by (simp add: pp_T6_WI_a_operator_def shift_def
      pp_T6_WI_a_def pp_T6_liar_def
      pp_biconditional_operator_def pp_biconditional_builder_def
      pp_fun_prime_def pp_pure_def pp_Pure_def
      shift_by_def shift_ren_def eval_nat_numeral
      rename_lift_Suc_after_shift)

lemma typed_pp_T6_WI_advertised_master:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> pp_T6_WI_advertised_master r : Prop"
  unfolding pp_T6_WI_advertised_master_def
  using typed_pp_T6_WI_a_operator[OF r_type]
  by (rule typed_pp_T6_WI_master_family)

lemma typed_pp_T6_WI_advertised_master_claim:
  "\<Gamma> \<turnstile> pp_T6_WI_advertised_master_claim : Prop"
  unfolding pp_T6_WI_advertised_master_claim_def
  using typed_pp_fun_prime[OF typed_var0]
    typed_pp_T6_WI_advertised_master[OF typed_var0]
  by (intro has_type.Forall has_type.Imp)

lemma subst_pp_T6_WI_master_at[simp]:
  "subst s (pp_T6_WI_master_at a A) =
    pp_T6_WI_master_at (subst s a) (subst s A)"
  by (simp add: pp_T6_WI_master_at_def subst_lift_shift)

lemma rename_pp_T6_WI_master_at[simp]:
  "rename r (pp_T6_WI_master_at a A) =
    pp_T6_WI_master_at (rename r a) (rename r A)"
  by (simp add: pp_T6_WI_master_at_def shift_rename_lift)

lemma shift_pp_T6_WI_master_at[simp]:
  "shift (pp_T6_WI_master_at a A) =
    pp_T6_WI_master_at (shift a) (shift A)"
  by (simp add: shift_def)

lemma rename_pp_T6_WI_master_family[simp]:
  "rename r (pp_T6_WI_master_family a) =
    pp_T6_WI_master_family (rename r a)"
  by (simp add: pp_T6_WI_master_family_def shift_rename_lift)

lemma shift_pp_T6_WI_master_family[simp]:
  "shift (pp_T6_WI_master_family a) =
    pp_T6_WI_master_family (shift a)"
  by (simp add: shift_def)

lemma shift_pp_T6_WI_diagonal_point[simp]:
  "shift (pp_T6_WI_diagonal_point r A) =
    pp_T6_WI_diagonal_point (shift r) (shift A)"
  by (simp add: pp_T6_WI_diagonal_point_def shift_pp_T6_liar)

lemma shift_by_2_pp_T6_WI_diagonal_point[simp]:
  "shift_by 2 (pp_T6_WI_diagonal_point r A) =
    pp_T6_WI_diagonal_point (shift_by 2 r) (shift_by 2 A)"
proof -
  have lhs:
    "shift_by 2 (pp_T6_WI_diagonal_point r A) =
      shift (shift (pp_T6_WI_diagonal_point r A))"
    using shift_shift_eq_shift_by_2[
      of "pp_T6_WI_diagonal_point r A"]
    by simp
  have r_rhs: "shift_by 2 r = shift (shift r)"
    using shift_shift_eq_shift_by_2[of r] by simp
  have A_rhs: "shift_by 2 A = shift (shift A)"
    using shift_shift_eq_shift_by_2[of A] by simp
  show ?thesis
    using lhs r_rhs A_rhs by simp
qed

lemma shift_pp_T6_WI_a[simp]:
  "shift (pp_T6_WI_a r A) =
    pp_T6_WI_a (shift r) (shift A)"
  by (simp add: pp_T6_WI_a_as_liar_at_point shift_pp_T6_liar)

lemma rename_lift_pp_T6_liar_T6_WI[simp]:
  "rename (lift_ren Suc) pp_T6_liar = pp_T6_liar"
  by (simp add: pp_T6_liar_def pp_fun_prime_def
      pp_pure_def pp_Pure_def shift_by_def shift_ren_def
      eval_nat_numeral)

lemma shift_pp_T6_WI_rhs_formula[simp]:
  "shift
      (Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (pp_T6_WI_a (shift r) (Var 0)
            \<longleftrightarrow>\<^sub>o Neg (shift A)))) =
    Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (pp_T6_WI_a (shift (shift r)) (Var 0)
          \<longleftrightarrow>\<^sub>o Neg (shift (shift A))))"
  by (simp add: shift_def pp_T6_WI_a_def
      pp_biconditional_operator_def pp_biconditional_builder_def
      rename_lift_Suc_after_shift)

lemma shift_pp_T6_WI_operator_rhs_formula[simp]:
  "shift
      (Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (App (shift a) (Var 0)
            \<longleftrightarrow>\<^sub>o Neg (shift A)))) =
    Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (App (shift (shift a)) (Var 0)
          \<longleftrightarrow>\<^sub>o Neg (shift (shift A))))"
  by (simp add: shift_def pp_pure_def pp_Pure_def
      rename_lift_Suc_after_shift)

lemma shift_pp_T6_WI_comparison_operator[simp]:
  "shift (pp_T6_WI_comparison_operator A) =
    pp_T6_WI_comparison_operator (shift A)"
  by (simp add: pp_T6_WI_comparison_operator_def shift_pp_T6_liar)

lemma shift_pp_T6_WI_collision_operator[simp]:
  "shift (pp_T6_WI_collision_operator A E) =
    pp_T6_WI_collision_operator (shift A) (shift E)"
  by (simp add: pp_T6_WI_collision_operator_def)

lemma CEV_axiom_master_family_instance:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and family:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_T6_WI_master_family a"
    and pure_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_T6_WI_master_at a A"
proof -
  have family_type:
    "\<Gamma> \<turnstile> pp_T6_WI_master_family a : Prop"
    using a_type by (rule typed_pp_T6_WI_master_family)
  have raw:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 A
        (Imp
          (pp_pure Prop (Var 0))
          (pp_T6_WI_master_at (shift a) (Var 0)))"
    using family_type A_type family
    unfolding pp_T6_WI_master_family_def
    by (rule CEV_axiom_from_UI_typed)
  have inst:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_pure Prop A) (pp_T6_WI_master_at a A)"
    using raw
    by (simp add: subst0_def
        subst0_shift[of A a, unfolded subst0_def])
  show ?thesis
    using pure_A inst by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_master_rhs_instance:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and rhs:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Forall Prop
          (Imp
            (pp_pure Prop (Var 0))
            (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
              Neg (shift A)))"
    and pure_C:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop C"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    (App a C \<longleftrightarrow>\<^sub>o Neg A)"
proof -
  have rhs_type:
    "\<Gamma> \<turnstile>
      Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
            Neg (shift A))) : Prop"
    using typed_pp_T6_WI_master_at[OF a_type A_type]
    unfolding pp_T6_WI_master_at_def
    by (auto elim: has_type.cases)
  have raw:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 C
        (Imp
          (pp_pure Prop (Var 0))
          (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
            Neg (shift A)))"
    using rhs_type C_type rhs by (rule CEV_axiom_from_UI_typed)
  have inst:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (pp_pure Prop C)
        (App a C \<longleftrightarrow>\<^sub>o Neg A)"
    using raw
    by (simp add: subst0_def
        subst0_shift[of C a, unfolded subst0_def]
        subst0_shift[of C A, unfolded subst0_def])
  show ?thesis
    using pure_C inst by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_T6_WI_rhs_instance:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and rhs:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Forall Prop
          (Imp
            (pp_pure Prop (Var 0))
            (pp_T6_WI_a (shift r) (Var 0)
              \<longleftrightarrow>\<^sub>o Neg (shift A)))"
    and pure_C:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop C"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    (pp_T6_WI_a r C \<longleftrightarrow>\<^sub>o Neg A)"
proof -
  let ?B =
    "Imp
      (pp_pure Prop (Var 0))
      (pp_T6_WI_a (shift r) (Var 0)
        \<longleftrightarrow>\<^sub>o Neg (shift A))"
  have rs_type: "Prop # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have As_type: "Prop # \<Gamma> \<turnstile> shift A : Prop"
    using A_type by (rule typed_shift_ctx)
  have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have B_type: "Prop # \<Gamma> \<turnstile> ?B : Prop"
    using typed_pp_pure[OF v_type]
      typed_pp_T6_WI_a[OF rs_type v_type] As_type
    by (intro has_type.Imp has_type.Conj has_type.Neg)
  have raw:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s subst0 C ?B"
    using has_type.Forall[OF B_type] C_type rhs
    by (rule CEV_axiom_from_UI_typed)
  have inst:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (pp_pure Prop C)
        (pp_T6_WI_a r C \<longleftrightarrow>\<^sub>o Neg A)"
    using raw
    by (simp add: pp_T6_WI_a_def pp_T6_liar_def
      pp_biconditional_operator_def pp_biconditional_builder_def
      pp_fun_prime_def pp_pure_def pp_Pure_def
      subst0_def subst0_shift[of C r, unfolded subst0_def]
      subst0_shift[of C A, unfolded subst0_def]
      shift_by_def shift_ren_def eval_nat_numeral)
  show ?thesis
    using pure_C inst by (rule CEV_axiom_from.MP)
qed

subsection \<open>Biconditional reindexing algebra\<close>

lemma CEV_T6_WI_biconditional_cong:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and D_type: "\<Gamma> \<turnstile> D : Prop"
    and AB: "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
    and CD: "\<Gamma> \<turnstile>\<^sub>CEV (C \<longleftrightarrow>\<^sub>o D)"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    ((A \<longleftrightarrow>\<^sub>o C) \<longleftrightarrow>\<^sub>o
      (B \<longleftrightarrow>\<^sub>o D))"
proof -
  let ?AB = "A \<longleftrightarrow>\<^sub>o B"
  let ?CD = "C \<longleftrightarrow>\<^sub>o D"
  let ?R =
    "(A \<longleftrightarrow>\<^sub>o C) \<longleftrightarrow>\<^sub>o
      (B \<longleftrightarrow>\<^sub>o D)"
  have taut:
    "\<Gamma> \<turnstile>\<^sub>CEV Imp ?AB (Imp ?CD ?R)"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma> (Imp ?AB (Imp ?CD ?R))"
    proof (unfold prop_tautology_def, intro conjI)
      show "\<Gamma> \<turnstile> Imp ?AB (Imp ?CD ?R) : Prop"
        using A_type B_type C_type D_type
        by (intro has_type.Imp has_type.Conj)
    next
      show "\<forall>v. prop_eval v (Imp ?AB (Imp ?CD ?R))"
        apply (simp only: prop_eval.simps)
        by blast
    qed
  qed
  have step: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?CD ?R"
    using AB taut by (rule CEV_proves.MP)
  show ?thesis
    using CD step by (rule CEV_proves.MP)
qed

lemma CEV_T6_WI_biconditional_reassociate:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    (((p \<longleftrightarrow>\<^sub>o C) \<longleftrightarrow>\<^sub>o A)
      \<longleftrightarrow>\<^sub>o
      (p \<longleftrightarrow>\<^sub>o (A \<longleftrightarrow>\<^sub>o C)))"
proof (rule CEV_prop_tautology)
  show "prop_tautology \<Gamma>
    (((p \<longleftrightarrow>\<^sub>o C) \<longleftrightarrow>\<^sub>o A)
      \<longleftrightarrow>\<^sub>o
      (p \<longleftrightarrow>\<^sub>o (A \<longleftrightarrow>\<^sub>o C)))"
  proof (unfold prop_tautology_def, intro conjI)
    show "\<Gamma> \<turnstile>
      (((p \<longleftrightarrow>\<^sub>o C) \<longleftrightarrow>\<^sub>o A)
        \<longleftrightarrow>\<^sub>o
        (p \<longleftrightarrow>\<^sub>o
          (A \<longleftrightarrow>\<^sub>o C))) : Prop"
      using p_type A_type C_type
      by (intro has_type.Conj has_type.Imp)
  next
    show "\<forall>v. prop_eval v
      (((p \<longleftrightarrow>\<^sub>o C) \<longleftrightarrow>\<^sub>o A)
        \<longleftrightarrow>\<^sub>o
        (p \<longleftrightarrow>\<^sub>o
          (A \<longleftrightarrow>\<^sub>o C)))"
      apply (simp only: prop_eval.simps)
      by blast
  qed
qed

lemma CEV_T6_WI_negated_biconditional:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    (Neg (p \<longleftrightarrow>\<^sub>o A)
      \<longleftrightarrow>\<^sub>o
      (p \<longleftrightarrow>\<^sub>o Neg A))"
proof (rule CEV_prop_tautology)
  show "prop_tautology \<Gamma>
    (Neg (p \<longleftrightarrow>\<^sub>o A)
      \<longleftrightarrow>\<^sub>o
      (p \<longleftrightarrow>\<^sub>o Neg A))"
  proof (unfold prop_tautology_def, intro conjI)
    show "\<Gamma> \<turnstile>
      (Neg (p \<longleftrightarrow>\<^sub>o A)
        \<longleftrightarrow>\<^sub>o
        (p \<longleftrightarrow>\<^sub>o Neg A)) : Prop"
      using p_type A_type
      by (intro has_type.Conj has_type.Imp has_type.Neg)
  next
    show "\<forall>v. prop_eval v
      (Neg (p \<longleftrightarrow>\<^sub>o A)
        \<longleftrightarrow>\<^sub>o
        (p \<longleftrightarrow>\<^sub>o Neg A))"
      apply (simp only: prop_eval.simps)
      by blast
  qed
qed

theorem CEV_T6_WI_biconditional_compose:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (pp_compose
        (pp_biconditional_operator A)
        (pp_biconditional_operator C))
      (pp_biconditional_operator
        (A \<longleftrightarrow>\<^sub>o C))"
proof -
  let ?BA = "pp_biconditional_operator A"
  let ?BC = "pp_biconditional_operator C"
  let ?AC = "A \<longleftrightarrow>\<^sub>o C"
  let ?BAC = "pp_biconditional_operator ?AC"
  have BA_type: "\<Gamma> \<turnstile> ?BA : pp_unary_ty"
    using A_type by (rule typed_pp_biconditional_operator)
  have BC_type: "\<Gamma> \<turnstile> ?BC : pp_unary_ty"
    using C_type by (rule typed_pp_biconditional_operator)
  have AC_type: "\<Gamma> \<turnstile> ?AC : Prop"
    using A_type C_type by (intro has_type.Conj has_type.Imp)
  have BAC_type: "\<Gamma> \<turnstile> ?BAC : pp_unary_ty"
    using AC_type by (rule typed_pp_biconditional_operator)
  have op_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Eq (Prop \<rightarrow>\<^sub>o Prop)
        (pp_compose ?BA ?BC) ?BAC"
  proof (rule CEV_unary_equivalence)
    show "\<Gamma> \<turnstile> pp_compose ?BA ?BC : Prop \<rightarrow>\<^sub>o Prop"
      using typed_pp_compose[OF BA_type BC_type]
      by (simp add: pp_unary_ty_def)
  next
    show "\<Gamma> \<turnstile> ?BAC : Prop \<rightarrow>\<^sub>o Prop"
      using BAC_type by (simp add: pp_unary_ty_def)
  next
    let ?v = "Var 0"
    let ?BAs = "shift ?BA"
    let ?BCs = "shift ?BC"
    let ?BACs = "shift ?BAC"
    let ?As = "shift A"
    let ?Cs = "shift C"
    let ?L = "App (pp_compose ?BAs ?BCs) ?v"
    let ?M0 = "App ?BAs (App ?BCs ?v)"
    let ?M1 = "App ?BCs ?v \<longleftrightarrow>\<^sub>o ?As"
    let ?M2 = "(?v \<longleftrightarrow>\<^sub>o ?Cs)
      \<longleftrightarrow>\<^sub>o ?As"
    let ?M3 = "?v \<longleftrightarrow>\<^sub>o
      (?As \<longleftrightarrow>\<^sub>o ?Cs)"
    let ?R = "App ?BACs ?v"
    have As_type: "Prop # \<Gamma> \<turnstile> ?As : Prop"
      using A_type by (rule typed_shift_ctx)
    have Cs_type: "Prop # \<Gamma> \<turnstile> ?Cs : Prop"
      using C_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> ?v : Prop"
      by (rule typed_var0)
    have BAs_type: "Prop # \<Gamma> \<turnstile> ?BAs : pp_unary_ty"
      using BA_type by (rule typed_shift_ctx)
    have BCs_type: "Prop # \<Gamma> \<turnstile> ?BCs : pp_unary_ty"
      using BC_type by (rule typed_shift_ctx)
    have BACs_type: "Prop # \<Gamma> \<turnstile> ?BACs : pp_unary_ty"
      using BAC_type by (rule typed_shift_ctx)
    have BCv_type: "Prop # \<Gamma> \<turnstile> App ?BCs ?v : Prop"
      using BCs_type v_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have L_type: "Prop # \<Gamma> \<turnstile> ?L : Prop"
      using typed_pp_compose[OF BAs_type BCs_type] v_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    have M0_type: "Prop # \<Gamma> \<turnstile> ?M0 : Prop"
      using BAs_type BCv_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have M1_type: "Prop # \<Gamma> \<turnstile> ?M1 : Prop"
      using BCv_type As_type by (intro has_type.Conj has_type.Imp)
    have M2_type: "Prop # \<Gamma> \<turnstile> ?M2 : Prop"
      using v_type Cs_type As_type
      by (intro has_type.Conj has_type.Imp)
    have M3_type: "Prop # \<Gamma> \<turnstile> ?M3 : Prop"
      using v_type As_type Cs_type
      by (intro has_type.Conj has_type.Imp)
    have R_type: "Prop # \<Gamma> \<turnstile> ?R : Prop"
      using BACs_type v_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have L_M0:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?L \<longleftrightarrow>\<^sub>o ?M0)"
      using BAs_type BCs_type v_type by (rule CEV_pp_compose_apply)
    have M0_M1:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?M0 \<longleftrightarrow>\<^sub>o ?M1)"
      using CEV_pp_biconditional_operator_apply[OF As_type BCv_type]
      by (simp add: shift_pp_biconditional_operator_T6_WI)
    have BC_beta:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV
        (App ?BCs ?v \<longleftrightarrow>\<^sub>o
          (?v \<longleftrightarrow>\<^sub>o ?Cs))"
      using CEV_pp_biconditional_operator_apply[OF Cs_type v_type]
      by (simp add: shift_pp_biconditional_operator_T6_WI)
    have refl_A:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?As \<longleftrightarrow>\<^sub>o ?As)"
    proof (rule CEV_prop_tautology)
      show "prop_tautology (Prop # \<Gamma>)
        (?As \<longleftrightarrow>\<^sub>o ?As)"
        unfolding prop_tautology_def
        using As_type by (auto simp: prop_eval.simps)
    qed
    have M1_M2:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?M1 \<longleftrightarrow>\<^sub>o ?M2)"
      using BCv_type
        has_type.Conj[OF has_type.Imp[OF v_type Cs_type]
          has_type.Imp[OF Cs_type v_type]]
        As_type As_type BC_beta refl_A
      by (rule CEV_T6_WI_biconditional_cong)
    have M2_M3:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?M2 \<longleftrightarrow>\<^sub>o ?M3)"
      using v_type As_type Cs_type
      by (rule CEV_T6_WI_biconditional_reassociate)
    have R_M3:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?R \<longleftrightarrow>\<^sub>o ?M3)"
      using
        CEV_pp_biconditional_operator_apply[
          OF has_type.Conj[
            OF has_type.Imp[OF As_type Cs_type]
              has_type.Imp[OF Cs_type As_type]]
            v_type]
      by (simp add: shift_pp_biconditional_operator_T6_WI)
    have M3_R:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?M3 \<longleftrightarrow>\<^sub>o ?R)"
      using R_type M3_type R_M3 by (rule CEV_biconditional_sym)
    have L_M1:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?L \<longleftrightarrow>\<^sub>o ?M1)"
      using L_type M0_type M1_type L_M0 M0_M1
      by (rule CEV_biconditional_trans)
    have L_M2:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?L \<longleftrightarrow>\<^sub>o ?M2)"
      using L_type M1_type M2_type L_M1 M1_M2
      by (rule CEV_biconditional_trans)
    have L_M3:
      "Prop # \<Gamma> \<turnstile>\<^sub>CEV (?L \<longleftrightarrow>\<^sub>o ?M3)"
      using L_type M2_type M3_type L_M2 M2_M3
      by (rule CEV_biconditional_trans)
    show "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      (App (shift (pp_compose ?BA ?BC)) (Var 0)
        \<longleftrightarrow>\<^sub>o App (shift ?BAC) (Var 0))"
      using L_type M3_type R_type L_M3 M3_R
      by (simp add: shift_pp_biconditional_operator_T6_WI)
        (rule CEV_biconditional_trans)
  qed
  show ?thesis
    using op_eq by (simp add: pp_unary_ty_def)
qed

lemma pp_biconditional_builder_purity_axiom:
  "pp_pure
      (Prop \<rightarrow>\<^sub>o pp_unary_ty)
      pp_biconditional_builder \<in> pp_T6_core_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
proof (intro UnI1 CollectI exI conjI)
  show "[] \<turnstile> pp_biconditional_builder :
      Prop \<rightarrow>\<^sub>o pp_unary_ty"
    by (rule typed_pp_biconditional_builder)
  show "consts_of pp_biconditional_builder = {}"
    by (simp add: pp_biconditional_builder_def)
qed simp

lemma CEV_axiom_biconditional_operator_pure_from:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and pure_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure Prop A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_unary_ty (pp_biconditional_operator A)"
proof -
  have closure:
    "pp_application_closure Prop pp_unary_ty \<in> T"
    using pp_T6_application_closure_axiom core by blast
  have builder_pure_core:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure
        (Prop \<rightarrow>\<^sub>o pp_unary_ty)
        pp_biconditional_builder"
    using pp_biconditional_builder_purity_axiom
      typed_pp_pure[OF typed_pp_biconditional_builder]
    by (rule CEV_axiom_proves.Axiom)
  have builder_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure
        (Prop \<rightarrow>\<^sub>o pp_unary_ty)
        pp_biconditional_builder"
    using CEV_axiom_proves_mono[OF builder_pure_core core]
    by (rule CEV_axiom_from.Theorem)
  show ?thesis
    unfolding pp_biconditional_operator_def
    using closure typed_pp_biconditional_builder A_type
      builder_pure pure_A
    by (rule pp_axiom_application_closed_from)
qed

lemma CEV_axiom_biconditional_pure_from:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and pure_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop A"
    and pure_C:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop C"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure Prop (A \<longleftrightarrow>\<^sub>o C)"
proof -
  let ?BC = "pp_biconditional_operator C"
  let ?M = "App ?BC A"
  let ?AC = "A \<longleftrightarrow>\<^sub>o C"
  have BC_type: "\<Gamma> \<turnstile> ?BC : pp_unary_ty"
    using C_type by (rule typed_pp_biconditional_operator)
  have M_type: "\<Gamma> \<turnstile> ?M : Prop"
    using BC_type A_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have AC_type: "\<Gamma> \<turnstile> ?AC : Prop"
    using A_type C_type by (intro has_type.Conj has_type.Imp)
  have pure_BC:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?BC"
    using core C_type pure_C
    by (rule CEV_axiom_biconditional_operator_pure_from)
  have closure:
    "pp_application_closure Prop Prop \<in> T"
    using pp_T6_application_closure_axiom core by blast
  have pure_M:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop ?M"
    using closure BC_type[unfolded pp_unary_ty_def]
      A_type pure_BC pure_A
    unfolding pp_unary_ty_def
    by (rule pp_axiom_application_closed_from)
  have M_AC:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?M ?AC"
  proof (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
    show "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop ?M ?AC"
      using M_type AC_type
        CEV_pp_biconditional_operator_apply[OF C_type A_type]
      by (rule CEV_zeroary_equivalence)
  qed
  show ?thesis
    using M_type AC_type pure_M M_AC
    by (rule CEV_axiom_from_pure_eq_transport)
qed

lemma CEV_axiom_biconditional_self_inverse:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq pp_unary_ty
      (pp_compose
        (pp_biconditional_operator A)
        (pp_biconditional_operator A))
      pp_identity_operator"
proof -
  let ?BA = "pp_biconditional_operator A"
  let ?AA = "A \<longleftrightarrow>\<^sub>o A"
  let ?BAA = "pp_biconditional_operator ?AA"
  let ?BT = "pp_biconditional_operator ObjTrue"
  have BA_type: "\<Gamma> \<turnstile> ?BA : pp_unary_ty"
    using A_type by (rule typed_pp_biconditional_operator)
  have AA_type: "\<Gamma> \<turnstile> ?AA : Prop"
    using A_type by (intro has_type.Conj has_type.Imp)
  have BAA_type: "\<Gamma> \<turnstile> ?BAA : pp_unary_ty"
    using AA_type by (rule typed_pp_biconditional_operator)
  have BT_type: "\<Gamma> \<turnstile> ?BT : pp_unary_ty"
    using typed_ObjTrue by (rule typed_pp_biconditional_operator)
  have comp_type:
    "\<Gamma> \<turnstile> pp_compose ?BA ?BA : pp_unary_ty"
    using BA_type BA_type by (rule typed_pp_compose)
  have comp_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty (pp_compose ?BA ?BA) ?BAA"
    using CEV_T6_WI_biconditional_compose[OF A_type A_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have AA:
    "\<Gamma> \<turnstile>\<^sub>CEV ?AA"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma> ?AA"
      unfolding prop_tautology_def
      using AA_type by (auto simp: prop_eval.simps)
  qed
  have AA_true_iff:
    "\<Gamma> \<turnstile>\<^sub>CEV (?AA \<longleftrightarrow>\<^sub>o ObjTrue)"
    using AA by (rule CEV_theorem_equiv_ObjTrue)
  have AA_true_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop ?AA ObjTrue"
    using AA_type typed_ObjTrue AA_true_iff
    by (rule CEV_zeroary_equivalence)
  have op_transport:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Eq Prop ?AA ObjTrue)
        (Eq pp_unary_ty ?BAA ?BT)"
    using CEV_axiom_biconditional_operator_eq_transport[
      OF AA_type typed_ObjTrue]
    by (rule CEV_axiom_from.Theorem)
  have op_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?BAA ?BT"
    using
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[OF AA_true_eq]]
      op_transport
    by (rule CEV_axiom_from.MP)
  have true_id:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?BT pp_identity_operator"
    using CEV_pp_biconditional_ObjTrue_eq_identity
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have comp_true:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty (pp_compose ?BA ?BA) ?BT"
    using comp_type BAA_type BT_type comp_eq op_eq
    by (rule CEV_axiom_from_eq_trans)
  show ?thesis
    using comp_type BT_type typed_pp_identity_operator
      comp_true true_id
    by (rule CEV_axiom_from_eq_trans)
qed

lemma CEV_axiom_from_group_member_of_pure_self_inverse:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and pure_Z:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty Z"
    and involution:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (pp_compose Z Z)
          pp_identity_operator"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
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
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (Eq pp_unary_ty
          (pp_compose Z Z)
          pp_identity_operator)
        (Eq pp_unary_ty
          (pp_compose Z Z)
          pp_identity_operator)"
    using involution involution by (rule CEV_axiom_from_conj_intro)
  have witness:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty Z)
        (Conj
          (Eq pp_unary_ty
            (pp_compose Z Z)
            pp_identity_operator)
          (Eq pp_unary_ty
            (pp_compose Z Z)
            pp_identity_operator))"
    using pure_Z equations by (rule CEV_axiom_from_conj_intro)
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
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
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
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
      (simp add: subst0_def pp_pure_def pp_Pure_def
        subst_left subst_right subst_id)
  have reversible:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_reversible Z"
    using witness eg by (rule CEV_axiom_from.MP)
  show ?thesis
    unfolding pp_group_member_def
    using pure_Z reversible by (rule CEV_axiom_from_conj_intro)
qed

lemma CEV_axiom_biconditional_group_member_from:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and pure_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure Prop A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_group_member (pp_biconditional_operator A)"
proof -
  have pure_B:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty (pp_biconditional_operator A)"
    using core A_type pure_A
    by (rule CEV_axiom_biconditional_operator_pure_from)
  have involution:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty
        (pp_compose
          (pp_biconditional_operator A)
          (pp_biconditional_operator A))
        pp_identity_operator"
    using A_type by (rule CEV_axiom_biconditional_self_inverse)
  show ?thesis
    using typed_pp_biconditional_operator[OF A_type]
      pure_B involution
    by (rule CEV_axiom_from_group_member_of_pure_self_inverse)
qed

lemma CEV_axiom_T6_WI_comparison_operator_pure_from:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and pure_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_unary_ty (pp_T6_WI_comparison_operator A)"
proof -
  have BA_type:
    "\<Gamma> \<turnstile> pp_biconditional_operator A : pp_unary_ty"
    using A_type by (rule typed_pp_biconditional_operator)
  have pure_BA:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty (pp_biconditional_operator A)"
    using core A_type pure_A
    by (rule CEV_axiom_biconditional_operator_pure_from)
  have pure_D:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty pp_T6_liar"
    using CEV_axiom_proves_mono[OF pp_T6_liar_pure core]
    by (rule CEV_axiom_from.Theorem)
  show ?thesis
    unfolding pp_T6_WI_comparison_operator_def
    using core BA_type typed_pp_T6_liar pure_BA pure_D
    by (rule pp_compose_pure_from)
qed

lemma CEV_axiom_T6_WI_collision_operator_pure_from:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and E_type: "\<Gamma> \<turnstile> E : Prop"
    and pure_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop A"
    and pure_E:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop E"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_unary_ty (pp_T6_WI_collision_operator A E)"
proof -
  have Y_type:
    "\<Gamma> \<turnstile> pp_T6_WI_comparison_operator A : pp_unary_ty"
    using A_type by (rule typed_pp_T6_WI_comparison_operator)
  have BE_type:
    "\<Gamma> \<turnstile> pp_biconditional_operator E : pp_unary_ty"
    using E_type by (rule typed_pp_biconditional_operator)
  have pure_Y:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty (pp_T6_WI_comparison_operator A)"
    using core A_type pure_A
    by (rule CEV_axiom_T6_WI_comparison_operator_pure_from)
  have pure_BE:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty (pp_biconditional_operator E)"
    using core E_type pure_E
    by (rule CEV_axiom_biconditional_operator_pure_from)
  show ?thesis
    unfolding pp_T6_WI_collision_operator_def
    using core Y_type BE_type pure_Y pure_BE
    by (rule pp_compose_pure_from)
qed

lemma CEV_axiom_T6_WI_collision_decomposition:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and E_type: "\<Gamma> \<turnstile> E : Prop"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop
      (pp_T6_WI_diagonal_point r A)
      (App
        (pp_T6_WI_collision_operator A E)
        (App (pp_biconditional_operator E) r))"
proof -
  let ?BA = "pp_biconditional_operator A"
  let ?BE = "pp_biconditional_operator E"
  let ?Y = "pp_T6_WI_comparison_operator A"
  let ?X = "pp_T6_WI_collision_operator A E"
  let ?q = "App ?BE r"
  let ?BEq = "App ?BE ?q"
  let ?D_BEq = "App pp_T6_liar ?BEq"
  let ?BA_D_BEq = "App ?BA ?D_BEq"
  let ?p = "pp_T6_WI_diagonal_point r A"
  have BA_type: "\<Gamma> \<turnstile> ?BA : pp_unary_ty"
    using A_type by (rule typed_pp_biconditional_operator)
  have BE_type: "\<Gamma> \<turnstile> ?BE : pp_unary_ty"
    using E_type by (rule typed_pp_biconditional_operator)
  have Y_type: "\<Gamma> \<turnstile> ?Y : pp_unary_ty"
    using A_type by (rule typed_pp_T6_WI_comparison_operator)
  have X_type: "\<Gamma> \<turnstile> ?X : pp_unary_ty"
    using A_type E_type by (rule typed_pp_T6_WI_collision_operator)
  have q_type: "\<Gamma> \<turnstile> ?q : Prop"
    using BE_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have BEq_type: "\<Gamma> \<turnstile> ?BEq : Prop"
    using BE_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have D_BEq_type: "\<Gamma> \<turnstile> ?D_BEq : Prop"
    using typed_pp_T6_liar BEq_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have BA_D_BEq_type: "\<Gamma> \<turnstile> ?BA_D_BEq : Prop"
    using BA_type D_BEq_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have p_type: "\<Gamma> \<turnstile> ?p : Prop"
    using r_type A_type by (rule typed_pp_T6_WI_diagonal_point)
  have Xq_type: "\<Gamma> \<turnstile> App ?X ?q : Prop"
    using X_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have involution:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty
        (pp_compose ?BE ?BE)
        pp_identity_operator"
    using E_type by (rule CEV_axiom_biconditional_self_inverse)
  have cancel:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?BEq r"
    using BE_type BE_type r_type involution
    by (rule CEV_axiom_from_T6_inverse_cancel)
  have D_cancel:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?D_BEq (App pp_T6_liar r)"
    using typed_pp_T6_liar BEq_type r_type cancel
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have BA_cancel:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?BA_D_BEq ?p"
    using BA_type D_BEq_type
      has_type.App[
        OF typed_pp_T6_liar[unfolded pp_unary_ty_def] r_type]
      D_cancel
    unfolding pp_T6_WI_diagonal_point_def pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have outer_beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?X ?q) (App ?Y ?BEq)"
    unfolding pp_T6_WI_collision_operator_def
    using CEV_pp_compose_apply_eq[OF Y_type BE_type q_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have inner_beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?Y ?BEq) ?BA_D_BEq"
    unfolding pp_T6_WI_comparison_operator_def
    using CEV_pp_compose_apply_eq[
      OF BA_type typed_pp_T6_liar BEq_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have YBEq_type: "\<Gamma> \<turnstile> App ?Y ?BEq : Prop"
    using Y_type BEq_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have first:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?X ?q) ?BA_D_BEq"
    using Xq_type YBEq_type BA_D_BEq_type outer_beta inner_beta
    by (rule CEV_axiom_from_eq_trans)
  have Xq_p:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?X ?q) ?p"
    using Xq_type BA_D_BEq_type p_type first BA_cancel
    by (rule CEV_axiom_from_eq_trans)
  show ?thesis
    using Xq_type p_type Xq_p
    by (rule CEV_axiom_from_eq_sym)
qed

lemma CEV_axiom_T6_WI_collision_value:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and E_type: "\<Gamma> \<turnstile> E : Prop"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop
      (App
        (pp_T6_WI_collision_operator A E)
        (pp_T6_WI_diagonal_point r A))
      (App
        (pp_biconditional_operator A)
        (pp_T6_WI_a r (E \<longleftrightarrow>\<^sub>o A)))"
proof -
  let ?D = pp_T6_liar
  let ?BA = "pp_biconditional_operator A"
  let ?BE = "pp_biconditional_operator E"
  let ?C = "E \<longleftrightarrow>\<^sub>o A"
  let ?BC = "pp_biconditional_operator ?C"
  let ?Y = "pp_T6_WI_comparison_operator A"
  let ?X = "pp_T6_WI_collision_operator A E"
  let ?d = "App ?D r"
  let ?p = "pp_T6_WI_diagonal_point r A"
  let ?BEp = "App ?BE ?p"
  let ?BCd = "App ?BC ?d"
  let ?D_BEp = "App ?D ?BEp"
  let ?D_BCd = "App ?D ?BCd"
  let ?BA_D_BEp = "App ?BA ?D_BEp"
  let ?target = "App ?BA (pp_T6_WI_a r ?C)"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have BA_type: "\<Gamma> \<turnstile> ?BA : pp_unary_ty"
    using A_type by (rule typed_pp_biconditional_operator)
  have BE_type: "\<Gamma> \<turnstile> ?BE : pp_unary_ty"
    using E_type by (rule typed_pp_biconditional_operator)
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using E_type A_type by (intro has_type.Conj has_type.Imp)
  have BC_type: "\<Gamma> \<turnstile> ?BC : pp_unary_ty"
    using C_type by (rule typed_pp_biconditional_operator)
  have Y_type: "\<Gamma> \<turnstile> ?Y : pp_unary_ty"
    using A_type by (rule typed_pp_T6_WI_comparison_operator)
  have X_type: "\<Gamma> \<turnstile> ?X : pp_unary_ty"
    using A_type E_type by (rule typed_pp_T6_WI_collision_operator)
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have p_type: "\<Gamma> \<turnstile> ?p : Prop"
    using r_type A_type by (rule typed_pp_T6_WI_diagonal_point)
  have BEp_type: "\<Gamma> \<turnstile> ?BEp : Prop"
    using BE_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have BCd_type: "\<Gamma> \<turnstile> ?BCd : Prop"
    using BC_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have D_BEp_type: "\<Gamma> \<turnstile> ?D_BEp : Prop"
    using D_type BEp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have D_BCd_type: "\<Gamma> \<turnstile> ?D_BCd : Prop"
    using D_type BCd_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have BA_D_BEp_type: "\<Gamma> \<turnstile> ?BA_D_BEp : Prop"
    using BA_type D_BEp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have aC_type: "\<Gamma> \<turnstile> pp_T6_WI_a r ?C : Prop"
    using r_type C_type by (rule typed_pp_T6_WI_a)
  have target_type: "\<Gamma> \<turnstile> ?target : Prop"
    using BA_type aC_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xp_type: "\<Gamma> \<turnstile> App ?X ?p : Prop"
    using X_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have YBEp_type: "\<Gamma> \<turnstile> App ?Y ?BEp : Prop"
    using Y_type BEp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have comp_type:
    "\<Gamma> \<turnstile> pp_compose ?BE ?BA : pp_unary_ty"
    using BE_type BA_type by (rule typed_pp_compose)
  have comp_d_type:
    "\<Gamma> \<turnstile> App (pp_compose ?BE ?BA) ?d : Prop"
    using comp_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have op_reindex:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty (pp_compose ?BE ?BA) ?BC"
    using CEV_T6_WI_biconditional_compose[OF E_type A_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have comp_beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App (pp_compose ?BE ?BA) ?d) ?BEp"
    unfolding pp_T6_WI_diagonal_point_def
    using CEV_pp_compose_apply_eq[OF BE_type BA_type d_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have comp_beta_sym:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?BEp (App (pp_compose ?BE ?BA) ?d)"
    using comp_d_type BEp_type comp_beta
    by (rule CEV_axiom_from_eq_sym)
  have comp_reindex:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App (pp_compose ?BE ?BA) ?d) ?BCd"
    using comp_type BC_type d_type op_reindex
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have BEp_BCd:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?BEp ?BCd"
    using BEp_type comp_d_type BCd_type
      comp_beta_sym comp_reindex
    by (rule CEV_axiom_from_eq_trans)
  have D_reindex:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?D_BEp ?D_BCd"
    using D_type BEp_type BCd_type BEp_BCd
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have BA_reindex:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?BA_D_BEp ?target"
    using BA_type D_BEp_type D_BCd_type D_reindex
    unfolding pp_T6_WI_a_def pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have outer_beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?X ?p) (App ?Y ?BEp)"
    unfolding pp_T6_WI_collision_operator_def
    using CEV_pp_compose_apply_eq[OF Y_type BE_type p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have inner_beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?Y ?BEp) ?BA_D_BEp"
    unfolding pp_T6_WI_comparison_operator_def
    using CEV_pp_compose_apply_eq[OF BA_type D_type BEp_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have first:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?X ?p) ?BA_D_BEp"
    using Xp_type YBEp_type BA_D_BEp_type outer_beta inner_beta
    by (rule CEV_axiom_from_eq_trans)
  show ?thesis
    using Xp_type BA_D_BEp_type target_type first BA_reindex
    by (rule CEV_axiom_from_eq_trans)
qed

lemma CEV_axiom_T6_WI_collision_neg_equiv:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and E_type: "\<Gamma> \<turnstile> E : Prop"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    (Neg
        (App
          (pp_T6_WI_collision_operator A E)
          (pp_T6_WI_diagonal_point r A))
      \<longleftrightarrow>\<^sub>o
      (pp_T6_WI_a r (E \<longleftrightarrow>\<^sub>o A)
        \<longleftrightarrow>\<^sub>o Neg A))"
proof -
  let ?C = "E \<longleftrightarrow>\<^sub>o A"
  let ?aC = "pp_T6_WI_a r ?C"
  let ?Xv =
    "App
      (pp_T6_WI_collision_operator A E)
      (pp_T6_WI_diagonal_point r A)"
  let ?BAaC = "App (pp_biconditional_operator A) ?aC"
  let ?mid = "?aC \<longleftrightarrow>\<^sub>o A"
  let ?target = "?aC \<longleftrightarrow>\<^sub>o Neg A"
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using E_type A_type by (intro has_type.Conj has_type.Imp)
  have aC_type: "\<Gamma> \<turnstile> ?aC : Prop"
    using r_type C_type by (rule typed_pp_T6_WI_a)
  have Xv_type: "\<Gamma> \<turnstile> ?Xv : Prop"
    using typed_pp_T6_WI_collision_operator[OF A_type E_type]
      typed_pp_T6_WI_diagonal_point[OF r_type A_type]
    unfolding pp_unary_ty_def
    by (rule has_type.App)
  have BAaC_type: "\<Gamma> \<turnstile> ?BAaC : Prop"
    using typed_pp_biconditional_operator[OF A_type] aC_type
    unfolding pp_unary_ty_def
    by (rule has_type.App)
  have mid_type: "\<Gamma> \<turnstile> ?mid : Prop"
    using aC_type A_type by (intro has_type.Conj has_type.Imp)
  have target_type: "\<Gamma> \<turnstile> ?target : Prop"
    using aC_type A_type
    by (intro has_type.Conj has_type.Imp has_type.Neg)
  have value_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?Xv ?BAaC"
    using r_type A_type E_type
    by (rule CEV_axiom_T6_WI_collision_value)
  have beta_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?BAaC ?mid"
  proof (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
    show "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop ?BAaC ?mid"
      using BAaC_type mid_type
        CEV_pp_biconditional_operator_apply[OF A_type aC_type]
      by (rule CEV_zeroary_equivalence)
  qed
  have value_mid:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?Xv ?mid"
    using Xv_type BAaC_type mid_type value_eq beta_eq
    by (rule CEV_axiom_from_eq_trans)
  have neg_value_mid:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?Xv) (Neg ?mid)"
    using Xv_type mid_type value_mid
    by (rule CEV_axiom_from_T5_neg_cong)
  have neg_mid_target:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?mid) ?target"
  proof (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
    show "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (Neg ?mid) ?target"
      using has_type.Neg[OF mid_type] target_type
        CEV_T6_WI_negated_biconditional[OF aC_type A_type]
      by (rule CEV_zeroary_equivalence)
  qed
  have final_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?Xv) ?target"
    using has_type.Neg[OF Xv_type] has_type.Neg[OF mid_type]
      target_type neg_value_mid neg_mid_target
    by (rule CEV_axiom_from_eq_trans)
  have eq_to_iff:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Eq Prop (Neg ?Xv) ?target)
        (Neg ?Xv \<longleftrightarrow>\<^sub>o ?target)"
    using CEV_eq_prop_biconditional_imp[
      OF has_type.Neg[OF Xv_type] target_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using final_eq eq_to_iff by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_prop_tautology:
  assumes taut: "prop_tautology \<Gamma> A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
  using CEV_prop_tautology[OF taut]
  by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)

lemma CEV_axiom_from_biconditional_trans:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and AB:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        (A \<longleftrightarrow>\<^sub>o B)"
    and BC:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        (B \<longleftrightarrow>\<^sub>o C)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    (A \<longleftrightarrow>\<^sub>o C)"
proof -
  have taut:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (A \<longleftrightarrow>\<^sub>o B)
        (Imp
          (B \<longleftrightarrow>\<^sub>o C)
          (A \<longleftrightarrow>\<^sub>o C))"
  proof (rule CEV_axiom_from_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (A \<longleftrightarrow>\<^sub>o B)
        (Imp
          (B \<longleftrightarrow>\<^sub>o C)
          (A \<longleftrightarrow>\<^sub>o C)))"
    proof (unfold prop_tautology_def, intro conjI)
      show "\<Gamma> \<turnstile>
        Imp
          (A \<longleftrightarrow>\<^sub>o B)
          (Imp
            (B \<longleftrightarrow>\<^sub>o C)
            (A \<longleftrightarrow>\<^sub>o C)) : Prop"
        using A_type B_type C_type
        by (intro has_type.Imp has_type.Conj)
    next
      show "\<forall>v. prop_eval v
        (Imp
          (A \<longleftrightarrow>\<^sub>o B)
          (Imp
            (B \<longleftrightarrow>\<^sub>o C)
            (A \<longleftrightarrow>\<^sub>o C)))"
        apply (simp only: prop_eval.simps)
        by blast
    qed
  qed
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (B \<longleftrightarrow>\<^sub>o C)
        (A \<longleftrightarrow>\<^sub>o C)"
    using AB taut by (rule CEV_axiom_from.MP)
  show ?thesis
    using BC step by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_T6_WI_index_collapse:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop
      (pp_T6_WI_a r
        ((C \<longleftrightarrow>\<^sub>o A) \<longleftrightarrow>\<^sub>o A))
      (pp_T6_WI_a r C)"
proof -
  let ?E = "C \<longleftrightarrow>\<^sub>o A"
  let ?K = "?E \<longleftrightarrow>\<^sub>o A"
  let ?BK = "pp_biconditional_operator ?K"
  let ?BC = "pp_biconditional_operator C"
  let ?d = "App pp_T6_liar r"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using C_type A_type by (intro has_type.Conj has_type.Imp)
  have K_type: "\<Gamma> \<turnstile> ?K : Prop"
    using has_type.Conj[
      OF has_type.Imp[OF E_type A_type]
        has_type.Imp[OF A_type E_type]] .
  have BK_type: "\<Gamma> \<turnstile> ?BK : pp_unary_ty"
    using K_type by (rule typed_pp_biconditional_operator)
  have BC_type: "\<Gamma> \<turnstile> ?BC : pp_unary_ty"
    using C_type by (rule typed_pp_biconditional_operator)
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using typed_pp_T6_liar r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have K_C_iff:
    "\<Gamma> \<turnstile>\<^sub>CEV (?K \<longleftrightarrow>\<^sub>o C)"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma> (?K \<longleftrightarrow>\<^sub>o C)"
    proof (unfold prop_tautology_def, intro conjI)
      show "\<Gamma> \<turnstile> (?K \<longleftrightarrow>\<^sub>o C) : Prop"
        using has_type.Conj[
          OF has_type.Imp[OF K_type C_type]
            has_type.Imp[OF C_type K_type]] .
    next
      show "\<forall>v. prop_eval v (?K \<longleftrightarrow>\<^sub>o C)"
        apply (simp only: prop_eval.simps)
        by blast
    qed
  qed
  have K_C_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop ?K C"
    using K_type C_type K_C_iff
    by (rule CEV_zeroary_equivalence)
  have op_rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Eq Prop ?K C) (Eq pp_unary_ty ?BK ?BC)"
    using CEV_axiom_biconditional_operator_eq_transport[
      OF K_type C_type]
    by (rule CEV_axiom_from.Theorem)
  have op_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?BK ?BC"
    using
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[OF K_C_eq]]
      op_rule
    by (rule CEV_axiom_from.MP)
  have arg_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?BK ?d) (App ?BC ?d)"
    using BK_type BC_type d_type op_eq
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have BKd_type: "\<Gamma> \<turnstile> App ?BK ?d : Prop"
    using BK_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have BCd_type: "\<Gamma> \<turnstile> App ?BC ?d : Prop"
    using BC_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_T6_WI_a_def
    using typed_pp_T6_liar BKd_type BCd_type arg_eq
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
qed

lemma CEV_axiom_T6_WI_collision_neg_equiv_reindexed:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    (Neg
        (App
          (pp_T6_WI_collision_operator
            A (C \<longleftrightarrow>\<^sub>o A))
          (pp_T6_WI_diagonal_point r A))
      \<longleftrightarrow>\<^sub>o
      (pp_T6_WI_a r C \<longleftrightarrow>\<^sub>o Neg A))"
proof -
  let ?E = "C \<longleftrightarrow>\<^sub>o A"
  let ?K = "?E \<longleftrightarrow>\<^sub>o A"
  let ?aK = "pp_T6_WI_a r ?K"
  let ?aC = "pp_T6_WI_a r C"
  let ?L =
    "Neg
      (App
        (pp_T6_WI_collision_operator A ?E)
        (pp_T6_WI_diagonal_point r A))"
  let ?M = "?aK \<longleftrightarrow>\<^sub>o Neg A"
  let ?R = "?aC \<longleftrightarrow>\<^sub>o Neg A"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using C_type A_type by (intro has_type.Conj has_type.Imp)
  have K_type: "\<Gamma> \<turnstile> ?K : Prop"
    using has_type.Conj[
      OF has_type.Imp[OF E_type A_type]
        has_type.Imp[OF A_type E_type]] .
  have aK_type: "\<Gamma> \<turnstile> ?aK : Prop"
    using r_type K_type by (rule typed_pp_T6_WI_a)
  have aC_type: "\<Gamma> \<turnstile> ?aC : Prop"
    using r_type C_type by (rule typed_pp_T6_WI_a)
  have X_type:
    "\<Gamma> \<turnstile> pp_T6_WI_collision_operator A ?E : pp_unary_ty"
    using A_type E_type by (rule typed_pp_T6_WI_collision_operator)
  have p_type:
    "\<Gamma> \<turnstile> pp_T6_WI_diagonal_point r A : Prop"
    using r_type A_type by (rule typed_pp_T6_WI_diagonal_point)
  have L_type: "\<Gamma> \<turnstile> ?L : Prop"
    using X_type p_type unfolding pp_unary_ty_def
    by (intro has_type.Neg has_type.App)
  have M_type: "\<Gamma> \<turnstile> ?M : Prop"
    using aK_type A_type
    by (intro has_type.Conj has_type.Imp has_type.Neg)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using aC_type A_type
    by (intro has_type.Conj has_type.Imp has_type.Neg)
  have L_M:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?L \<longleftrightarrow>\<^sub>o ?M)"
    using r_type A_type E_type
    by (rule CEV_axiom_T6_WI_collision_neg_equiv)
  have index_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?aK ?aC"
    using r_type A_type C_type
    by (rule CEV_axiom_T6_WI_index_collapse)
  have index_iff_rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Eq Prop ?aK ?aC) (?aK \<longleftrightarrow>\<^sub>o ?aC)"
    using CEV_eq_prop_biconditional_imp[OF aK_type aC_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have index_iff:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?aK \<longleftrightarrow>\<^sub>o ?aC)"
    using index_eq index_iff_rule by (rule CEV_axiom_from.MP)
  have congr_rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (?aK \<longleftrightarrow>\<^sub>o ?aC)
        (?M \<longleftrightarrow>\<^sub>o ?R)"
  proof (rule CEV_axiom_from_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp (?aK \<longleftrightarrow>\<^sub>o ?aC)
        (?M \<longleftrightarrow>\<^sub>o ?R))"
    proof (unfold prop_tautology_def, intro conjI)
      show "\<Gamma> \<turnstile>
        Imp (?aK \<longleftrightarrow>\<^sub>o ?aC)
          (?M \<longleftrightarrow>\<^sub>o ?R) : Prop"
        using aK_type aC_type A_type
        by (intro has_type.Imp has_type.Conj has_type.Neg)
    next
      show "\<forall>v. prop_eval v
        (Imp (?aK \<longleftrightarrow>\<^sub>o ?aC)
          (?M \<longleftrightarrow>\<^sub>o ?R))"
        apply (simp only: prop_eval.simps)
        by blast
    qed
  qed
  have M_R:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?M \<longleftrightarrow>\<^sub>o ?R)"
    using index_iff congr_rule by (rule CEV_axiom_from.MP)
  show ?thesis
    using L_type M_type R_type L_M M_R
    by (rule CEV_axiom_from_biconditional_trans)
qed

theorem CEV_T6_WI_master_forward:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_fun_prime r)
        (Conj
          (pp_pure Prop A)
          (pp_T6_WI_a r A)))
      (Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (pp_T6_WI_a (shift r) (Var 0)
            \<longleftrightarrow>\<^sub>o Neg (shift A))))"
proof -
  let ?H =
    "Conj
      (pp_fun_prime r)
      (Conj
        (pp_pure Prop A)
        (pp_T6_WI_a r A))"
  let ?C = "Var 0"
  let ?rs = "shift r"
  let ?As = "shift A"
  let ?Hs = "shift ?H"
  let ?PC = "pp_pure Prop ?C"
  let ?E = "?C \<longleftrightarrow>\<^sub>o ?As"
  let ?BE = "pp_biconditional_operator ?E"
  let ?X = "pp_T6_WI_collision_operator ?As ?E"
  let ?q = "App ?BE ?rs"
  let ?p = "pp_T6_WI_diagonal_point ?rs ?As"
  let ?aA = "pp_T6_WI_a ?rs ?As"
  let ?R =
    "pp_T6_WI_a ?rs ?C \<longleftrightarrow>\<^sub>o Neg ?As"
  let ?Q = "Imp ?PC ?R"
  let ?S = "insert ?PC {?Hs}"
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_fun_prime[OF r_type]
      typed_pp_pure[OF A_type]
      typed_pp_T6_WI_a[OF r_type A_type]
    by (intro has_type.Conj)
  have rs_type: "Prop # \<Gamma> \<turnstile> ?rs : Prop"
    using r_type by (rule typed_shift_ctx)
  have As_type: "Prop # \<Gamma> \<turnstile> ?As : Prop"
    using A_type by (rule typed_shift_ctx)
  have Hs_type: "Prop # \<Gamma> \<turnstile> ?Hs : Prop"
    using H_type by (rule typed_shift_ctx)
  have C_type: "Prop # \<Gamma> \<turnstile> ?C : Prop"
    by (rule typed_var0)
  have PC_type: "Prop # \<Gamma> \<turnstile> ?PC : Prop"
    using C_type by (rule typed_pp_pure)
  have E_type: "Prop # \<Gamma> \<turnstile> ?E : Prop"
    using C_type As_type by (intro has_type.Conj has_type.Imp)
  have BE_type: "Prop # \<Gamma> \<turnstile> ?BE : pp_unary_ty"
    using E_type by (rule typed_pp_biconditional_operator)
  have X_type: "Prop # \<Gamma> \<turnstile> ?X : pp_unary_ty"
    using As_type E_type by (rule typed_pp_T6_WI_collision_operator)
  have q_type: "Prop # \<Gamma> \<turnstile> ?q : Prop"
    using BE_type rs_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have p_type: "Prop # \<Gamma> \<turnstile> ?p : Prop"
    using rs_type As_type by (rule typed_pp_T6_WI_diagonal_point)
  have aA_type: "Prop # \<Gamma> \<turnstile> ?aA : Prop"
    using rs_type As_type by (rule typed_pp_T6_WI_a)
  have R_type: "Prop # \<Gamma> \<turnstile> ?R : Prop"
    using typed_pp_T6_WI_a[OF rs_type C_type] As_type
    by (intro has_type.Conj has_type.Imp has_type.Neg)
  have Q_type: "Prop # \<Gamma> \<turnstile> ?Q : Prop"
    using PC_type R_type by (rule has_type.Imp)
  have d_H:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Hs"
    using Hs_type by (intro CEV_axiom_from.Assumption) simp
  have d_PC:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PC"
    using PC_type by (intro CEV_axiom_from.Assumption) simp
  have d_fun:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_fun_prime ?rs"
    using d_H
    by simp (rule CEV_axiom_from_conj_left)
  have d_tail:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_pure Prop ?As) ?aA"
    using d_H
    by simp (rule CEV_axiom_from_conj_right)
  have d_pure_A:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ?As"
    using d_tail by (rule CEV_axiom_from_conj_left)
  have d_aA:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?aA"
    using d_tail by (rule CEV_axiom_from_conj_right)
  have pure_E:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ?E"
    using core C_type As_type d_PC d_pure_A
    by (rule CEV_axiom_biconditional_pure_from)
  have group_BE:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_group_member ?BE"
    using core E_type pure_E
    by (rule CEV_axiom_biconditional_group_member_from)
  have fun_pair:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_fun_prime ?rs) (pp_group_member ?BE)"
    using d_fun group_BE by (rule CEV_axiom_from_conj_intro)
  have fun_rule:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj (pp_fun_prime ?rs) (pp_group_member ?BE))
        (pp_fun_prime ?q)"
    using CEV_fun_prime_under_group_member[
      OF core rs_type BE_type]
    by (rule CEV_axiom_from.Theorem)
  have fun_q:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_fun_prime ?q"
    using fun_pair fun_rule by (rule CEV_axiom_from.MP)
  have pure_X:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?X"
    using core As_type E_type d_pure_A pure_E
    by (rule CEV_axiom_T6_WI_collision_operator_pure_from)
  have decomposition:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?p (App ?X ?q)"
    using rs_type As_type E_type
    by (rule CEV_axiom_T6_WI_collision_decomposition)
  have not_Xp:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (App ?X ?p)"
    using p_type X_type q_type d_aA pure_X fun_q decomposition
    unfolding pp_T6_WI_a_as_liar_at_point
    by (rule CEV_axiom_from_T5_liar_elim)
  have collision_equiv:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (Neg (App ?X ?p) \<longleftrightarrow>\<^sub>o ?R)"
    using rs_type As_type C_type
    by (rule CEV_axiom_T6_WI_collision_neg_equiv_reindexed)
  have not_Xp_to_R:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Neg (App ?X ?p)) ?R"
    using collision_equiv by (rule CEV_axiom_from_conj_left)
  have d_R:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
    using not_Xp not_Xp_to_R by (rule CEV_axiom_from.MP)
  have under_H:
    "Prop # \<Gamma> ; T ; {?Hs} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Q"
  proof (rule CEV_axiom_from_deduction)
    show "Prop # \<Gamma> \<turnstile> ?PC : Prop"
      by (rule PC_type)
    show "Prop # \<Gamma> ; T ; insert ?PC {?Hs}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
      by (rule d_R)
  qed
  have body:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?Hs ?Q"
    using Hs_type under_H by (rule CEV_axiom_from_singleton_imp)
  show ?thesis
  proof (rule CEV_axiom_proves.Gen)
    show "\<Gamma> \<turnstile> ?H : Prop"
      by (rule H_type)
    show "Prop # \<Gamma> \<turnstile> ?Q : Prop"
      by (rule Q_type)
    show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?H) ?Q"
      using body by simp
  qed
qed

lemma CEV_axiom_WI_instance:
  assumes WI_in: "pp_WI \<in> T"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_group_member Z) (pp_biconditional_member Z)"
proof -
  have WI_type: "\<Gamma> \<turnstile> pp_WI : Prop"
    by (rule typed_pp_WI)
  have d_WI: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_WI"
    using WI_in WI_type by (rule CEV_axiom_proves.Axiom)
  have body_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      Imp
        (pp_group_member (Var 0))
        (pp_biconditional_member (Var 0)) : Prop"
    using typed_pp_group_member[
        OF typed_var0[
          where \<sigma> = pp_unary_ty and \<Gamma> = \<Gamma>]]
      typed_pp_biconditional_member[
        OF typed_var0[
          where \<sigma> = pp_unary_ty and \<Gamma> = \<Gamma>]]
    by (rule has_type.Imp)
  have raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 Z
        (Imp
          (pp_group_member (Var 0))
          (pp_biconditional_member (Var 0)))"
    using body_type Z_type d_WI
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

lemma CEV_axiom_WI_group_elim:
  assumes WI_in: "pp_WI \<in> T"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
    and bound:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (Conj
            (pp_pure Prop (Var 0))
            (Eq pp_unary_ty
              (shift Z)
              (pp_biconditional_operator (Var 0))))
          (shift Q)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_group_member Z) Q"
proof -
  let ?B =
    "Conj
      (pp_pure Prop (Var 0))
      (Eq pp_unary_ty
        (shift Z)
        (pp_biconditional_operator (Var 0)))"
  have B_type: "Prop # \<Gamma> \<turnstile> ?B : Prop"
  proof -
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    have Zs_type: "Prop # \<Gamma> \<turnstile> shift Z : pp_unary_ty"
      using Z_type by (rule typed_shift_ctx)
    have Bv_type:
      "Prop # \<Gamma> \<turnstile>
        pp_biconditional_operator (Var 0) : pp_unary_ty"
      using v_type by (rule typed_pp_biconditional_operator)
    show ?thesis
      using typed_pp_pure[OF v_type] Zs_type Bv_type
      by (intro has_type.Conj has_type.Eq)
  qed
  have exists_to_Q:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Exists Prop ?B) Q"
    using B_type Q_type bound
    by (rule CEV_axiom_proves.Inst)
  have group_to_exists:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_group_member Z) (Exists Prop ?B)"
    using CEV_axiom_WI_instance[OF WI_in Z_type]
    unfolding pp_biconditional_member_def .
  have G_type: "\<Gamma> \<turnstile> pp_group_member Z : Prop"
    using Z_type by (rule typed_pp_group_member)
  have d_G:
    "\<Gamma> ; T ; {pp_group_member Z}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member Z"
    using G_type by (intro CEV_axiom_from.Assumption) simp
  have d_exists:
    "\<Gamma> ; T ; {pp_group_member Z}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Exists Prop ?B"
    using d_G CEV_axiom_from.Theorem[OF group_to_exists]
    by (rule CEV_axiom_from.MP)
  have d_Q:
    "\<Gamma> ; T ; {pp_group_member Z}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Q"
    using d_exists CEV_axiom_from.Theorem[OF exists_to_Q]
    by (rule CEV_axiom_from.MP)
  show ?thesis
    using G_type d_Q by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_axiom_same_kind_elim:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
    and bound:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (Conj
            (pp_group_member (Var 0))
            (Eq pp_unary_ty
              (shift X)
              (pp_compose (shift Y) (Var 0))))
          (shift Q)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_same_kind X Y) Q"
proof -
  let ?B =
    "Conj
      (pp_group_member (Var 0))
      (Eq pp_unary_ty
        (shift X)
        (pp_compose (shift Y) (Var 0)))"
  have B_type: "pp_unary_ty # \<Gamma> \<turnstile> ?B : Prop"
  proof -
    have v_type:
      "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
      by (rule typed_var0)
    have Xs_type:
      "pp_unary_ty # \<Gamma> \<turnstile> shift X : pp_unary_ty"
      using X_type by (rule typed_shift_ctx)
    have Ys_type:
      "pp_unary_ty # \<Gamma> \<turnstile> shift Y : pp_unary_ty"
      using Y_type by (rule typed_shift_ctx)
    have comp_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_compose (shift Y) (Var 0) : pp_unary_ty"
      using Ys_type v_type by (rule typed_pp_compose)
    show ?thesis
      using typed_pp_group_member[OF v_type] Xs_type comp_type
      by (intro has_type.Conj has_type.Eq)
  qed
  have eliminated:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Exists pp_unary_ty ?B) Q"
    using B_type Q_type bound
    by (rule CEV_axiom_proves.Inst)
  show ?thesis
    using eliminated unfolding pp_same_kind_def .
qed

theorem CEV_T6_WI_group_collision_refutes:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and WI_in: "pp_WI \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure Prop A)
        (Forall Prop
          (Imp
            (pp_pure Prop (Var 0))
            (pp_T6_WI_a (shift r) (Var 0)
              \<longleftrightarrow>\<^sub>o Neg (shift A)))))
      (Imp
        (pp_group_member Z)
        (Neg
          (App
            (pp_compose
              (pp_T6_WI_comparison_operator A)
              Z)
            (pp_T6_WI_diagonal_point r A))))"
proof -
  let ?Y = "pp_T6_WI_comparison_operator A"
  let ?p = "pp_T6_WI_diagonal_point r A"
  let ?R = "Neg (App (pp_compose ?Y Z) ?p)"
  let ?H =
    "Conj
      (pp_pure Prop A)
      (Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (pp_T6_WI_a (shift r) (Var 0)
            \<longleftrightarrow>\<^sub>o Neg (shift A))))"
  let ?Q = "Imp ?H ?R"
  have Y_type: "\<Gamma> \<turnstile> ?Y : pp_unary_ty"
    using A_type by (rule typed_pp_T6_WI_comparison_operator)
  have p_type: "\<Gamma> \<turnstile> ?p : Prop"
    using r_type A_type by (rule typed_pp_T6_WI_diagonal_point)
  have YZ_type: "\<Gamma> \<turnstile> pp_compose ?Y Z : pp_unary_ty"
    using Y_type Z_type by (rule typed_pp_compose)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using YZ_type p_type unfolding pp_unary_ty_def
    by (intro has_type.Neg has_type.App)
  have rhs_type:
    "\<Gamma> \<turnstile>
      Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (pp_T6_WI_a (shift r) (Var 0)
            \<longleftrightarrow>\<^sub>o Neg (shift A))) : Prop"
  proof -
    have rs_type: "Prop # \<Gamma> \<turnstile> shift r : Prop"
      using r_type by (rule typed_shift_ctx)
    have As_type: "Prop # \<Gamma> \<turnstile> shift A : Prop"
      using A_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    show ?thesis
      using typed_pp_pure[OF v_type]
        typed_pp_T6_WI_a[OF rs_type v_type] As_type
      by (intro has_type.Forall has_type.Imp
          has_type.Conj has_type.Neg)
  qed
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_pure[OF A_type] rhs_type
    by (rule has_type.Conj)
  have Q_type: "\<Gamma> \<turnstile> ?Q : Prop"
    using H_type R_type by (rule has_type.Imp)

  let ?E = "Var 0"
  let ?Zs = "shift Z"
  let ?rs = "shift r"
  let ?As = "shift A"
  let ?Ys = "pp_T6_WI_comparison_operator ?As"
  let ?ps = "pp_T6_WI_diagonal_point ?rs ?As"
  let ?Hs = "shift ?H"
  let ?BE = "pp_biconditional_operator ?E"
  let ?B =
    "Conj
      (pp_pure Prop ?E)
      (Eq pp_unary_ty ?Zs ?BE)"
  let ?index = "?E \<longleftrightarrow>\<^sub>o ?As"
  let ?clause =
    "pp_T6_WI_a ?rs ?index \<longleftrightarrow>\<^sub>o Neg ?As"
  let ?collision = "pp_T6_WI_collision_operator ?As ?E"
  let ?left = "App (pp_compose ?Ys ?Zs) ?ps"
  let ?right = "App ?collision ?ps"
  let ?S = "insert ?Hs {?B}"
  have E_type: "Prop # \<Gamma> \<turnstile> ?E : Prop"
    by (rule typed_var0)
  have Zs_type: "Prop # \<Gamma> \<turnstile> ?Zs : pp_unary_ty"
    using Z_type by (rule typed_shift_ctx)
  have rs_type: "Prop # \<Gamma> \<turnstile> ?rs : Prop"
    using r_type by (rule typed_shift_ctx)
  have As_type: "Prop # \<Gamma> \<turnstile> ?As : Prop"
    using A_type by (rule typed_shift_ctx)
  have Ys_type: "Prop # \<Gamma> \<turnstile> ?Ys : pp_unary_ty"
    using As_type by (rule typed_pp_T6_WI_comparison_operator)
  have ps_type: "Prop # \<Gamma> \<turnstile> ?ps : Prop"
    using rs_type As_type by (rule typed_pp_T6_WI_diagonal_point)
  have Hs_type: "Prop # \<Gamma> \<turnstile> ?Hs : Prop"
    using H_type by (rule typed_shift_ctx)
  have BE_type: "Prop # \<Gamma> \<turnstile> ?BE : pp_unary_ty"
    using E_type by (rule typed_pp_biconditional_operator)
  have B_type: "Prop # \<Gamma> \<turnstile> ?B : Prop"
    using typed_pp_pure[OF E_type] Zs_type BE_type
    by (intro has_type.Conj has_type.Eq)
  have index_type: "Prop # \<Gamma> \<turnstile> ?index : Prop"
    using E_type As_type by (intro has_type.Conj has_type.Imp)
  have collision_type:
    "Prop # \<Gamma> \<turnstile> ?collision : pp_unary_ty"
    using As_type E_type by (rule typed_pp_T6_WI_collision_operator)
  have left_op_type:
    "Prop # \<Gamma> \<turnstile> pp_compose ?Ys ?Zs : pp_unary_ty"
    using Ys_type Zs_type by (rule typed_pp_compose)
  have left_type: "Prop # \<Gamma> \<turnstile> ?left : Prop"
    using left_op_type ps_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have right_type: "Prop # \<Gamma> \<turnstile> ?right : Prop"
    using collision_type ps_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have d_B:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?B"
    using B_type by (intro CEV_axiom_from.Assumption) simp
  have d_H:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Hs"
    using Hs_type by (intro CEV_axiom_from.Assumption) simp
  have pure_E:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ?E"
    using d_B by (rule CEV_axiom_from_conj_left)
  have Z_eq_BE:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?Zs ?BE"
    using d_B by (rule CEV_axiom_from_conj_right)
  have pure_A:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ?As"
    using d_H
    by simp (rule CEV_axiom_from_conj_left)
  have rhs:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (pp_T6_WI_a (shift ?rs) (Var 0)
            \<longleftrightarrow>\<^sub>o Neg (shift ?As)))"
    using d_H
    by simp (rule CEV_axiom_from_conj_right)
  have pure_index:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ?index"
    using core E_type As_type pure_E pure_A
    by (rule CEV_axiom_biconditional_pure_from)
  have d_clause:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?clause"
    using rs_type As_type index_type rhs pure_index
    by (rule CEV_axiom_T6_WI_rhs_instance)
  have collision_equiv:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (Neg ?right \<longleftrightarrow>\<^sub>o ?clause)"
    using rs_type As_type E_type
    by (rule CEV_axiom_T6_WI_collision_neg_equiv)
  have clause_to_collision:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?clause (Neg ?right)"
    using collision_equiv by (rule CEV_axiom_from_conj_right)
  have not_right:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?right"
    using d_clause clause_to_collision by (rule CEV_axiom_from.MP)
  have Zp_type: "Prop # \<Gamma> \<turnstile> App ?Zs ?ps : Prop"
    using Zs_type ps_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have BEp_type: "Prop # \<Gamma> \<turnstile> App ?BE ?ps : Prop"
    using BE_type ps_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have YZp_type:
    "Prop # \<Gamma> \<turnstile> App ?Ys (App ?Zs ?ps) : Prop"
    using Ys_type Zp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have YBEp_type:
    "Prop # \<Gamma> \<turnstile> App ?Ys (App ?BE ?ps) : Prop"
    using Ys_type BEp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have left_beta:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?left (App ?Ys (App ?Zs ?ps))"
    using CEV_pp_compose_apply_eq[OF Ys_type Zs_type ps_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have arg_eq:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?Zs ?ps) (App ?BE ?ps)"
    using Zs_type BE_type ps_type Z_eq_BE
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have Y_arg_eq:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop
        (App ?Ys (App ?Zs ?ps))
        (App ?Ys (App ?BE ?ps))"
    using Ys_type Zp_type BEp_type arg_eq
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have right_beta:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?right (App ?Ys (App ?BE ?ps))"
    unfolding pp_T6_WI_collision_operator_def
    using CEV_pp_compose_apply_eq[OF Ys_type BE_type ps_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have right_beta_sym:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?Ys (App ?BE ?ps)) ?right"
    using right_type YBEp_type right_beta
    by (rule CEV_axiom_from_eq_sym)
  have first:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?left (App ?Ys (App ?BE ?ps))"
    using left_type YZp_type YBEp_type left_beta Y_arg_eq
    by (rule CEV_axiom_from_eq_trans)
  have left_right:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?left ?right"
    using left_type YBEp_type right_type first right_beta_sym
    by (rule CEV_axiom_from_eq_trans)
  have neg_eq:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?left) (Neg ?right)"
    using left_type right_type left_right
    by (rule CEV_axiom_from_T5_neg_cong)
  have neg_eq_sym:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?right) (Neg ?left)"
    using has_type.Neg[OF left_type] has_type.Neg[OF right_type]
      neg_eq
    by (rule CEV_axiom_from_eq_sym)
  have not_left:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?left"
    using has_type.Neg[OF right_type] has_type.Neg[OF left_type]
      not_right neg_eq_sym
    by (rule CEV_axiom_from_eq_prop_elim)
  have under_B:
    "Prop # \<Gamma> ; T ; {?B} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?Hs (Neg ?left)"
  proof (rule CEV_axiom_from_deduction)
    show "Prop # \<Gamma> \<turnstile> ?Hs : Prop"
      by (rule Hs_type)
    show "Prop # \<Gamma> ; T ; insert ?Hs {?B}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?left"
      by (rule not_left)
  qed
  have bound:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?B (shift ?Q)"
  proof -
    have raw:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?B (Imp ?Hs (Neg ?left))"
      using B_type under_B by (rule CEV_axiom_from_singleton_imp)
    show ?thesis
      using raw by simp
  qed
  have group_to_Q:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_group_member Z) ?Q"
    using WI_in Z_type Q_type bound
    by (rule CEV_axiom_WI_group_elim)
  have reorder:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Imp (pp_group_member Z) (Imp ?H ?R))
        (Imp ?H (Imp (pp_group_member Z) ?R))"
  proof (rule CEV_axiom_proves.Base, rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp (pp_group_member Z) (Imp ?H ?R))
        (Imp ?H (Imp (pp_group_member Z) ?R)))"
    proof (unfold prop_tautology_def, intro conjI)
      show "\<Gamma> \<turnstile>
        Imp
          (Imp (pp_group_member Z) (Imp ?H ?R))
          (Imp ?H (Imp (pp_group_member Z) ?R)) : Prop"
        using typed_pp_group_member[OF Z_type] H_type R_type
        by (intro has_type.Imp)
    next
      show "\<forall>v. prop_eval v
        (Imp
          (Imp (pp_group_member Z) (Imp ?H ?R))
          (Imp ?H (Imp (pp_group_member Z) ?R)))"
        apply (simp only: prop_eval.simps)
        by blast
    qed
  qed
  show ?thesis
    using group_to_Q reorder by (rule CEV_axiom_proves.MP)
qed

theorem CEV_T6_WI_same_kind_refutes:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and WI_in: "pp_WI \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure Prop A)
        (Forall Prop
          (Imp
            (pp_pure Prop (Var 0))
            (pp_T6_WI_a (shift r) (Var 0)
              \<longleftrightarrow>\<^sub>o Neg (shift A)))))
      (Imp
        (pp_same_kind X (pp_T6_WI_comparison_operator A))
        (Neg
          (App X (pp_T6_WI_diagonal_point r A))))"
proof -
  let ?Y = "pp_T6_WI_comparison_operator A"
  let ?p = "pp_T6_WI_diagonal_point r A"
  let ?R = "Neg (App X ?p)"
  let ?H =
    "Conj
      (pp_pure Prop A)
      (Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (pp_T6_WI_a (shift r) (Var 0)
            \<longleftrightarrow>\<^sub>o Neg (shift A))))"
  let ?Q = "Imp ?H ?R"
  have Y_type: "\<Gamma> \<turnstile> ?Y : pp_unary_ty"
    using A_type by (rule typed_pp_T6_WI_comparison_operator)
  have p_type: "\<Gamma> \<turnstile> ?p : Prop"
    using r_type A_type by (rule typed_pp_T6_WI_diagonal_point)
  have Xp_type: "\<Gamma> \<turnstile> App X ?p : Prop"
    using X_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using Xp_type by (rule has_type.Neg)
  have rhs_type:
    "\<Gamma> \<turnstile>
      Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (pp_T6_WI_a (shift r) (Var 0)
            \<longleftrightarrow>\<^sub>o Neg (shift A))) : Prop"
  proof -
    have rs_type: "Prop # \<Gamma> \<turnstile> shift r : Prop"
      using r_type by (rule typed_shift_ctx)
    have As_type: "Prop # \<Gamma> \<turnstile> shift A : Prop"
      using A_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    show ?thesis
      using typed_pp_pure[OF v_type]
        typed_pp_T6_WI_a[OF rs_type v_type] As_type
      by (intro has_type.Forall has_type.Imp
          has_type.Conj has_type.Neg)
  qed
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_pure[OF A_type] rhs_type
    by (rule has_type.Conj)
  have Q_type: "\<Gamma> \<turnstile> ?Q : Prop"
    using H_type R_type by (rule has_type.Imp)

  let ?Z = "Var 0"
  let ?Xs = "shift X"
  let ?Ys = "pp_T6_WI_comparison_operator (shift A)"
  let ?rs = "shift r"
  let ?As = "shift A"
  let ?ps = "pp_T6_WI_diagonal_point ?rs ?As"
  let ?Hs = "shift ?H"
  let ?GZ = "pp_group_member ?Z"
  let ?YZ = "pp_compose ?Ys ?Z"
  let ?E = "Eq pp_unary_ty ?Xs ?YZ"
  let ?B = "Conj ?GZ ?E"
  let ?left = "App ?Xs ?ps"
  let ?right = "App ?YZ ?ps"
  let ?S = "insert ?Hs {?B}"
  have Z_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Z : pp_unary_ty"
    by (rule typed_var0)
  have Xs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Xs : pp_unary_ty"
    using X_type by (rule typed_shift_ctx)
  have rs_type: "pp_unary_ty # \<Gamma> \<turnstile> ?rs : Prop"
    using r_type by (rule typed_shift_ctx)
  have As_type: "pp_unary_ty # \<Gamma> \<turnstile> ?As : Prop"
    using A_type by (rule typed_shift_ctx)
  have Ys_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Ys : pp_unary_ty"
    using As_type by (rule typed_pp_T6_WI_comparison_operator)
  have ps_type: "pp_unary_ty # \<Gamma> \<turnstile> ?ps : Prop"
    using rs_type As_type by (rule typed_pp_T6_WI_diagonal_point)
  have Hs_type: "pp_unary_ty # \<Gamma> \<turnstile> ?Hs : Prop"
    using H_type by (rule typed_shift_ctx)
  have GZ_type: "pp_unary_ty # \<Gamma> \<turnstile> ?GZ : Prop"
    using Z_type by (rule typed_pp_group_member)
  have YZ_type: "pp_unary_ty # \<Gamma> \<turnstile> ?YZ : pp_unary_ty"
    using Ys_type Z_type by (rule typed_pp_compose)
  have E_type: "pp_unary_ty # \<Gamma> \<turnstile> ?E : Prop"
    using Xs_type YZ_type by (rule has_type.Eq)
  have B_type: "pp_unary_ty # \<Gamma> \<turnstile> ?B : Prop"
    using GZ_type E_type by (rule has_type.Conj)
  have left_type: "pp_unary_ty # \<Gamma> \<turnstile> ?left : Prop"
    using Xs_type ps_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have right_type: "pp_unary_ty # \<Gamma> \<turnstile> ?right : Prop"
    using YZ_type ps_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have d_B:
    "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?B"
    using B_type by (intro CEV_axiom_from.Assumption) simp
  have d_H:
    "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Hs"
    using Hs_type by (intro CEV_axiom_from.Assumption) simp
  have d_GZ:
    "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?GZ"
    using d_B by (rule CEV_axiom_from_conj_left)
  have d_E:
    "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using d_B by (rule CEV_axiom_from_conj_right)
  have group_rule:
    "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?Hs (Imp ?GZ (Neg ?right))"
    using CEV_T6_WI_group_collision_refutes[
      OF core WI_in rs_type As_type Z_type]
    by simp (rule CEV_axiom_from.Theorem)
  have group_step:
    "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?GZ (Neg ?right)"
    using d_H group_rule by (rule CEV_axiom_from.MP)
  have not_right:
    "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg ?right"
    using d_GZ group_step by (rule CEV_axiom_from.MP)
  have app_eq:
    "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?left ?right"
    using Xs_type YZ_type ps_type d_E
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have neg_eq:
    "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?left) (Neg ?right)"
    using left_type right_type app_eq
    by (rule CEV_axiom_from_T5_neg_cong)
  have neg_eq_sym:
    "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?right) (Neg ?left)"
    using has_type.Neg[OF left_type] has_type.Neg[OF right_type]
      neg_eq
    by (rule CEV_axiom_from_eq_sym)
  have not_left:
    "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg ?left"
    using has_type.Neg[OF right_type] has_type.Neg[OF left_type]
      not_right neg_eq_sym
    by (rule CEV_axiom_from_eq_prop_elim)
  have under_B:
    "pp_unary_ty # \<Gamma> ; T ; {?B}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?Hs (Neg ?left)"
  proof (rule CEV_axiom_from_deduction)
    show "pp_unary_ty # \<Gamma> \<turnstile> ?Hs : Prop"
      by (rule Hs_type)
    show "pp_unary_ty # \<Gamma> ; T ; insert ?Hs {?B}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?left"
      by (rule not_left)
  qed
  have bound:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?B (shift ?Q)"
  proof -
    have raw:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?B (Imp ?Hs (Neg ?left))"
      using B_type under_B by (rule CEV_axiom_from_singleton_imp)
    show ?thesis
      using raw by simp
  qed
  have same_to_Q:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_same_kind X ?Y) ?Q"
  proof (rule CEV_axiom_same_kind_elim[
      OF X_type Y_type Q_type])
    show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Conj
          (pp_group_member (Var 0))
          (Eq pp_unary_ty
            (shift X)
            (pp_compose (shift ?Y) (Var 0))))
        (shift ?Q)"
      using bound by simp
  qed
  have reorder:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Imp (pp_same_kind X ?Y) (Imp ?H ?R))
        (Imp ?H (Imp (pp_same_kind X ?Y) ?R))"
  proof (rule CEV_axiom_proves.Base, rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp (pp_same_kind X ?Y) (Imp ?H ?R))
        (Imp ?H (Imp (pp_same_kind X ?Y) ?R)))"
    proof (unfold prop_tautology_def, intro conjI)
      show "\<Gamma> \<turnstile>
        Imp
          (Imp (pp_same_kind X ?Y) (Imp ?H ?R))
          (Imp ?H (Imp (pp_same_kind X ?Y) ?R)) : Prop"
        using typed_pp_same_kind[OF X_type Y_type] H_type R_type
        by (intro has_type.Imp)
    next
      show "\<forall>v. prop_eval v
        (Imp
          (Imp (pp_same_kind X ?Y) (Imp ?H ?R))
          (Imp ?H (Imp (pp_same_kind X ?Y) ?R)))"
        apply (simp only: prop_eval.simps)
        by blast
    qed
  qed
  show ?thesis
    using same_to_Q reorder by (rule CEV_axiom_proves.MP)
qed

theorem CEV_T6_WI_master_reverse:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and WI_in: "pp_WI \<in> T"
    and L2_in: "pp_L2 \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_fun_prime r)
        (Conj
          (pp_pure Prop A)
          (Forall Prop
            (Imp
              (pp_pure Prop (Var 0))
              (pp_T6_WI_a (shift r) (Var 0)
                \<longleftrightarrow>\<^sub>o Neg (shift A))))))
      (pp_T6_WI_a r A)"
proof -
  let ?rhs =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (pp_T6_WI_a (shift r) (Var 0)
          \<longleftrightarrow>\<^sub>o Neg (shift A)))"
  let ?H =
    "Conj
      (pp_fun_prime r)
      (Conj
        (pp_pure Prop A)
        ?rhs)"
  let ?p = "pp_T6_WI_diagonal_point r A"
  let ?aA = "pp_T6_WI_a r A"
  have rhs_type: "\<Gamma> \<turnstile> ?rhs : Prop"
  proof -
    have rs_type: "Prop # \<Gamma> \<turnstile> shift r : Prop"
      using r_type by (rule typed_shift_ctx)
    have As_type: "Prop # \<Gamma> \<turnstile> shift A : Prop"
      using A_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    show ?thesis
      using typed_pp_pure[OF v_type]
        typed_pp_T6_WI_a[OF rs_type v_type] As_type
      by (intro has_type.Forall has_type.Imp
          has_type.Conj has_type.Neg)
  qed
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_fun_prime[OF r_type]
      typed_pp_pure[OF A_type] rhs_type
    by (intro has_type.Conj)
  have p_type: "\<Gamma> \<turnstile> ?p : Prop"
    using r_type A_type by (rule typed_pp_T6_WI_diagonal_point)
  have aA_type: "\<Gamma> \<turnstile> ?aA : Prop"
    using r_type A_type by (rule typed_pp_T6_WI_a)

  let ?X = "Var 1"
  let ?q = "Var 0"
  let ?r2 = "shift (shift r)"
  let ?A2 = "shift (shift A)"
  let ?p2 = "pp_T6_WI_diagonal_point ?r2 ?A2"
  let ?Y2 = "pp_T6_WI_comparison_operator ?A2"
  let ?H2 = "shift (shift ?H)"
  let ?PX = "pp_pure pp_unary_ty ?X"
  let ?Fq = "pp_fun_prime ?q"
  let ?decomp = "Eq Prop ?p2 (App ?X ?q)"
  let ?P = "Conj ?PX (Conj ?Fq ?decomp)"
  let ?R = "Neg (App ?X ?p2)"
  let ?S = "insert ?P {?H2}"
  have X_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?X : pp_unary_ty"
    by (rule has_type.Var) (simp add: lookup_def)
  have q_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?q : Prop"
    by (rule typed_var0)
  have r2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?r2 : Prop"
    using r_type by (rule typed_shift_ctx[OF typed_shift_ctx])
  have A2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?A2 : Prop"
    using A_type by (rule typed_shift_ctx[OF typed_shift_ctx])
  have p2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?p2 : Prop"
    using r2_type A2_type by (rule typed_pp_T6_WI_diagonal_point)
  have Y2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?Y2 : pp_unary_ty"
    using A2_type by (rule typed_pp_T6_WI_comparison_operator)
  have H2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?H2 : Prop"
    using H_type by (rule typed_shift_ctx[OF typed_shift_ctx])
  have Xq_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> App ?X ?q : Prop"
    using X_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xp_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> App ?X ?p2 : Prop"
    using X_type p2_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have P_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_pure[OF X_type]
      typed_pp_fun_prime[OF q_type] p2_type Xq_type
    by (intro has_type.Conj has_type.Eq)
  have R_type: "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?R : Prop"
    using Xp_type by (rule has_type.Neg)
  have d_H:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H2"
    using H2_type by (intro CEV_axiom_from.Assumption) simp
  have d_P:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have fun_r:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime ?r2"
    using d_H
    by simp (rule CEV_axiom_from_conj_left)
  have d_Htail:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Conj
          (pp_pure Prop ?A2)
          (Forall Prop
            (Imp
              (pp_pure Prop (Var 0))
              (pp_T6_WI_a (shift ?r2) (Var 0)
                \<longleftrightarrow>\<^sub>o Neg (shift ?A2))))"
    using d_H
    by simp (rule CEV_axiom_from_conj_right)
  have pure_X:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PX"
    using d_P by (rule CEV_axiom_from_conj_left)
  have d_Ptail:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj ?Fq ?decomp"
    using d_P by (rule CEV_axiom_from_conj_right)
  have fun_q:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Fq"
    using d_Ptail by (rule CEV_axiom_from_conj_left)
  have decomposition:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?decomp"
    using d_Ptail by (rule CEV_axiom_from_conj_right)
  have pure_A:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop ?A2"
    using d_Htail by (rule CEV_axiom_from_conj_left)
  have pure_Y:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty ?Y2"
    using core A2_type pure_A
    by (rule CEV_axiom_T6_WI_comparison_operator_pure_from)
  have Yr_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> App ?Y2 ?r2 : Prop"
    using Y2_type r2_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Y_beta:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?Y2 ?r2) ?p2"
    unfolding pp_T6_WI_comparison_operator_def
      pp_T6_WI_diagonal_point_def
    using CEV_pp_compose_apply_eq[
      OF typed_pp_biconditional_operator[OF A2_type]
        typed_pp_T6_liar r2_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have Xq_p:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?X ?q) ?p2"
    using p2_type Xq_type decomposition
    by (rule CEV_axiom_from_eq_sym)
  have p_Yr:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?p2 (App ?Y2 ?r2)"
    using Yr_type p2_type Y_beta
    by (rule CEV_axiom_from_eq_sym)
  have collision_eq:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App ?X ?q) (App ?Y2 ?r2)"
    using Xq_type p2_type Yr_type Xq_p p_Yr
    by (rule CEV_axiom_from_eq_trans)
  have l2_prem:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Conj
          (pp_pure pp_unary_ty ?X)
          (Conj
            (pp_pure pp_unary_ty ?Y2)
            (Conj
              (pp_fun_prime ?q)
              (Conj
                (pp_fun_prime ?r2)
                (Eq Prop (App ?X ?q) (App ?Y2 ?r2)))))"
    using pure_X
      CEV_axiom_from_conj_intro[
        OF pure_Y
          CEV_axiom_from_conj_intro[
            OF fun_q
              CEV_axiom_from_conj_intro[
                OF fun_r collision_eq]]]
    by (rule CEV_axiom_from_conj_intro)
  have l2_rule:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp
          (Conj
            (pp_pure pp_unary_ty ?X)
            (Conj
              (pp_pure pp_unary_ty ?Y2)
              (Conj
                (pp_fun_prime ?q)
                (Conj
                  (pp_fun_prime ?r2)
                  (Eq Prop (App ?X ?q) (App ?Y2 ?r2))))))
          (pp_same_kind ?X ?Y2)"
    using CEV_axiom_L2_instance[
      OF L2_in X_type Y2_type q_type r2_type]
    by (rule CEV_axiom_from.Theorem)
  have same:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_same_kind ?X ?Y2"
    using l2_prem l2_rule by (rule CEV_axiom_from.MP)
  have refute_rule:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp
          (Conj
            (pp_pure Prop ?A2)
            (Forall Prop
              (Imp
                (pp_pure Prop (Var 0))
                (pp_T6_WI_a (shift ?r2) (Var 0)
                  \<longleftrightarrow>\<^sub>o Neg (shift ?A2)))))
          (Imp (pp_same_kind ?X ?Y2) ?R)"
    using CEV_T6_WI_same_kind_refutes[
      OF core WI_in r2_type A2_type X_type]
    by (rule CEV_axiom_from.Theorem)
  have refute_step:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp (pp_same_kind ?X ?Y2) ?R"
    using d_Htail refute_rule by (rule CEV_axiom_from.MP)
  have d_R:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
    using same refute_step by (rule CEV_axiom_from.MP)
  have under_H2:
    "Prop # pp_unary_ty # \<Gamma> ; T ; {?H2}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?P ?R"
  proof (rule CEV_axiom_from_deduction)
    show "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?P : Prop"
      by (rule P_type)
    show "Prop # pp_unary_ty # \<Gamma> ; T ; insert ?P {?H2}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
      by (rule d_R)
  qed
  have deepest:
    "Prop # pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?H2 (Imp ?P ?R)"
    using H2_type under_H2 by (rule CEV_axiom_from_singleton_imp)

  let ?H1 = "shift ?H"
  have H1_type: "pp_unary_ty # \<Gamma> \<turnstile> ?H1 : Prop"
    using H_type by (rule typed_shift_ctx)
  have matrix_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> Imp ?P ?R : Prop"
    using P_type R_type by (rule has_type.Imp)
  have inner:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?H1 (Forall Prop (Imp ?P ?R))"
  proof (rule CEV_axiom_proves.Gen)
    show "pp_unary_ty # \<Gamma> \<turnstile> ?H1 : Prop"
      by (rule H1_type)
    show "Prop # pp_unary_ty # \<Gamma> \<turnstile> Imp ?P ?R : Prop"
      by (rule matrix_type)
    show "Prop # pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?H1) (Imp ?P ?R)"
      using deepest by simp
  qed
  have forall_q_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      Forall Prop (Imp ?P ?R) : Prop"
    using matrix_type by (rule has_type.Forall)
  have outer:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?H
        (Forall pp_unary_ty
          (Forall Prop (Imp ?P ?R)))"
  proof (rule CEV_axiom_proves.Gen)
    show "\<Gamma> \<turnstile> ?H : Prop"
      by (rule H_type)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      Forall Prop (Imp ?P ?R) : Prop"
      by (rule forall_q_type)
    show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?H) (Forall Prop (Imp ?P ?R))"
      by (rule inner)
  qed
  have liar_rule:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?H (pp_T5_liar_at ?p)"
    using outer
    by (simp add: pp_T5_liar_at_explicit
      shift_shift_eq_shift_by_2)
  let ?S0 = "{?H}"
  have d_H0:
    "\<Gamma> ; T ; ?S0 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using H_type by (intro CEV_axiom_from.Assumption) simp
  have d_liar_at:
    "\<Gamma> ; T ; ?S0 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_T5_liar_at ?p"
    using d_H0 CEV_axiom_from.Theorem[OF liar_rule]
    by (rule CEV_axiom_from.MP)
  have a_eq:
    "\<Gamma> ; T ; ?S0 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?aA (pp_T5_liar_at ?p)"
    unfolding pp_T6_WI_a_as_liar_at_point
    using CEV_pp_T6_liar_apply_eq[OF p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have liar_eq_a:
    "\<Gamma> ; T ; ?S0 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (pp_T5_liar_at ?p) ?aA"
    using aA_type typed_pp_T5_liar_at[OF p_type] a_eq
    by (rule CEV_axiom_from_eq_sym)
  have d_aA:
    "\<Gamma> ; T ; ?S0 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?aA"
    using typed_pp_T5_liar_at[OF p_type] aA_type
      d_liar_at liar_eq_a
    by (rule CEV_axiom_from_eq_prop_elim)
  show ?thesis
    using H_type d_aA by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_T6_WI_master_at_direct:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and WI_in: "pp_WI \<in> T"
    and L2_in: "pp_L2 \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj (pp_fun_prime r) (pp_pure Prop A))
      (pp_T6_WI_a r A
        \<longleftrightarrow>\<^sub>o
        Forall Prop
          (Imp
            (pp_pure Prop (Var 0))
            (pp_T6_WI_a (shift r) (Var 0)
              \<longleftrightarrow>\<^sub>o Neg (shift A))))"
proof -
  let ?F = "pp_fun_prime r"
  let ?PA = "pp_pure Prop A"
  let ?aA = "pp_T6_WI_a r A"
  let ?R =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (pp_T6_WI_a (shift r) (Var 0)
          \<longleftrightarrow>\<^sub>o Neg (shift A)))"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have PA_type: "\<Gamma> \<turnstile> ?PA : Prop"
    using A_type by (rule typed_pp_pure)
  have aA_type: "\<Gamma> \<turnstile> ?aA : Prop"
    using r_type A_type by (rule typed_pp_T6_WI_a)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
  proof -
    have rs_type: "Prop # \<Gamma> \<turnstile> shift r : Prop"
      using r_type by (rule typed_shift_ctx)
    have As_type: "Prop # \<Gamma> \<turnstile> shift A : Prop"
      using A_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    show ?thesis
      using typed_pp_pure[OF v_type]
        typed_pp_T6_WI_a[OF rs_type v_type] As_type
      by (intro has_type.Forall has_type.Imp
          has_type.Conj has_type.Neg)
  qed
  have forward:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj ?F (Conj ?PA ?aA)) ?R"
    using core r_type A_type by (rule CEV_T6_WI_master_forward)
  have reverse:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj ?F (Conj ?PA ?R)) ?aA"
    using core WI_in L2_in r_type A_type
    by (rule CEV_T6_WI_master_reverse)
  have combine:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Imp (Conj ?F (Conj ?PA ?aA)) ?R)
        (Imp
          (Imp (Conj ?F (Conj ?PA ?R)) ?aA)
          (Imp (Conj ?F ?PA) (?aA \<longleftrightarrow>\<^sub>o ?R)))"
  proof (rule CEV_axiom_proves.Base, rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp (Conj ?F (Conj ?PA ?aA)) ?R)
        (Imp
          (Imp (Conj ?F (Conj ?PA ?R)) ?aA)
          (Imp (Conj ?F ?PA) (?aA \<longleftrightarrow>\<^sub>o ?R))))"
    proof (unfold prop_tautology_def, intro conjI)
      show "\<Gamma> \<turnstile>
        Imp
          (Imp (Conj ?F (Conj ?PA ?aA)) ?R)
          (Imp
            (Imp (Conj ?F (Conj ?PA ?R)) ?aA)
            (Imp (Conj ?F ?PA)
              (?aA \<longleftrightarrow>\<^sub>o ?R))) : Prop"
        using F_type PA_type aA_type R_type
        by (intro has_type.Imp has_type.Conj)
    next
      show "\<forall>v. prop_eval v
        (Imp
          (Imp (Conj ?F (Conj ?PA ?aA)) ?R)
          (Imp
            (Imp (Conj ?F (Conj ?PA ?R)) ?aA)
            (Imp (Conj ?F ?PA)
              (?aA \<longleftrightarrow>\<^sub>o ?R))))"
        apply (simp only: prop_eval.simps)
        by blast
    qed
  qed
  have step:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Imp (Conj ?F (Conj ?PA ?R)) ?aA)
        (Imp (Conj ?F ?PA) (?aA \<longleftrightarrow>\<^sub>o ?R))"
    using forward combine by (rule CEV_axiom_proves.MP)
  show ?thesis
    using reverse step by (rule CEV_axiom_proves.MP)
qed

theorem CEV_T6_WI_master_family_direct:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and WI_in: "pp_WI \<in> T"
    and L2_in: "pp_L2 \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (pp_T6_WI_a (shift r) (Var 0)
            \<longleftrightarrow>\<^sub>o
            Forall Prop
              (Imp
                (pp_pure Prop (Var 0))
                (pp_T6_WI_a
                    (shift (shift r)) (Var 0)
                  \<longleftrightarrow>\<^sub>o
                  Neg (Var 1))))))"
proof -
  let ?F = "pp_fun_prime r"
  let ?A = "Var 0"
  let ?rs = "shift r"
  let ?Fs = "pp_fun_prime ?rs"
  let ?PA = "pp_pure Prop ?A"
  let ?aA = "pp_T6_WI_a ?rs ?A"
  let ?R =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (pp_T6_WI_a (shift ?rs) (Var 0)
          \<longleftrightarrow>\<^sub>o Neg (shift ?A)))"
  let ?Q = "Imp ?PA (?aA \<longleftrightarrow>\<^sub>o ?R)"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have rs_type: "Prop # \<Gamma> \<turnstile> ?rs : Prop"
    using r_type by (rule typed_shift_ctx)
  have A_type: "Prop # \<Gamma> \<turnstile> ?A : Prop"
    by (rule typed_var0)
  have PA_type: "Prop # \<Gamma> \<turnstile> ?PA : Prop"
    using A_type by (rule typed_pp_pure)
  have aA_type: "Prop # \<Gamma> \<turnstile> ?aA : Prop"
    using rs_type A_type by (rule typed_pp_T6_WI_a)
  have R_type: "Prop # \<Gamma> \<turnstile> ?R : Prop"
  proof -
    have r2_type:
      "Prop # Prop # \<Gamma> \<turnstile> shift ?rs : Prop"
      using rs_type by (rule typed_shift_ctx)
    have As_type:
      "Prop # Prop # \<Gamma> \<turnstile> shift ?A : Prop"
      using A_type by (rule typed_shift_ctx)
    have v_type:
      "Prop # Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    show ?thesis
      using typed_pp_pure[OF v_type]
        typed_pp_T6_WI_a[OF r2_type v_type] As_type
      by (intro has_type.Forall has_type.Imp
          has_type.Conj has_type.Neg)
  qed
  have Q_type: "Prop # \<Gamma> \<turnstile> ?Q : Prop"
    using PA_type aA_type R_type
    by (intro has_type.Imp has_type.Conj)
  have at:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj ?Fs ?PA) (?aA \<longleftrightarrow>\<^sub>o ?R)"
    using core WI_in L2_in rs_type A_type
    by (rule CEV_T6_WI_master_at_direct)
  have curry:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Imp (Conj ?Fs ?PA) (?aA \<longleftrightarrow>\<^sub>o ?R))
        (Imp ?Fs ?Q)"
  proof (rule CEV_axiom_proves.Base, rule CEV_prop_tautology)
    show "prop_tautology (Prop # \<Gamma>)
      (Imp
        (Imp (Conj ?Fs ?PA) (?aA \<longleftrightarrow>\<^sub>o ?R))
        (Imp ?Fs ?Q))"
    proof (unfold prop_tautology_def, intro conjI)
      show "Prop # \<Gamma> \<turnstile>
        Imp
          (Imp (Conj ?Fs ?PA)
            (?aA \<longleftrightarrow>\<^sub>o ?R))
          (Imp ?Fs ?Q) : Prop"
        using typed_pp_fun_prime[OF rs_type]
          PA_type aA_type R_type
        by (intro has_type.Imp has_type.Conj)
    next
      show "\<forall>v. prop_eval v
        (Imp
          (Imp (Conj ?Fs ?PA)
            (?aA \<longleftrightarrow>\<^sub>o ?R))
          (Imp ?Fs ?Q))"
        apply (simp only: prop_eval.simps)
        by blast
    qed
  qed
  have body:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?Fs ?Q"
    using at curry by (rule CEV_axiom_proves.MP)
  have shifted_body:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?F) ?Q"
    using body by simp
  have generalized:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (Forall Prop ?Q)"
    using F_type Q_type shifted_body
    by (rule CEV_axiom_proves.Gen)
  show ?thesis
    using generalized by (simp add: shift_def)
qed

theorem CEV_T6_WI_rhs_operator_equiv:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    ((Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (pp_T6_WI_a (shift r) (Var 0)
            \<longleftrightarrow>\<^sub>o Neg (shift A))))
      \<longleftrightarrow>\<^sub>o
      (Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (App
              (shift (pp_T6_WI_a_operator r))
              (Var 0)
            \<longleftrightarrow>\<^sub>o Neg (shift A)))))"
proof -
  let ?a = "pp_T6_WI_a_operator r"
  let ?DR =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (pp_T6_WI_a (shift r) (Var 0)
          \<longleftrightarrow>\<^sub>o Neg (shift A)))"
  let ?OR =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (App (shift ?a) (Var 0)
          \<longleftrightarrow>\<^sub>o Neg (shift A)))"
  have a_type: "\<Gamma> \<turnstile> ?a : Prop \<rightarrow>\<^sub>o Prop"
    using r_type by (rule typed_pp_T6_WI_a_operator)
  have DR_type: "\<Gamma> \<turnstile> ?DR : Prop"
  proof -
    have rs_type: "Prop # \<Gamma> \<turnstile> shift r : Prop"
      using r_type by (rule typed_shift_ctx)
    have As_type: "Prop # \<Gamma> \<turnstile> shift A : Prop"
      using A_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    show ?thesis
      using typed_pp_pure[OF v_type]
        typed_pp_T6_WI_a[OF rs_type v_type] As_type
      by (intro has_type.Forall has_type.Imp
          has_type.Conj has_type.Neg)
  qed
  have OR_type: "\<Gamma> \<turnstile> ?OR : Prop"
  proof -
    have as_type:
      "Prop # \<Gamma> \<turnstile> shift ?a : Prop \<rightarrow>\<^sub>o Prop"
      using a_type by (rule typed_shift_ctx)
    have As_type: "Prop # \<Gamma> \<turnstile> shift A : Prop"
      using A_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    show ?thesis
      using typed_pp_pure[OF v_type]
        has_type.App[OF as_type v_type] As_type
      by (intro has_type.Forall has_type.Imp
          has_type.Conj has_type.Neg)
  qed

  let ?C = "Var 0"
  let ?rs = "shift r"
  let ?As = "shift A"
  let ?as = "shift ?a"
  let ?PC = "pp_pure Prop ?C"
  let ?dC = "pp_T6_WI_a ?rs ?C"
  let ?oC = "App ?as ?C"
  let ?N = "Neg ?As"
  let ?DC = "?dC \<longleftrightarrow>\<^sub>o ?N"
  let ?OC = "?oC \<longleftrightarrow>\<^sub>o ?N"
  have C_type: "Prop # \<Gamma> \<turnstile> ?C : Prop"
    by (rule typed_var0)
  have rs_type: "Prop # \<Gamma> \<turnstile> ?rs : Prop"
    using r_type by (rule typed_shift_ctx)
  have As_type: "Prop # \<Gamma> \<turnstile> ?As : Prop"
    using A_type by (rule typed_shift_ctx)
  have as_type:
    "Prop # \<Gamma> \<turnstile> ?as : Prop \<rightarrow>\<^sub>o Prop"
    using a_type by (rule typed_shift_ctx)
  have PC_type: "Prop # \<Gamma> \<turnstile> ?PC : Prop"
    using C_type by (rule typed_pp_pure)
  have dC_type: "Prop # \<Gamma> \<turnstile> ?dC : Prop"
    using rs_type C_type by (rule typed_pp_T6_WI_a)
  have oC_type: "Prop # \<Gamma> \<turnstile> ?oC : Prop"
    using as_type C_type by (rule has_type.App)
  have N_type: "Prop # \<Gamma> \<turnstile> ?N : Prop"
    using As_type by (rule has_type.Neg)
  have DC_type: "Prop # \<Gamma> \<turnstile> ?DC : Prop"
    using dC_type N_type by (intro has_type.Conj has_type.Imp)
  have OC_type: "Prop # \<Gamma> \<turnstile> ?OC : Prop"
    using oC_type N_type by (intro has_type.Conj has_type.Imp)
  have beta_eq:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV Eq Prop ?oC ?dC"
    using CEV_pp_T6_WI_a_operator_apply_eq[
      OF rs_type C_type]
    by simp
  have beta_iff:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (?oC \<longleftrightarrow>\<^sub>o ?dC)"
    using CEV_eq_prop_biconditional[
      OF oC_type dC_type beta_eq]
    by (rule CEV_axiom_proves.Base)
  have clause_cong_rule:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (?oC \<longleftrightarrow>\<^sub>o ?dC)
        (?DC \<longleftrightarrow>\<^sub>o ?OC)"
  proof (rule CEV_axiom_proves.Base, rule CEV_prop_tautology)
    show "prop_tautology (Prop # \<Gamma>)
      (Imp
        (?oC \<longleftrightarrow>\<^sub>o ?dC)
        (?DC \<longleftrightarrow>\<^sub>o ?OC))"
    proof (unfold prop_tautology_def, intro conjI)
      show "Prop # \<Gamma> \<turnstile>
        Imp
          (?oC \<longleftrightarrow>\<^sub>o ?dC)
          (?DC \<longleftrightarrow>\<^sub>o ?OC) : Prop"
        using oC_type dC_type N_type
        by (intro has_type.Imp has_type.Conj)
    next
      show "\<forall>v. prop_eval v
        (Imp
          (?oC \<longleftrightarrow>\<^sub>o ?dC)
          (?DC \<longleftrightarrow>\<^sub>o ?OC))"
        apply (simp only: prop_eval.simps)
        by blast
    qed
  qed
  have clause_equiv:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (?DC \<longleftrightarrow>\<^sub>o ?OC)"
    using beta_iff clause_cong_rule by (rule CEV_axiom_proves.MP)

  have direct_to_operator:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?DR ?OR"
  proof -
    let ?S = "insert ?PC {shift ?DR}"
    have d_DR:
      "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Forall Prop
          (Imp
            (pp_pure Prop (Var 0))
            (pp_T6_WI_a (shift ?rs) (Var 0)
              \<longleftrightarrow>\<^sub>o Neg (shift ?As)))"
    proof -
      have raw:
        "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s shift ?DR"
        using typed_shift_ctx[OF DR_type]
        by (intro CEV_axiom_from.Assumption) simp
      show ?thesis
        using raw by simp
    qed
    have d_PC:
      "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PC"
      using PC_type by (intro CEV_axiom_from.Assumption) simp
    have d_DC:
      "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?DC"
      using rs_type As_type C_type d_DR d_PC
      by (rule CEV_axiom_T6_WI_rhs_instance)
    have DC_to_OC:
      "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?DC ?OC"
    proof -
      have local_clause_equiv:
        "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          (?DC \<longleftrightarrow>\<^sub>o ?OC)"
        using clause_equiv by (rule CEV_axiom_from.Theorem)
      show ?thesis
        using local_clause_equiv by (rule CEV_axiom_from_conj_left)
    qed
    have d_OC:
      "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?OC"
      using d_DC DC_to_OC by (rule CEV_axiom_from.MP)
    have under_DR:
      "Prop # \<Gamma> ; T ; {shift ?DR}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?PC ?OC"
      using PC_type d_OC by (rule CEV_axiom_from_deduction)
    have body:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (shift ?DR) (Imp ?PC ?OC)"
      using typed_shift_ctx[OF DR_type] under_DR
      by (rule CEV_axiom_from_singleton_imp)
    show ?thesis
      using DR_type
        has_type.Imp[OF PC_type OC_type] body
      by (rule CEV_axiom_proves.Gen)
  qed

  have operator_to_direct:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?OR ?DR"
  proof -
    let ?S = "insert ?PC {shift ?OR}"
    have d_OR:
      "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Forall Prop
          (Imp
            (pp_pure Prop (Var 0))
            (App (shift ?as) (Var 0)
              \<longleftrightarrow>\<^sub>o Neg (shift ?As)))"
    proof -
      have raw:
        "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s shift ?OR"
        using typed_shift_ctx[OF OR_type]
        by (intro CEV_axiom_from.Assumption) simp
      have shift_OR:
        "shift ?OR =
          Forall Prop
            (Imp
              (pp_pure Prop (Var 0))
              (App (shift ?as) (Var 0)
                \<longleftrightarrow>\<^sub>o Neg (shift ?As)))"
        using shift_pp_T6_WI_operator_rhs_formula[of ?a A]
        by (simp only:)
      show ?thesis
        using raw by (simp only: shift_OR)
    qed
    have d_PC:
      "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PC"
      using PC_type by (intro CEV_axiom_from.Assumption) simp
    have d_OC:
      "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?OC"
      using as_type As_type C_type d_OR d_PC
      by (rule CEV_axiom_master_rhs_instance)
    have OC_to_DC:
      "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?OC ?DC"
    proof -
      have local_clause_equiv:
        "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          (?DC \<longleftrightarrow>\<^sub>o ?OC)"
        using clause_equiv by (rule CEV_axiom_from.Theorem)
      show ?thesis
        using local_clause_equiv by (rule CEV_axiom_from_conj_right)
    qed
    have d_DC:
      "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?DC"
      using d_OC OC_to_DC by (rule CEV_axiom_from.MP)
    have under_OR:
      "Prop # \<Gamma> ; T ; {shift ?OR}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?PC ?DC"
      using PC_type d_DC by (rule CEV_axiom_from_deduction)
    have body:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (shift ?OR) (Imp ?PC ?DC)"
      using typed_shift_ctx[OF OR_type] under_OR
      by (rule CEV_axiom_from_singleton_imp)
    show ?thesis
      using OR_type
        has_type.Imp[OF PC_type DC_type] body
      by (rule CEV_axiom_proves.Gen)
  qed
  show ?thesis
    using direct_to_operator operator_to_direct
    by (rule CEV_axiom_conj_intro)
qed

theorem CEV_T6_WI_master_at_operator_direct:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and WI_in: "pp_WI \<in> T"
    and L2_in: "pp_L2 \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj (pp_fun_prime r) (pp_pure Prop A))
      (pp_T6_WI_master_at (pp_T6_WI_a_operator r) A)"
proof -
  let ?a = "pp_T6_WI_a_operator r"
  let ?H = "Conj (pp_fun_prime r) (pp_pure Prop A)"
  let ?dA = "pp_T6_WI_a r A"
  let ?oA = "App ?a A"
  let ?DR =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (pp_T6_WI_a (shift r) (Var 0)
          \<longleftrightarrow>\<^sub>o Neg (shift A)))"
  let ?OR =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (App (shift ?a) (Var 0)
          \<longleftrightarrow>\<^sub>o Neg (shift A)))"
  have a_type: "\<Gamma> \<turnstile> ?a : Prop \<rightarrow>\<^sub>o Prop"
    using r_type by (rule typed_pp_T6_WI_a_operator)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_fun_prime[OF r_type]
      typed_pp_pure[OF A_type]
    by (rule has_type.Conj)
  have dA_type: "\<Gamma> \<turnstile> ?dA : Prop"
    using r_type A_type by (rule typed_pp_T6_WI_a)
  have oA_type: "\<Gamma> \<turnstile> ?oA : Prop"
    using a_type A_type by (rule has_type.App)
  have DR_type: "\<Gamma> \<turnstile> ?DR : Prop"
  proof -
    have rs_type: "Prop # \<Gamma> \<turnstile> shift r : Prop"
      using r_type by (rule typed_shift_ctx)
    have As_type: "Prop # \<Gamma> \<turnstile> shift A : Prop"
      using A_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    show ?thesis
      using typed_pp_pure[OF v_type]
        typed_pp_T6_WI_a[OF rs_type v_type] As_type
      by (intro has_type.Forall has_type.Imp
          has_type.Conj has_type.Neg)
  qed
  have OR_type: "\<Gamma> \<turnstile> ?OR : Prop"
  proof -
    have as_type:
      "Prop # \<Gamma> \<turnstile> shift ?a : Prop \<rightarrow>\<^sub>o Prop"
      using a_type by (rule typed_shift_ctx)
    have As_type: "Prop # \<Gamma> \<turnstile> shift A : Prop"
      using A_type by (rule typed_shift_ctx)
    have v_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    show ?thesis
      using typed_pp_pure[OF v_type]
        has_type.App[OF as_type v_type] As_type
      by (intro has_type.Forall has_type.Imp
          has_type.Conj has_type.Neg)
  qed
  have direct:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?H (?dA \<longleftrightarrow>\<^sub>o ?DR)"
    using core WI_in L2_in r_type A_type
    by (rule CEV_T6_WI_master_at_direct)
  have lhs_eq: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop ?oA ?dA"
    using r_type A_type by (rule CEV_pp_T6_WI_a_operator_apply_eq)
  have lhs_equiv:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (?oA \<longleftrightarrow>\<^sub>o ?dA)"
    using CEV_eq_prop_biconditional[
      OF oA_type dA_type lhs_eq]
    by (rule CEV_axiom_proves.Base)
  have rhs_equiv:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (?DR \<longleftrightarrow>\<^sub>o ?OR)"
    using r_type A_type by (rule CEV_T6_WI_rhs_operator_equiv)
  have dA_DR_type:
    "\<Gamma> \<turnstile> (?dA \<longleftrightarrow>\<^sub>o ?DR) : Prop"
    using dA_type DR_type by (intro has_type.Conj has_type.Imp)
  have oA_dA_type:
    "\<Gamma> \<turnstile> (?oA \<longleftrightarrow>\<^sub>o ?dA) : Prop"
    using oA_type dA_type by (intro has_type.Conj has_type.Imp)
  have DR_OR_type:
    "\<Gamma> \<turnstile> (?DR \<longleftrightarrow>\<^sub>o ?OR) : Prop"
    using DR_type OR_type by (intro has_type.Conj has_type.Imp)
  have oA_OR_type:
    "\<Gamma> \<turnstile> (?oA \<longleftrightarrow>\<^sub>o ?OR) : Prop"
    using oA_type OR_type by (intro has_type.Conj has_type.Imp)
  have bridge:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Imp ?H (?dA \<longleftrightarrow>\<^sub>o ?DR))
        (Imp
          (?oA \<longleftrightarrow>\<^sub>o ?dA)
          (Imp
            (?DR \<longleftrightarrow>\<^sub>o ?OR)
            (Imp ?H (?oA \<longleftrightarrow>\<^sub>o ?OR))))"
  proof (rule CEV_axiom_proves.Base, rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp ?H (?dA \<longleftrightarrow>\<^sub>o ?DR))
        (Imp
          (?oA \<longleftrightarrow>\<^sub>o ?dA)
          (Imp
            (?DR \<longleftrightarrow>\<^sub>o ?OR)
            (Imp ?H (?oA \<longleftrightarrow>\<^sub>o ?OR)))))"
    proof (unfold prop_tautology_def, intro conjI)
      show "\<Gamma> \<turnstile>
        Imp
          (Imp ?H (?dA \<longleftrightarrow>\<^sub>o ?DR))
          (Imp
            (?oA \<longleftrightarrow>\<^sub>o ?dA)
            (Imp
              (?DR \<longleftrightarrow>\<^sub>o ?OR)
              (Imp ?H
                (?oA \<longleftrightarrow>\<^sub>o ?OR)))) : Prop"
        using H_type dA_DR_type oA_dA_type DR_OR_type oA_OR_type
        by (intro has_type.Imp)
    next
      show "\<forall>v. prop_eval v
        (Imp
          (Imp ?H (?dA \<longleftrightarrow>\<^sub>o ?DR))
          (Imp
            (?oA \<longleftrightarrow>\<^sub>o ?dA)
            (Imp
              (?DR \<longleftrightarrow>\<^sub>o ?OR)
              (Imp ?H
                (?oA \<longleftrightarrow>\<^sub>o ?OR)))))"
        apply (simp only: prop_eval.simps)
        by blast
    qed
  qed
  have step1:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (?oA \<longleftrightarrow>\<^sub>o ?dA)
        (Imp
          (?DR \<longleftrightarrow>\<^sub>o ?OR)
          (Imp ?H (?oA \<longleftrightarrow>\<^sub>o ?OR)))"
    using direct bridge by (rule CEV_axiom_proves.MP)
  have step2:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (?DR \<longleftrightarrow>\<^sub>o ?OR)
        (Imp ?H (?oA \<longleftrightarrow>\<^sub>o ?OR))"
    using lhs_equiv step1 by (rule CEV_axiom_proves.MP)
  have result:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?H (?oA \<longleftrightarrow>\<^sub>o ?OR)"
    using rhs_equiv step2 by (rule CEV_axiom_proves.MP)
  show ?thesis
    using result unfolding pp_T6_WI_master_at_def .
qed

theorem CEV_T6_WI_advertised_master_direct:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and WI_in: "pp_WI \<in> T"
    and L2_in: "pp_L2 \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (pp_T6_WI_advertised_master r)"
proof -
  let ?a = "pp_T6_WI_a_operator r"
  let ?F = "pp_fun_prime r"
  let ?A = "Var 0"
  let ?as = "shift ?a"
  let ?Fs = "shift ?F"
  let ?PA = "pp_pure Prop ?A"
  let ?M = "pp_T6_WI_master_at ?as ?A"
  let ?Q = "Imp ?PA ?M"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have Fs_type: "Prop # \<Gamma> \<turnstile> ?Fs : Prop"
    using F_type by (rule typed_shift_ctx)
  have rs_type: "Prop # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have A_type: "Prop # \<Gamma> \<turnstile> ?A : Prop"
    by (rule typed_var0)
  have as_type:
    "Prop # \<Gamma> \<turnstile> ?as : Prop \<rightarrow>\<^sub>o Prop"
    using typed_pp_T6_WI_a_operator[OF r_type]
    by (rule typed_shift_ctx)
  have PA_type: "Prop # \<Gamma> \<turnstile> ?PA : Prop"
    using A_type by (rule typed_pp_pure)
  have M_type: "Prop # \<Gamma> \<turnstile> ?M : Prop"
    using as_type A_type by (rule typed_pp_T6_WI_master_at)
  have Q_type: "Prop # \<Gamma> \<turnstile> ?Q : Prop"
    using PA_type M_type by (rule has_type.Imp)
  have at:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Conj (pp_fun_prime (shift r)) ?PA)
        (pp_T6_WI_master_at
          (pp_T6_WI_a_operator (shift r)) ?A)"
    using core WI_in L2_in rs_type A_type
    by (rule CEV_T6_WI_master_at_operator_direct)
  have at_shifted:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj ?Fs ?PA) ?M"
    using at by simp
  have curry:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Imp (Conj ?Fs ?PA) ?M)
        (Imp ?Fs ?Q)"
  proof (rule CEV_axiom_proves.Base, rule CEV_prop_tautology)
    show "prop_tautology (Prop # \<Gamma>)
      (Imp
        (Imp (Conj ?Fs ?PA) ?M)
        (Imp ?Fs ?Q))"
    proof (unfold prop_tautology_def, intro conjI)
      show "Prop # \<Gamma> \<turnstile>
        Imp
          (Imp (Conj ?Fs ?PA) ?M)
          (Imp ?Fs ?Q) : Prop"
        using Fs_type PA_type M_type Q_type
        by (intro has_type.Imp has_type.Conj)
    next
      show "\<forall>v. prop_eval v
        (Imp
          (Imp (Conj ?Fs ?PA) ?M)
          (Imp ?Fs ?Q))"
        apply (simp only: prop_eval.simps)
        by blast
    qed
  qed
  have body:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?Fs ?Q"
    using at_shifted curry by (rule CEV_axiom_proves.MP)
  have shifted_body:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?F) ?Q"
    using body by simp
  have generalized:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (Forall Prop ?Q)"
    using F_type Q_type shifted_body
    by (rule CEV_axiom_proves.Gen)
  show ?thesis
    using generalized
    unfolding pp_T6_WI_advertised_master_def
      pp_T6_WI_master_family_def
    by simp
qed

lemma CEV_axiom_from_master_not_top:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and pure_top_in: "pp_pure Prop ObjTrue \<in> T"
    and family:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_T6_WI_master_family a"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Neg (App a ObjTrue)"
proof -
  let ?aT = "App a ObjTrue"
  let ?RT =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
          Neg (shift ObjTrue)))"
  have aT_type: "\<Gamma> \<turnstile> ?aT : Prop"
    using a_type typed_ObjTrue by (rule has_type.App)
  have pure_top:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ObjTrue"
  proof (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Axiom)
    show "pp_pure Prop ObjTrue \<in> T"
      by (rule pure_top_in)
    show "\<Gamma> \<turnstile> pp_pure Prop ObjTrue : Prop"
      using typed_ObjTrue by (rule typed_pp_pure)
  qed
  have master_top:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T6_WI_master_at a ObjTrue"
    using a_type typed_ObjTrue family pure_top
    by (rule CEV_axiom_master_family_instance)
  have aT_to_RT:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aT ?RT"
    using master_top
    unfolding pp_T6_WI_master_at_def
    by (rule CEV_axiom_from_conj_left)
  let ?S' = "insert ?aT S"
  have d_aT: "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?aT"
    using aT_type by (intro CEV_axiom_from.Assumption) simp
  have d_RT: "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?RT"
  proof -
    have d_imp:
      "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aT ?RT"
      using aT_to_RT by (rule CEV_axiom_from_mono) blast
    show ?thesis
      using d_aT d_imp by (rule CEV_axiom_from.MP)
  qed
  have pure_top':
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ObjTrue"
    using pure_top by (rule CEV_axiom_from_mono) blast
  have top_bicond:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?aT \<longleftrightarrow>\<^sub>o Neg ObjTrue)"
    using a_type typed_ObjTrue typed_ObjTrue d_RT pure_top'
    by (rule CEV_axiom_master_rhs_instance)
  have aT_to_not_true:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?aT (Neg ObjTrue)"
    using top_bicond by (rule CEV_axiom_from_conj_left)
  have not_true:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ObjTrue"
    using d_aT aT_to_not_true by (rule CEV_axiom_from.MP)
  have d_true:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjTrue"
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves_ObjTrue)
  have d_false:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_true not_true by (rule CEV_axiom_from_contradiction)
  have aT_to_false:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aT ObjFalse"
    using aT_type d_false by (rule CEV_axiom_from_deduction)
  have convert:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?aT ObjFalse) (Neg ?aT)"
    using CEV_proves_imp_false_to_neg[OF aT_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using aT_to_false convert by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_master_not_a:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and pure_top_in: "pp_pure Prop ObjTrue \<in> T"
    and family:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_T6_WI_master_family a"
    and pure_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App a A)"
proof -
  let ?aA = "App a A"
  let ?aT = "App a ObjTrue"
  let ?RA =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
          Neg (shift A)))"
  have aA_type: "\<Gamma> \<turnstile> ?aA : Prop"
    using a_type A_type by (rule has_type.App)
  have aT_type: "\<Gamma> \<turnstile> ?aT : Prop"
    using a_type typed_ObjTrue by (rule has_type.App)
  have pure_top:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ObjTrue"
  proof (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Axiom)
    show "pp_pure Prop ObjTrue \<in> T"
      by (rule pure_top_in)
    show "\<Gamma> \<turnstile> pp_pure Prop ObjTrue : Prop"
      using typed_ObjTrue by (rule typed_pp_pure)
  qed
  have master_A:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T6_WI_master_at a A"
    using a_type A_type family pure_A
    by (rule CEV_axiom_master_family_instance)
  have aA_to_RA:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aA ?RA"
    using master_A
    unfolding pp_T6_WI_master_at_def
    by (rule CEV_axiom_from_conj_left)
  have not_aT:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?aT"
    using a_type pure_top_in family
    by (rule CEV_axiom_from_master_not_top)
  let ?S' = "insert ?aA S"
  have d_aA: "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?aA"
    using aA_type by (intro CEV_axiom_from.Assumption) simp
  have d_RA: "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?RA"
  proof -
    have d_imp:
      "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aA ?RA"
      using aA_to_RA by (rule CEV_axiom_from_mono) blast
    show ?thesis
      using d_aA d_imp by (rule CEV_axiom_from.MP)
  qed
  have pure_top':
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ObjTrue"
    using pure_top by (rule CEV_axiom_from_mono) blast
  have pure_A':
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop A"
    using pure_A by (rule CEV_axiom_from_mono) blast
  have top_bicond:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?aT \<longleftrightarrow>\<^sub>o Neg A)"
    using a_type A_type typed_ObjTrue d_RA pure_top'
    by (rule CEV_axiom_master_rhs_instance)
  have not_aT':
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?aT"
    using not_aT by (rule CEV_axiom_from_mono) blast
  have recover_A_taut:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Neg ?aT)
        (Imp (?aT \<longleftrightarrow>\<^sub>o Neg A) A)"
  proof (rule CEV_axiom_from_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp (Neg ?aT)
        (Imp (?aT \<longleftrightarrow>\<^sub>o Neg A) A))"
    proof (unfold prop_tautology_def, intro conjI)
      show "\<Gamma> \<turnstile>
        Imp (Neg ?aT)
          (Imp (?aT \<longleftrightarrow>\<^sub>o Neg A) A) : Prop"
        using aT_type A_type
        by (intro has_type.Imp has_type.Neg has_type.Conj)
    next
      show "\<forall>v. prop_eval v
        (Imp (Neg ?aT)
          (Imp (?aT \<longleftrightarrow>\<^sub>o Neg A) A))"
        by (simp add: prop_eval.simps)
    qed
  qed
  have recover_A_step:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (?aT \<longleftrightarrow>\<^sub>o Neg A) A"
    using not_aT' recover_A_taut by (rule CEV_axiom_from.MP)
  have d_A: "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    using top_bicond recover_A_step by (rule CEV_axiom_from.MP)
  have self_bicond:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?aA \<longleftrightarrow>\<^sub>o Neg A)"
    using a_type A_type A_type d_RA pure_A'
    by (rule CEV_axiom_master_rhs_instance)
  have aA_to_not_A:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aA (Neg A)"
    using self_bicond by (rule CEV_axiom_from_conj_left)
  have not_A: "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg A"
    using d_aA aA_to_not_A by (rule CEV_axiom_from.MP)
  have d_false:
    "\<Gamma> ; T ; ?S' \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_A not_A by (rule CEV_axiom_from_contradiction)
  have aA_to_false:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?aA ObjFalse"
    using aA_type d_false by (rule CEV_axiom_from_deduction)
  have convert:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?aA ObjFalse) (Neg ?aA)"
    using CEV_proves_imp_false_to_neg[OF aA_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using aA_to_false convert by (rule CEV_axiom_from.MP)
qed

theorem CEV_T6_WI_master_family_inconsistent:
  assumes a_type: "\<Gamma> \<turnstile> a : Prop \<rightarrow>\<^sub>o Prop"
    and pure_top_in: "pp_pure Prop ObjTrue \<in> T"
    and family:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_T6_WI_master_family a"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof -
  let ?F = "pp_T6_WI_master_family a"
  let ?aT = "App a ObjTrue"
  let ?RT =
    "Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (App (shift a) (Var 0) \<longleftrightarrow>\<^sub>o
          Neg (shift ObjTrue)))"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using a_type by (rule typed_pp_T6_WI_master_family)
  have aT_type: "\<Gamma> \<turnstile> ?aT : Prop"
    using a_type typed_ObjTrue by (rule has_type.App)
  have pure_top:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ObjTrue"
  proof (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Axiom)
    show "pp_pure Prop ObjTrue \<in> T"
      by (rule pure_top_in)
    show "\<Gamma> \<turnstile> pp_pure Prop ObjTrue : Prop"
      using typed_ObjTrue by (rule typed_pp_pure)
  qed
  have family_local:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using family by (rule CEV_axiom_from.Theorem)
  have master_top:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T6_WI_master_at a ObjTrue"
    using a_type typed_ObjTrue family_local pure_top
    by (rule CEV_axiom_master_family_instance)
  have RT_to_aT:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?RT ?aT"
    using master_top
    unfolding pp_T6_WI_master_at_def
    by (rule CEV_axiom_from_conj_right)
  have not_aT:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?aT"
    using a_type pure_top_in family_local
    by (rule CEV_axiom_from_master_not_top)

  let ?aS = "shift a"
  let ?FS = "shift ?F"
  let ?C = "Var 0"
  let ?PC = "pp_pure Prop ?C"
  let ?aC = "App ?aS ?C"
  let ?Q = "Imp ?PC (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)"
  have aS_type:
    "Prop # \<Gamma> \<turnstile> ?aS : Prop \<rightarrow>\<^sub>o Prop"
    using a_type by (rule typed_shift_ctx)
  have C_type: "Prop # \<Gamma> \<turnstile> ?C : Prop"
    by (rule typed_var0)
  have PC_type: "Prop # \<Gamma> \<turnstile> ?PC : Prop"
    using C_type by (rule typed_pp_pure)
  have aC_type: "Prop # \<Gamma> \<turnstile> ?aC : Prop"
    using aS_type C_type by (rule has_type.App)
  have FS_type: "Prop # \<Gamma> \<turnstile> ?FS : Prop"
    using F_type by (rule typed_shift_ctx)
  have family_shift:
    "?FS = pp_T6_WI_master_family ?aS"
    by simp
  let ?S2 = "insert ?PC {?FS}"
  have d_FS:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T6_WI_master_family ?aS"
  proof -
    have raw:
      "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?FS"
      using FS_type by (intro CEV_axiom_from.Assumption) simp
    show ?thesis
      using raw family_shift by simp
  qed
  have d_PC:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PC"
    using PC_type by (intro CEV_axiom_from.Assumption) simp
  have not_aC:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?aC"
    using aS_type C_type pure_top_in d_FS d_PC
    by (rule CEV_axiom_from_master_not_a)
  have bicond_taut:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Neg ?aC)
        (Imp ObjTrue (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue))"
  proof (rule CEV_axiom_from_prop_tautology)
    show "prop_tautology (Prop # \<Gamma>)
      (Imp (Neg ?aC)
        (Imp ObjTrue (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)))"
    proof (unfold prop_tautology_def, intro conjI)
      show "Prop # \<Gamma> \<turnstile>
        Imp (Neg ?aC)
          (Imp ObjTrue
            (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)) : Prop"
        using aC_type typed_ObjTrue
        by (intro has_type.Imp has_type.Neg has_type.Conj)
    next
      show "\<forall>v. prop_eval v
        (Imp (Neg ?aC)
          (Imp ObjTrue
            (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)))"
        by (simp add: prop_eval.simps)
    qed
  qed
  have bicond_step:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ObjTrue (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)"
    using not_aC bicond_taut by (rule CEV_axiom_from.MP)
  have d_true:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjTrue"
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves_ObjTrue)
  have d_bicond:
    "Prop # \<Gamma> ; T ; ?S2 \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)"
    using d_true bicond_step by (rule CEV_axiom_from.MP)
  have under_FS:
    "Prop # \<Gamma> ; T ; {?FS} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Q"
  proof (rule CEV_axiom_from_deduction)
    show "Prop # \<Gamma> \<turnstile> ?PC : Prop"
      by (rule PC_type)
    show "Prop # \<Gamma> ; T ; insert ?PC {?FS}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        (?aC \<longleftrightarrow>\<^sub>o Neg ObjTrue)"
      by (rule d_bicond)
  qed
  have empty_local:
    "Prop # \<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?FS ?Q"
  proof (rule CEV_axiom_from_deduction)
    show "Prop # \<Gamma> \<turnstile> ?FS : Prop"
      by (rule FS_type)
    show "Prop # \<Gamma> ; T ; insert ?FS {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Q"
      using under_FS by simp
  qed
  have shifted_guard:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ?F) ?Q"
    using empty_local CEV_axiom_from_empty_iff by blast
  have rhs_guard:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?F (Forall Prop ?Q)"
  proof (rule CEV_axiom_proves.Gen)
    show "\<Gamma> \<turnstile> ?F : Prop" by (rule F_type)
    show "Prop # \<Gamma> \<turnstile> ?Q : Prop"
      using PC_type aC_type typed_ObjTrue
      by (intro has_type.Imp has_type.Conj has_type.Neg)
    show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ?F) ?Q"
      by (rule shifted_guard)
  qed
  have d_RT_raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall Prop ?Q"
    using family rhs_guard by (rule CEV_axiom_proves.MP)
  have d_RT:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?RT"
    using d_RT_raw
    by (intro CEV_axiom_from.Theorem)
      (simp add: shift_def ObjTrue_def)
  have d_aT:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?aT"
    using d_RT RT_to_aT by (rule CEV_axiom_from.MP)
  have d_false:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_aT not_aT by (rule CEV_axiom_from_contradiction)
  show ?thesis
    using d_false CEV_axiom_from_empty_iff by blast
qed

corollary CEV_T6_WI_advertised_master_inconsistent:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and core: "pp_T6_core_PP_axioms \<subseteq> T"
    and master:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_T6_WI_advertised_master r"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof -
  have pure_top_in: "pp_pure Prop ObjTrue \<in> T"
    using pp_ObjTrue_purity_axiom core
    unfolding pp_T6_core_PP_axioms_def by blast
  have a_type:
    "\<Gamma> \<turnstile> pp_T6_WI_a_operator r : Prop \<rightarrow>\<^sub>o Prop"
    using r_type by (rule typed_pp_T6_WI_a_operator)
  have family:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_T6_WI_master_family (pp_T6_WI_a_operator r)"
    using master unfolding pp_T6_WI_advertised_master_def .
  show ?thesis
    using a_type pure_top_in family
    by (rule CEV_T6_WI_master_family_inconsistent)
qed

lemma CEV_axiom_explosion:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and false: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
proof -
  have taut_raw:
    "\<Gamma> \<turnstile>\<^sub>CEV Imp (Neg ObjTrue) (Imp ObjTrue A)"
    using typed_ObjTrue A_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_imp_of_neg_left)
  have explosion_step:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjFalse (Imp ObjTrue A)"
    using taut_raw
    by (intro CEV_axiom_proves.Base)
      (simp add: ObjFalse_def)
  have true_to_A:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ObjTrue A"
    using false explosion_step by (rule CEV_axiom_proves.MP)
  have d_true: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjTrue"
    by (rule CEV_axiom_proves_ObjTrue)
  show ?thesis
    using d_true true_to_A by (rule CEV_axiom_proves.MP)
qed

theorem CEV_Goodman_T6_WI_advertised_master_claim_direct:
  "[] ; pp_T6_WI_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_T6_WI_advertised_master_claim"
proof -
  let ?Q =
    "Imp
      (pp_fun_prime (Var 0))
      (pp_T6_WI_advertised_master (Var 0))"
  have core:
    "pp_T6_core_PP_axioms \<subseteq> pp_T6_WI_axioms"
    unfolding pp_T6_WI_axioms_def by blast
  have WI_in: "pp_WI \<in> pp_T6_WI_axioms"
    unfolding pp_T6_WI_axioms_def by blast
  have L2_in: "pp_L2 \<in> pp_T6_WI_axioms"
    unfolding pp_T6_WI_axioms_def by blast
  have v_type: "[Prop] \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have Q_type: "[Prop] \<turnstile> ?Q : Prop"
    using typed_pp_fun_prime[OF v_type]
      typed_pp_T6_WI_advertised_master[OF v_type]
    by (rule has_type.Imp)
  have body:
    "[Prop] ; pp_T6_WI_axioms \<turnstile>\<^sub>CEV\<^sup>+ ?Q"
    using core WI_in L2_in v_type
    by (rule CEV_T6_WI_advertised_master_direct)
  have guarded:
    "[Prop] ; pp_T6_WI_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue ?Q"
    using typed_ObjTrue body by (rule CEV_axiom_imp_of_right)
  have generalized_imp:
    "[] ; pp_T6_WI_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue (Forall Prop ?Q)"
  proof (rule CEV_axiom_proves.Gen)
    show "[] \<turnstile> ObjTrue : Prop"
      by (rule typed_ObjTrue)
    show "[Prop] \<turnstile> ?Q : Prop"
      by (rule Q_type)
    show "[Prop] ; pp_T6_WI_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ObjTrue) ?Q"
      using guarded by (simp add: ObjTrue_def shift_def)
  qed
  have d_true:
    "[] ; pp_T6_WI_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjTrue"
    by (rule CEV_axiom_proves_ObjTrue)
  have generalized:
    "[] ; pp_T6_WI_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Forall Prop ?Q"
    using d_true generalized_imp by (rule CEV_axiom_proves.MP)
  show ?thesis
    using generalized
    unfolding pp_T6_WI_advertised_master_claim_def .
qed

text \<open>
  For comparison with the direct derivation above, the following redundant
  theorem records the shorter ex-falso route from the already established
  inconsistency of the exact T6-WI stock.  Its name exposes that weaker
  provenance.
\<close>

theorem CEV_Goodman_T6_WI_advertised_master_claim_ex_falso:
  "[] ; pp_T6_WI_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_T6_WI_advertised_master_claim"
  using typed_pp_T6_WI_advertised_master_claim CEV_Goodman_T6_WI
  by (rule CEV_axiom_explosion)

end
