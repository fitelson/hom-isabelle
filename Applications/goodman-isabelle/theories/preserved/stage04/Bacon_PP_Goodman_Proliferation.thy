theory Bacon_PP_Goodman_Proliferation
  imports 
    "Goodman_Legacy_04.Bacon_PP_Goodman_Higher_Type_Diagonal"
begin

section \<open>Goodman T5: proliferation of \<open>fun\<acute>\<close> propositions\<close>

text \<open>
  The proof uses Goodman's T6 liar but no transfer principle and no
  classification of the group of pure reversible operators.  Its temporary
  reductio hypothesis says that every \<open>fun\<acute>\<close> proposition is either
  \<open>r\<close> or \<open>\<not>r\<close>.  The delicate second case uses the operator
  \<open>\<not> \<circ> D \<circ> \<not>\<close>, with both inner double negations discharged as
  proposition identities.
\<close>

definition pp_T5_liar_body :: oterm where
  "pp_T5_liar_body =
    Forall pp_unary_ty
      (Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty (Var 1))
            (Conj
              (pp_fun_prime (Var 0))
              (Eq Prop
                (Var 2)
                (App (Var 1) (Var 0)))))
          (Neg
            (App (Var 1) (Var 2)))))"

definition pp_T5_liar_at :: "oterm \<Rightarrow> oterm" where
  "pp_T5_liar_at p = subst0 p pp_T5_liar_body"

lemma pp_T5_liar_at_explicit:
  "pp_T5_liar_at p =
    Forall pp_unary_ty
      (Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty (Var 1))
            (Conj
              (pp_fun_prime (Var 0))
              (Eq Prop
                (shift_by 2 p)
                (App (Var 1) (Var 0)))))
          (Neg
            (App (Var 1) (shift_by 2 p)))))"
proof -
  have ren:
    "rename Suc (rename Suc p) = rename (shift_ren 2 0) p"
    using shift_shift_eq_shift_by_2[of p]
    unfolding shift_def shift_by_def .
  show ?thesis
    by (simp add: pp_T5_liar_at_def pp_T5_liar_body_def subst0_def
      pp_fun_prime_def pp_pure_def pp_Pure_def
      shift_by_def shift_ren_def eval_nat_numeral ren)
qed

lemma subst0_pp_fun_prime_var0[simp]:
  "subst0 q (pp_fun_prime (Var 0)) = pp_fun_prime q"
proof -
  have ren:
    "rename Suc (rename Suc q) = rename (shift_ren 2 0) q"
    using shift_shift_eq_shift_by_2[of q]
    unfolding shift_def shift_by_def .
  show ?thesis
    by (simp add: pp_fun_prime_def pp_pure_def pp_Pure_def subst0_def
      shift_by_def shift_ren_def eval_nat_numeral ren)
qed

definition pp_T5_two_fun_prime :: "oterm \<Rightarrow> oterm" where
  "pp_T5_two_fun_prime r =
    Forall Prop
      (Imp
        (pp_fun_prime (Var 0))
        (Disj
          (Eq Prop (Var 0) (shift r))
          (Eq Prop (Var 0) (Neg (shift r)))))"

definition pp_T5_proliferation :: "oterm \<Rightarrow> oterm" where
  "pp_T5_proliferation r =
    Exists Prop
      (Conj
        (pp_fun_prime (Var 0))
        (Conj
          (Neg (Eq Prop (Var 0) (shift r)))
          (Neg (Eq Prop (Var 0) (Neg (shift r))))))"

definition pp_T5_axioms :: "oterm set" where
  "pp_T5_axioms = pp_T6_core_PP_axioms"

lemma typed_pp_T5_liar_at:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile> pp_T5_liar_at p : Prop"
proof -
  have body_type: "Prop # \<Gamma> \<turnstile> pp_T5_liar_body : Prop"
    using typed_pp_T6_liar[of \<Gamma>]
    unfolding pp_T6_liar_def pp_T5_liar_body_def pp_unary_ty_def
    by (auto elim: has_type.cases)
  show ?thesis
    unfolding pp_T5_liar_at_def
    using body_type p_type by (rule subst0_preserves_typing)
qed

lemma typed_pp_T5_two_fun_prime:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> pp_T5_two_fun_prime r : Prop"
proof -
  have r_shift: "Prop # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have q_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  show ?thesis
    unfolding pp_T5_two_fun_prime_def
    using typed_pp_fun_prime[OF q_type] q_type r_shift
    by (intro has_type.Forall has_type.Imp has_type.Disj
        has_type.Eq has_type.Neg)
qed

lemma typed_pp_T5_proliferation:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> pp_T5_proliferation r : Prop"
proof -
  have r_shift: "Prop # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have q_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  show ?thesis
    unfolding pp_T5_proliferation_def
    using typed_pp_fun_prime[OF q_type] q_type r_shift
    by (intro has_type.Exists has_type.Conj has_type.Neg has_type.Eq)
qed

lemma shift_pp_T5_two_fun_prime[simp]:
  "shift (pp_T5_two_fun_prime r) =
    pp_T5_two_fun_prime (shift r)"
  by (simp add: pp_T5_two_fun_prime_def shift_def
    pp_fun_prime_def pp_pure_def pp_Pure_def
    shift_by_def shift_ren_def rename_lift_Suc_after_shift)

lemma shift_by_2_pp_T5_two_fun_prime[simp]:
  "shift_by 2 (pp_T5_two_fun_prime r) =
    pp_T5_two_fun_prime (shift_by 2 r)"
proof -
  have lhs:
    "shift_by 2 (pp_T5_two_fun_prime r) =
      shift (shift (pp_T5_two_fun_prime r))"
    using shift_shift_eq_shift_by_2[of "pp_T5_two_fun_prime r"]
    by simp
  have rhs:
    "shift_by 2 r = shift (shift r)"
    using shift_shift_eq_shift_by_2[of r] by simp
  show ?thesis
    using lhs rhs by simp
qed

lemma pp_T6_liar_apply_beta:
  "compatible_step beta_contract
    (App pp_T6_liar p)
    (pp_T5_liar_at p)"
  unfolding pp_T6_liar_def pp_T5_liar_body_def
    pp_T5_liar_at_def
  by (intro compatible_step.root beta_contract.beta)

lemma CEV_pp_T6_liar_apply_eq:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop (App pp_T6_liar p) (pp_T5_liar_at p)"
proof -
  have left_type: "\<Gamma> \<turnstile> App pp_T6_liar p : Prop"
    using typed_pp_T6_liar p_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have right_type: "\<Gamma> \<turnstile> pp_T5_liar_at p : Prop"
    using p_type by (rule typed_pp_T5_liar_at)
  have iff:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App pp_T6_liar p \<longleftrightarrow>\<^sub>o pp_T5_liar_at p)"
    using left_type right_type pp_T6_liar_apply_beta
    by (rule CEV_beta_step)
  show ?thesis
    using left_type right_type iff by (rule CEV_zeroary_equivalence)
qed

lemma CEV_axiom_from_T5_liar_elim:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
    and liar:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App pp_T6_liar p"
    and pure_X:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty X"
    and fun_q:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime q"
    and decomposition:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop p (App X q)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App X p)"
proof -
  have liar_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_T6_liar p) (pp_T5_liar_at p)"
    using CEV_pp_T6_liar_apply_eq[OF p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have liar_at:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_T5_liar_at p"
    using
      has_type.App[
        OF typed_pp_T6_liar[unfolded pp_unary_ty_def] p_type]
      typed_pp_T5_liar_at[OF p_type]
      liar liar_eq
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_prop_elim)
  have liar_at_explicit:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall pp_unary_ty
        (Forall Prop
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 1))
              (Conj
                (pp_fun_prime (Var 0))
                (Eq Prop
                  (shift_by 2 p)
                  (App (Var 1) (Var 0)))))
            (Neg
              (App (Var 1) (shift_by 2 p)))))"
    using liar_at by (simp only: pp_T5_liar_at_explicit)
  have outer_raw:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 X
        (Forall Prop
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 1))
              (Conj
                (pp_fun_prime (Var 0))
                (Eq Prop
                  (shift_by 2 p)
                  (App (Var 1) (Var 0)))))
            (Neg
              (App (Var 1) (shift_by 2 p)))))"
  proof (rule CEV_axiom_from_UI_typed)
    show "\<Gamma> \<turnstile>
      Forall pp_unary_ty
        (Forall Prop
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 1))
              (Conj
                (pp_fun_prime (Var 0))
                (Eq Prop
                  (shift_by 2 p)
                  (App (Var 1) (Var 0)))))
            (Neg
              (App (Var 1) (shift_by 2 p))))) : Prop"
      using typed_pp_T5_liar_at[OF p_type]
      by (simp only: pp_T5_liar_at_explicit)
    show "\<Gamma> \<turnstile> X : pp_unary_ty" by (rule X_type)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall pp_unary_ty
        (Forall Prop
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 1))
              (Conj
                (pp_fun_prime (Var 0))
                (Eq Prop
                  (shift_by 2 p)
                  (App (Var 1) (Var 0)))))
            (Neg
              (App (Var 1) (shift_by 2 p)))))"
      by (rule liar_at_explicit)
  qed
  have subst_p:
    "subst
      (lift_subst (case_nat X Var))
      (rename (shift_ren 2 0) p) = shift p"
    by (rule subst_lift_shift_by_2)
  have outer:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift X))
            (Conj
              (pp_fun_prime (Var 0))
              (Eq Prop
                (shift p)
                (App (shift X) (Var 0)))))
          (Neg
            (App (shift X) (shift p))))"
    using outer_raw
    by (simp add: subst0_def pp_fun_prime_def pp_pure_def pp_Pure_def
      shift_by_def shift_ren_def shift_def subst_lift_shift subst_p)
  have inner_raw:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 q
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift X))
            (Conj
              (pp_fun_prime (Var 0))
              (Eq Prop
                (shift p)
                (App (shift X) (Var 0)))))
          (Neg
            (App (shift X) (shift p))))"
  proof (rule CEV_axiom_from_UI_typed)
    show "\<Gamma> \<turnstile>
      Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift X))
            (Conj
              (pp_fun_prime (Var 0))
              (Eq Prop
                (shift p)
                (App (shift X) (Var 0)))))
          (Neg
            (App (shift X) (shift p)))) : Prop"
      using outer by (rule CEV_axiom_from_formula)
    show "\<Gamma> \<turnstile> q : Prop" by (rule q_type)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift X))
            (Conj
              (pp_fun_prime (Var 0))
              (Eq Prop
                (shift p)
                (App (shift X) (Var 0)))))
          (Neg
            (App (shift X) (shift p))))"
      by (rule outer)
  qed
  have rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj
          (pp_pure pp_unary_ty X)
          (Conj
            (pp_fun_prime q)
            (Eq Prop p (App X q))))
        (Neg (App X p))"
  proof -
    have subst_X:
      "subst (case_nat q Var) (rename Suc X) = X"
      using subst0_shift[of q X]
      unfolding subst0_def shift_def .
    have subst_p0:
      "subst (case_nat q Var) (rename Suc p) = p"
      using subst0_shift[of q p]
      unfolding subst0_def shift_def .
    have subst_fun:
      "subst (case_nat q Var) (pp_fun_prime (Var 0)) =
        pp_fun_prime q"
      using subst0_pp_fun_prime_var0[of q]
      unfolding subst0_def .
    show ?thesis
    using inner_raw
      by (simp add: subst0_def pp_pure_def pp_Pure_def shift_def
        subst_lift_shift subst_X subst_p0 subst_fun)
  qed
  have tail:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_fun_prime q)
        (Eq Prop p (App X q))"
    using fun_q decomposition by (rule CEV_axiom_from_conj_intro)
  have all_premises:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty X)
        (Conj
          (pp_fun_prime q)
          (Eq Prop p (App X q)))"
    using pure_X tail by (rule CEV_axiom_from_conj_intro)
  show ?thesis
    using all_premises rule by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_T5_neg_cong:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and AB:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop A B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (Neg A) (Neg B)"
proof -
  let ?N = pp_negation_operator
  have NA_type: "\<Gamma> \<turnstile> App ?N A : Prop"
    using typed_pp_negation_operator A_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have NB_type: "\<Gamma> \<turnstile> App ?N B : Prop"
    using typed_pp_negation_operator B_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have nA_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by (rule has_type.Neg)
  have nB_type: "\<Gamma> \<turnstile> Neg B : Prop"
    using B_type by (rule has_type.Neg)
  have op_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?N A) (App ?N B)"
    using typed_pp_negation_operator A_type B_type AB
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have beta_A:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?N A) (Neg A)"
    using CEV_pp_negation_apply_eq[OF A_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have beta_B:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?N B) (Neg B)"
    using CEV_pp_negation_apply_eq[OF B_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have beta_A_sym:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg A) (App ?N A)"
    using NA_type nA_type beta_A by (rule CEV_axiom_from_eq_sym)
  have first:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg A) (App ?N B)"
    using nA_type NA_type NB_type beta_A_sym op_eq
    by (rule CEV_axiom_from_eq_trans)
  show ?thesis
    using nA_type NB_type nB_type first beta_B
    by (rule CEV_axiom_from_eq_trans)
qed

lemma CEV_axiom_from_T5_disj_cases:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and disj:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Disj A B"
    and left:
      "\<Gamma> ; T ; insert A S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s C"
    and right:
      "\<Gamma> ; T ; insert B S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s C"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s C"
proof -
  have left_imp:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp A C"
    using A_type left by (rule CEV_axiom_from_deduction)
  have right_imp:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp B C"
    using B_type right by (rule CEV_axiom_from_deduction)
  have taut:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp A C)
        (Imp (Imp B C)
          (Imp (Disj A B) C))"
  proof (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base
      CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
    have formula_type:
      "\<Gamma> \<turnstile>
        Imp (Imp A C)
          (Imp (Imp B C)
            (Imp (Disj A B) C)) : Prop"
      using A_type B_type C_type by auto
    show "prop_tautology \<Gamma>
      (Imp (Imp A C)
        (Imp (Imp B C)
          (Imp (Disj A B) C)))"
      unfolding prop_tautology_def
      using formula_type by auto
  qed
  have step1:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp B C) (Imp (Disj A B) C)"
    using left_imp taut by (rule CEV_axiom_from.MP)
  have step2:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Disj A B) C"
    using right_imp step1 by (rule CEV_axiom_from.MP)
  show ?thesis
    using disj step2 by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_T5_inner_neg_neg_apply_eq:
  assumes F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop
      (App
        (pp_compose F pp_negation_operator)
        (Neg p))
      (App F p)"
proof -
  let ?N = pp_negation_operator
  let ?np = "Neg p"
  let ?Nnp = "App ?N ?np"
  have N_type: "\<Gamma> \<turnstile> ?N : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  have np_type: "\<Gamma> \<turnstile> ?np : Prop"
    using p_type by (rule has_type.Neg)
  have Nnp_type: "\<Gamma> \<turnstile> ?Nnp : Prop"
    using N_type np_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have nnp_type: "\<Gamma> \<turnstile> Neg ?np : Prop"
    using np_type by (rule has_type.Neg)
  have F_Nnp_type: "\<Gamma> \<turnstile> App F ?Nnp : Prop"
    using F_type Nnp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have F_nnp_type: "\<Gamma> \<turnstile> App F (Neg ?np) : Prop"
    using F_type nnp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Fp_type: "\<Gamma> \<turnstile> App F p : Prop"
    using F_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have comp:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop
        (App (pp_compose F ?N) ?np)
        (App F ?Nnp)"
    using CEV_pp_compose_apply_eq[OF F_type N_type np_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have neg_beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?Nnp (Neg ?np)"
    using CEV_pp_negation_apply_eq[OF np_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have under_F:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App F ?Nnp) (App F (Neg ?np))"
    using F_type Nnp_type nnp_type neg_beta
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have double_neg:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?np) p"
  proof (rule CEV_axiom_from_eq_sym)
    show "\<Gamma> \<turnstile> p : Prop" by (rule p_type)
    show "\<Gamma> \<turnstile> Neg ?np : Prop" by (rule nnp_type)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop p (Neg ?np)"
      using CEV_double_negation_eq[OF p_type]
      by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  qed
  have under_F_double:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App F (Neg ?np)) (App F p)"
    using F_type nnp_type p_type double_neg
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop
        (App (pp_compose F ?N) ?np)
        (App F (Neg ?np))"
  proof (rule CEV_axiom_from_eq_trans)
    show "\<Gamma> \<turnstile> App (pp_compose F ?N) ?np : Prop"
      using typed_pp_compose[OF F_type N_type] np_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    show "\<Gamma> \<turnstile> App F ?Nnp : Prop" by (rule F_Nnp_type)
    show "\<Gamma> \<turnstile> App F (Neg ?np) : Prop"
      by (rule F_nnp_type)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App (pp_compose F ?N) ?np) (App F ?Nnp)"
      by (rule comp)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App F ?Nnp) (App F (Neg ?np))"
      by (rule under_F)
  qed
  show ?thesis
  proof (rule CEV_axiom_from_eq_trans)
    show "\<Gamma> \<turnstile> App (pp_compose F ?N) ?np : Prop"
      using typed_pp_compose[OF F_type N_type] np_type
      unfolding pp_unary_ty_def by (rule has_type.App)
    show "\<Gamma> \<turnstile> App F (Neg ?np) : Prop"
      by (rule F_nnp_type)
    show "\<Gamma> \<turnstile> App F p : Prop" by (rule Fp_type)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop
        (App (pp_compose F ?N) ?np)
        (App F (Neg ?np))"
      by (rule step)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App F (Neg ?np)) (App F p)"
      by (rule under_F_double)
  qed
qed

lemma CEV_axiom_from_T5_triple_neg_apply_eq:
  assumes F_type: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop
      (App
        (pp_compose pp_negation_operator
          (pp_compose F pp_negation_operator))
        (Neg p))
      (Neg (App F p))"
proof -
  let ?N = pp_negation_operator
  let ?G = "pp_compose F ?N"
  let ?H = "pp_compose ?N ?G"
  let ?np = "Neg p"
  let ?Nnp = "App ?N ?np"
  let ?F_Nnp = "App F ?Nnp"
  let ?F_nnp = "App F (Neg ?np)"
  have N_type: "\<Gamma> \<turnstile> ?N : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  have G_type: "\<Gamma> \<turnstile> ?G : pp_unary_ty"
    using F_type N_type by (rule typed_pp_compose)
  have H_type: "\<Gamma> \<turnstile> ?H : pp_unary_ty"
    using N_type G_type by (rule typed_pp_compose)
  have np_type: "\<Gamma> \<turnstile> ?np : Prop"
    using p_type by (rule has_type.Neg)
  have Nnp_type: "\<Gamma> \<turnstile> ?Nnp : Prop"
    using N_type np_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have nnp_type: "\<Gamma> \<turnstile> Neg ?np : Prop"
    using np_type by (rule has_type.Neg)
  have GNp_type: "\<Gamma> \<turnstile> App ?G ?np : Prop"
    using G_type np_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have F_Nnp_type: "\<Gamma> \<turnstile> ?F_Nnp : Prop"
    using F_type Nnp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have F_nnp_type: "\<Gamma> \<turnstile> ?F_nnp : Prop"
    using F_type nnp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Fp_type: "\<Gamma> \<turnstile> App F p : Prop"
    using F_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have outer:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop
        (App ?H ?np)
        (App ?N (App ?G ?np))"
    using CEV_pp_compose_apply_eq[OF N_type G_type np_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have inner:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?G ?np) ?F_Nnp"
    using CEV_pp_compose_apply_eq[OF F_type N_type np_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have inner_under_N:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop
        (App ?N (App ?G ?np))
        (App ?N ?F_Nnp)"
    using N_type GNp_type F_Nnp_type inner
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have step1:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?H ?np) (App ?N ?F_Nnp)"
  proof (rule CEV_axiom_from_eq_trans)
    show "\<Gamma> \<turnstile> App ?H ?np : Prop"
      using H_type np_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "\<Gamma> \<turnstile> App ?N (App ?G ?np) : Prop"
      using N_type GNp_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "\<Gamma> \<turnstile> App ?N ?F_Nnp : Prop"
      using N_type F_Nnp_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?H ?np) (App ?N (App ?G ?np))"
      by (rule outer)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?N (App ?G ?np)) (App ?N ?F_Nnp)"
      by (rule inner_under_N)
  qed
  have outer_beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?N ?F_Nnp) (Neg ?F_Nnp)"
    using CEV_pp_negation_apply_eq[OF F_Nnp_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have step2:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?H ?np) (Neg ?F_Nnp)"
  proof (rule CEV_axiom_from_eq_trans)
    show "\<Gamma> \<turnstile> App ?H ?np : Prop"
      using H_type np_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "\<Gamma> \<turnstile> App ?N ?F_Nnp : Prop"
      using N_type F_Nnp_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "\<Gamma> \<turnstile> Neg ?F_Nnp : Prop"
      using F_Nnp_type by (rule has_type.Neg)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?H ?np) (App ?N ?F_Nnp)"
      by (rule step1)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?N ?F_Nnp) (Neg ?F_Nnp)"
      by (rule outer_beta)
  qed
  have Nnp_beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?Nnp (Neg ?np)"
    using CEV_pp_negation_apply_eq[OF np_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have F_beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?F_Nnp ?F_nnp"
    using F_type Nnp_type nnp_type Nnp_beta
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have neg_F_beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?F_Nnp) (Neg ?F_nnp)"
    using F_Nnp_type F_nnp_type F_beta
    by (rule CEV_axiom_from_T5_neg_cong)
  have double_neg:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?np) p"
  proof (rule CEV_axiom_from_eq_sym)
    show "\<Gamma> \<turnstile> p : Prop" by (rule p_type)
    show "\<Gamma> \<turnstile> Neg ?np : Prop" by (rule nnp_type)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop p (Neg ?np)"
      using CEV_double_negation_eq[OF p_type]
      by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  qed
  have F_double:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?F_nnp (App F p)"
    using F_type nnp_type p_type double_neg
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have neg_F_double:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?F_nnp) (Neg (App F p))"
    using F_nnp_type Fp_type F_double
    by (rule CEV_axiom_from_T5_neg_cong)
  have step3:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?H ?np) (Neg ?F_nnp)"
  proof (rule CEV_axiom_from_eq_trans)
    show "\<Gamma> \<turnstile> App ?H ?np : Prop"
      using H_type np_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "\<Gamma> \<turnstile> Neg ?F_Nnp : Prop"
      using F_Nnp_type by (rule has_type.Neg)
    show "\<Gamma> \<turnstile> Neg ?F_nnp : Prop"
      using F_nnp_type by (rule has_type.Neg)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?H ?np) (Neg ?F_Nnp)"
      by (rule step2)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?F_Nnp) (Neg ?F_nnp)"
      by (rule neg_F_beta)
  qed
  show ?thesis
  proof (rule CEV_axiom_from_eq_trans)
    show "\<Gamma> \<turnstile> App ?H ?np : Prop"
      using H_type np_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "\<Gamma> \<turnstile> Neg ?F_nnp : Prop"
      using F_nnp_type by (rule has_type.Neg)
    show "\<Gamma> \<turnstile> Neg (App F p) : Prop"
      using Fp_type by (rule has_type.Neg)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?H ?np) (Neg ?F_nnp)"
      by (rule step3)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?F_nnp) (Neg (App F p))"
      by (rule neg_F_double)
  qed
qed

subsection \<open>The two diagonal refutations\<close>

theorem CEV_T5_not_Dd:
  assumes core: "pp_T5_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg
        (App pp_T6_liar (App pp_T6_liar r)))"
proof -
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?F = "pp_fun_prime r"
  let ?P = "App ?D ?d"
  let ?S = "insert ?P {?F}"
  have core_T6: "pp_T6_core_PP_axioms \<subseteq> T"
    using core unfolding pp_T5_axioms_def .
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using D_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have d_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_P:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have pure_D:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?D"
    using CEV_axiom_proves_mono[
      OF pp_T6_liar_pure core_T6]
    by (rule CEV_axiom_from.Theorem)
  have decomposition:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?d (App ?D r)"
    using d_type
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base
        CEV_proves.CE CE_proves.C C_proves.H H_proves.Ref)
  have not_P:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?P"
    using d_type D_type r_type d_P pure_D d_F decomposition
    by (rule CEV_axiom_from_T5_liar_elim)
  have false:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_P not_P by (rule CEV_axiom_from_contradiction)
  have P_imp_false:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?P ObjFalse"
    using P_type false by (rule CEV_axiom_from_deduction)
  have to_neg:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?P ObjFalse) (Neg ?P)"
    using CEV_proves_imp_false_to_neg[OF P_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have not_P_under_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?P"
    using P_imp_false to_neg by (rule CEV_axiom_from.MP)
  show ?thesis
    using F_type not_P_under_F by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_T5_not_D_neg_d:
  assumes core: "pp_T5_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg
        (App pp_T6_liar
          (Neg (App pp_T6_liar r))))"
proof -
  let ?N = pp_negation_operator
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?P = "App ?D ?d"
  let ?Q = "App ?D (Neg ?d)"
  let ?X = "pp_compose ?N (pp_compose ?D ?N)"
  let ?F = "pp_fun_prime r"
  let ?S = "insert ?Q {?F}"
  have core_T6: "pp_T6_core_PP_axioms \<subseteq> T"
    using core unfolding pp_T5_axioms_def .
  have N_type: "\<Gamma> \<turnstile> ?N : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have DN_type: "\<Gamma> \<turnstile> pp_compose ?D ?N : pp_unary_ty"
    using D_type N_type by (rule typed_pp_compose)
  have X_type: "\<Gamma> \<turnstile> ?X : pp_unary_ty"
    using N_type DN_type by (rule typed_pp_compose)
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have nd_type: "\<Gamma> \<turnstile> Neg ?d : Prop"
    using d_type by (rule has_type.Neg)
  have nr_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using D_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Q_type: "\<Gamma> \<turnstile> ?Q : Prop"
    using D_type nd_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have d_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_Q:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Q"
    using Q_type by (intro CEV_axiom_from.Assumption) simp
  have not_P:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?P"
  proof -
    have rule:
      "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?F (Neg ?P)"
      using CEV_T5_not_Dd[OF core r_type]
      by (rule CEV_axiom_from.Theorem)
    show ?thesis
      using d_F rule by (rule CEV_axiom_from.MP)
  qed
  have fun_nr:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_fun_prime (Neg r)"
  proof -
    have rule:
      "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?F (pp_fun_prime (Neg r))"
      using CEV_fun_prime_under_negation[OF core_T6 r_type]
      by (rule CEV_axiom_from.Theorem)
    show ?thesis
      using d_F rule by (rule CEV_axiom_from.MP)
  qed
  have pure_D:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?D"
    using CEV_axiom_proves_mono[
      OF pp_T6_liar_pure core_T6]
    by (rule CEV_axiom_from.Theorem)
  have pure_N_plus:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty ?N"
  proof (rule CEV_axiom_proves.Axiom)
    show "pp_pure pp_unary_ty ?N \<in> T"
      using pp_T6_negation_purity_axiom core_T6 by blast
    show "\<Gamma> \<turnstile> pp_pure pp_unary_ty ?N : Prop"
      using N_type by (rule typed_pp_pure)
  qed
  have pure_N:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?N"
    using pure_N_plus by (rule CEV_axiom_from.Theorem)
  have pure_DN:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty (pp_compose ?D ?N)"
    using core_T6 D_type N_type pure_D pure_N
    by (rule pp_compose_pure_from)
  have pure_X:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?X"
    using core_T6 N_type DN_type pure_N pure_DN
    by (rule pp_compose_pure_from)
  have X_at_nr:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?X (Neg r)) (Neg ?d)"
    using CEV_axiom_from_T5_triple_neg_apply_eq[
      OF D_type r_type, where T = T and S = ?S]
    by simp
  have decomposition:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?d) (App ?X (Neg r))"
    using
      has_type.App[OF X_type[unfolded pp_unary_ty_def] nr_type]
      nd_type X_at_nr
    by (rule CEV_axiom_from_eq_sym)
  have not_X_nd:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (App ?X (Neg ?d))"
    using nd_type X_type nr_type d_Q pure_X fun_nr decomposition
    by (rule CEV_axiom_from_T5_liar_elim)
  have X_at_nd:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?X (Neg ?d)) (Neg ?P)"
    using CEV_axiom_from_T5_triple_neg_apply_eq[
      OF D_type d_type, where T = T and S = ?S]
    by simp
  have not_cong:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop
        (Neg (App ?X (Neg ?d)))
        (Neg (Neg ?P))"
    using
      has_type.App[
        OF X_type[unfolded pp_unary_ty_def] nd_type]
      has_type.Neg[OF P_type] X_at_nd
    by (rule CEV_axiom_from_T5_neg_cong)
  have double_not_P:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Neg ?P)"
    using
      has_type.Neg[
        OF has_type.App[
          OF X_type[unfolded pp_unary_ty_def] nd_type]]
      has_type.Neg[OF has_type.Neg[OF P_type]]
      not_X_nd not_cong
    by (rule CEV_axiom_from_eq_prop_elim)
  have false:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using not_P double_not_P by (rule CEV_axiom_from_contradiction)
  have Q_imp_false:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?Q ObjFalse"
    using Q_type false by (rule CEV_axiom_from_deduction)
  have to_neg:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?Q ObjFalse) (Neg ?Q)"
    using CEV_proves_imp_false_to_neg[OF Q_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have not_Q:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?Q"
    using Q_imp_false to_neg by (rule CEV_axiom_from.MP)
  show ?thesis
    using F_type not_Q by (rule CEV_axiom_from_singleton_imp)
qed

subsection \<open>The two-element hypothesis makes the liar true at its diagonal\<close>

lemma CEV_T5_liar_matrix_from_two:
  assumes core: "pp_T5_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_fun_prime r)
        (pp_T5_two_fun_prime r))
      (Imp
        (Conj
          (pp_pure pp_unary_ty X)
          (Conj
            (pp_fun_prime q)
            (Eq Prop
              (App pp_T6_liar r)
              (App X q))))
        (Neg
          (App X (App pp_T6_liar r))))"
proof -
  let ?N = pp_negation_operator
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?H = "Conj (pp_fun_prime r) (pp_T5_two_fun_prime r)"
  let ?P =
    "Conj
      (pp_pure pp_unary_ty X)
      (Conj
        (pp_fun_prime q)
        (Eq Prop ?d (App X q)))"
  let ?R = "Neg (App X ?d)"
  let ?Er = "Eq Prop q r"
  let ?Enr = "Eq Prop q (Neg r)"
  let ?S = "insert ?P {?H}"
  have core_T6: "pp_T6_core_PP_axioms \<subseteq> T"
    using core unfolding pp_T5_axioms_def .
  have N_type: "\<Gamma> \<turnstile> ?N : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xq_type: "\<Gamma> \<turnstile> App X q : Prop"
    using X_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xd_type: "\<Gamma> \<turnstile> App X ?d : Prop"
    using X_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have F_type: "\<Gamma> \<turnstile> pp_fun_prime r : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have C_type: "\<Gamma> \<turnstile> pp_T5_two_fun_prime r : Prop"
    using r_type by (rule typed_pp_T5_two_fun_prime)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using F_type C_type by (rule has_type.Conj)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_pure[OF X_type] typed_pp_fun_prime[OF q_type]
      d_type Xq_type
    by (intro has_type.Conj has_type.Eq)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using Xd_type by (rule has_type.Neg)
  have Er_type: "\<Gamma> \<turnstile> ?Er : Prop"
    using q_type r_type by (rule has_type.Eq)
  have Enr_type: "\<Gamma> \<turnstile> ?Enr : Prop"
    using q_type has_type.Neg[OF r_type] by (rule has_type.Eq)
  have d_H:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using H_type by (intro CEV_axiom_from.Assumption) simp
  have d_P:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have d_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime r"
    using d_H by (rule CEV_axiom_from_conj_left)
  have d_C:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T5_two_fun_prime r"
    using d_H by (rule CEV_axiom_from_conj_right)
  have d_pure_X:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty X"
    using d_P by (rule CEV_axiom_from_conj_left)
  have d_tail:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_fun_prime q) (Eq Prop ?d (App X q))"
    using d_P by (rule CEV_axiom_from_conj_right)
  have d_fun_q:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime q"
    using d_tail by (rule CEV_axiom_from_conj_left)
  have d_decomp:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?d (App X q)"
    using d_tail by (rule CEV_axiom_from_conj_right)
  have C_explicit_type:
    "\<Gamma> \<turnstile>
      Forall Prop
        (Imp
          (pp_fun_prime (Var 0))
          (Disj
            (Eq Prop (Var 0) (shift r))
            (Eq Prop (Var 0) (Neg (shift r))))) : Prop"
    using C_type unfolding pp_T5_two_fun_prime_def .
  have d_C_explicit:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall Prop
        (Imp
          (pp_fun_prime (Var 0))
          (Disj
            (Eq Prop (Var 0) (shift r))
            (Eq Prop (Var 0) (Neg (shift r)))))"
    using d_C unfolding pp_T5_two_fun_prime_def .
  have classification_raw:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 q
        (Imp
          (pp_fun_prime (Var 0))
          (Disj
            (Eq Prop (Var 0) (shift r))
            (Eq Prop (Var 0) (Neg (shift r)))))"
    using C_explicit_type q_type d_C_explicit
    by (rule CEV_axiom_from_UI_typed)
  have classification:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_fun_prime q) (Disj ?Er ?Enr)"
  proof -
    have subst_fun:
      "subst (case_nat q Var) (pp_fun_prime (Var 0)) =
        pp_fun_prime q"
      using subst0_pp_fun_prime_var0[of q]
      unfolding subst0_def .
    have subst_r:
      "subst (case_nat q Var) (rename Suc r) = r"
      using subst0_shift[of q r]
      unfolding subst0_def shift_def .
    show ?thesis
    using classification_raw
      by (simp add: subst0_def shift_def subst_fun subst_r)
  qed
  have disj:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Disj ?Er ?Enr"
    using d_fun_q classification by (rule CEV_axiom_from.MP)
  have left:
    "\<Gamma> ; T ; insert ?Er ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
  proof -
    let ?U = "insert ?Er ?S"
    have e_qr:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Er"
      using Er_type by (intro CEV_axiom_from.Assumption) simp
    have pure_X:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty X"
      using d_pure_X by (rule CEV_axiom_from_mono) simp
    have fun_r:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime r"
      using d_F by (rule CEV_axiom_from_mono) simp
    have decomp:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop ?d (App X q)"
      using d_decomp by (rule CEV_axiom_from_mono) simp
    have Xq_Xr:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App X q) (App X r)"
      using X_type q_type r_type e_qr
      unfolding pp_unary_ty_def
      by (rule CEV_axiom_from_eq_app_right)
    have Xr_Xq:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App X r) (App X q)"
      using
        has_type.App[OF X_type[unfolded pp_unary_ty_def] q_type]
        has_type.App[OF X_type[unfolded pp_unary_ty_def] r_type]
        Xq_Xr
      by (rule CEV_axiom_from_eq_sym)
    have Xq_d:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App X q) ?d"
      using d_type Xq_type decomp by (rule CEV_axiom_from_eq_sym)
    have same:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App X r) (App ?D r)"
      using
        has_type.App[OF X_type[unfolded pp_unary_ty_def] r_type]
        Xq_type d_type Xr_Xq Xq_d
      by (rule CEV_axiom_from_eq_trans)
    have pure_D:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty ?D"
      using CEV_axiom_proves_mono[
        OF pp_T6_liar_pure core_T6]
      by (rule CEV_axiom_from.Theorem)
    have X_D:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty X ?D"
      using r_type X_type D_type fun_r pure_X pure_D same
      by (rule CEV_axiom_from_fun_prime)
    have Xd_Dd:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App X ?d) (App ?D ?d)"
      using X_type D_type d_type X_D
      by (rule CEV_axiom_from_pp_apply_cong_left)
    have not_Dd:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App ?D ?d)"
    proof -
      have rule:
        "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Imp (pp_fun_prime r) (Neg (App ?D ?d))"
        using CEV_T5_not_Dd[OF core r_type]
        by (rule CEV_axiom_from.Theorem)
      show ?thesis
        using fun_r rule by (rule CEV_axiom_from.MP)
    qed
    have neg_eq:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop
          (Neg (App X ?d))
          (Neg (App ?D ?d))"
      using Xd_type
        has_type.App[OF D_type[unfolded pp_unary_ty_def] d_type]
        Xd_Dd
      by (rule CEV_axiom_from_T5_neg_cong)
    have neg_eq_sym:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop
          (Neg (App ?D ?d))
          (Neg (App X ?d))"
      using
        has_type.Neg[OF Xd_type]
        has_type.Neg[
          OF has_type.App[
            OF D_type[unfolded pp_unary_ty_def] d_type]]
        neg_eq
      by (rule CEV_axiom_from_eq_sym)
    show ?thesis
      using
        has_type.Neg[
          OF has_type.App[
            OF D_type[unfolded pp_unary_ty_def] d_type]]
        has_type.Neg[OF Xd_type]
        not_Dd neg_eq_sym
      by (rule CEV_axiom_from_eq_prop_elim)
  qed
  have right:
    "\<Gamma> ; T ; insert ?Enr ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
  proof -
    let ?U = "insert ?Enr ?S"
    let ?Y = "pp_compose X ?N"
    have nr_type: "\<Gamma> \<turnstile> Neg r : Prop"
      using r_type by (rule has_type.Neg)
    have nd_type: "\<Gamma> \<turnstile> Neg ?d : Prop"
      using d_type by (rule has_type.Neg)
    have Y_type: "\<Gamma> \<turnstile> ?Y : pp_unary_ty"
      using X_type N_type by (rule typed_pp_compose)
    have e_qnr:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Enr"
      using Enr_type by (intro CEV_axiom_from.Assumption) simp
    have pure_X:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty X"
      using d_pure_X by (rule CEV_axiom_from_mono) simp
    have fun_r:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime r"
      using d_F by (rule CEV_axiom_from_mono) simp
    have decomp:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop ?d (App X q)"
      using d_decomp by (rule CEV_axiom_from_mono) simp
    have Xq_Xnr:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App X q) (App X (Neg r))"
      using X_type q_type nr_type e_qnr
      unfolding pp_unary_ty_def
      by (rule CEV_axiom_from_eq_app_right)
    have d_Xnr:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop ?d (App X (Neg r))"
      using d_type Xq_type
        has_type.App[OF X_type[unfolded pp_unary_ty_def] nr_type]
        decomp Xq_Xnr
      by (rule CEV_axiom_from_eq_trans)
    have Yr_Xnr:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App ?Y r) (App X (Neg r))"
    proof -
      have comp:
        "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Eq Prop
            (App ?Y r)
            (App X (App ?N r))"
        using CEV_pp_compose_apply_eq[OF X_type N_type r_type]
        by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
      have beta:
        "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Eq Prop (App ?N r) (Neg r)"
        using CEV_pp_negation_apply_eq[OF r_type]
        by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
      have under_X:
        "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Eq Prop
            (App X (App ?N r))
            (App X (Neg r))"
        using X_type
          has_type.App[
            OF N_type[unfolded pp_unary_ty_def] r_type]
          nr_type beta
        unfolding pp_unary_ty_def
        by (rule CEV_axiom_from_eq_app_right)
      show ?thesis
        using
          has_type.App[OF Y_type[unfolded pp_unary_ty_def] r_type]
          has_type.App[
            OF X_type[unfolded pp_unary_ty_def]
              has_type.App[
                OF N_type[unfolded pp_unary_ty_def] r_type]]
          has_type.App[
            OF X_type[unfolded pp_unary_ty_def] nr_type]
          comp under_X
        by (rule CEV_axiom_from_eq_trans)
    qed
    have Yr_d:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App ?Y r) ?d"
    proof -
      have Xnr_d:
        "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Eq Prop (App X (Neg r)) ?d"
        using d_type
          has_type.App[
            OF X_type[unfolded pp_unary_ty_def] nr_type]
          d_Xnr
        by (rule CEV_axiom_from_eq_sym)
      show ?thesis
        using
          has_type.App[OF Y_type[unfolded pp_unary_ty_def] r_type]
          has_type.App[
            OF X_type[unfolded pp_unary_ty_def] nr_type]
          d_type Yr_Xnr Xnr_d
        by (rule CEV_axiom_from_eq_trans)
    qed
    have pure_N_plus:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty ?N"
    proof (rule CEV_axiom_proves.Axiom)
      show "pp_pure pp_unary_ty ?N \<in> T"
        using pp_T6_negation_purity_axiom core_T6 by blast
      show "\<Gamma> \<turnstile> pp_pure pp_unary_ty ?N : Prop"
        using N_type by (rule typed_pp_pure)
    qed
    have pure_N:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty ?N"
      using pure_N_plus by (rule CEV_axiom_from.Theorem)
    have pure_Y:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty ?Y"
      using core_T6 X_type N_type pure_X pure_N
      by (rule pp_compose_pure_from)
    have pure_D:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty ?D"
      using CEV_axiom_proves_mono[
        OF pp_T6_liar_pure core_T6]
      by (rule CEV_axiom_from.Theorem)
    have Y_D:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty ?Y ?D"
      using r_type Y_type D_type fun_r pure_Y pure_D Yr_d
      by (rule CEV_axiom_from_fun_prime)
    have at_nd:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App ?Y (Neg ?d)) (App ?D (Neg ?d))"
      using Y_type D_type nd_type Y_D
      by (rule CEV_axiom_from_pp_apply_cong_left)
    have Ynd_Xd:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App ?Y (Neg ?d)) (App X ?d)"
      using CEV_axiom_from_T5_inner_neg_neg_apply_eq[
        OF X_type d_type, where T = T and S = ?U]
      by simp
    have Xd_Ynd:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App X ?d) (App ?Y (Neg ?d))"
      using
        has_type.App[
          OF Y_type[unfolded pp_unary_ty_def] nd_type]
        Xd_type Ynd_Xd
      by (rule CEV_axiom_from_eq_sym)
    have Xd_Q:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App X ?d) (App ?D (Neg ?d))"
      using Xd_type
        has_type.App[
          OF Y_type[unfolded pp_unary_ty_def] nd_type]
        has_type.App[
          OF D_type[unfolded pp_unary_ty_def] nd_type]
        Xd_Ynd at_nd
      by (rule CEV_axiom_from_eq_trans)
    have not_Q:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App ?D (Neg ?d))"
    proof -
      have rule:
        "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Imp
            (pp_fun_prime r)
            (Neg (App ?D (Neg ?d)))"
        using CEV_T5_not_D_neg_d[OF core r_type]
        by (rule CEV_axiom_from.Theorem)
      show ?thesis
        using fun_r rule by (rule CEV_axiom_from.MP)
    qed
    have neg_eq:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop
          (Neg (App X ?d))
          (Neg (App ?D (Neg ?d)))"
      using Xd_type
        has_type.App[
          OF D_type[unfolded pp_unary_ty_def] nd_type]
        Xd_Q
      by (rule CEV_axiom_from_T5_neg_cong)
    have neg_eq_sym:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop
          (Neg (App ?D (Neg ?d)))
          (Neg (App X ?d))"
      using
        has_type.Neg[OF Xd_type]
        has_type.Neg[
          OF has_type.App[
            OF D_type[unfolded pp_unary_ty_def] nd_type]]
        neg_eq
      by (rule CEV_axiom_from_eq_sym)
    show ?thesis
      using
        has_type.Neg[
          OF has_type.App[
            OF D_type[unfolded pp_unary_ty_def] nd_type]]
        has_type.Neg[OF Xd_type]
        not_Q neg_eq_sym
      by (rule CEV_axiom_from_eq_prop_elim)
  qed
  have d_R:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
    using Er_type Enr_type R_type disj left right
    by (rule CEV_axiom_from_T5_disj_cases)
  have P_imp_R:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?P ?R"
    using P_type d_R by (rule CEV_axiom_from_deduction)
  show ?thesis
    using H_type P_imp_R by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_T5_liar_true_from_two:
  assumes core: "pp_T5_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_fun_prime r)
        (pp_T5_two_fun_prime r))
      (App pp_T6_liar (App pp_T6_liar r))"
proof -
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?H = "Conj (pp_fun_prime r) (pp_T5_two_fun_prime r)"
  let ?M =
    "Imp
      (Conj
        (pp_pure pp_unary_ty (Var 1))
        (Conj
          (pp_fun_prime (Var 0))
          (Eq Prop
            (shift_by 2 ?d)
            (App (Var 1) (Var 0)))))
      (Neg (App (Var 1) (shift_by 2 ?d)))"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_fun_prime[OF r_type]
      typed_pp_T5_two_fun_prime[OF r_type]
    by (rule has_type.Conj)
  have r2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> shift_by 2 r : Prop"
  proof -
    have "[Prop, pp_unary_ty] @ \<Gamma> \<turnstile>
      shift_by (length [Prop, pp_unary_ty]) r : Prop"
      using r_type by (rule shift_by_preserves_typing)
    then show ?thesis by (simp add: numeral_2_eq_2)
  qed
  have X2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> Var 1 : pp_unary_ty"
    by (rule has_type.Var) (simp add: lookup_def)
  have q2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have parameter:
    "Prop # pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (shift_by 2 ?H)
        ?M"
  proof -
    have raw:
      "Prop # pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (Conj
            (pp_fun_prime (shift_by 2 r))
            (pp_T5_two_fun_prime (shift_by 2 r)))
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 1))
              (Conj
                (pp_fun_prime (Var 0))
                (Eq Prop
                  (App pp_T6_liar (shift_by 2 r))
                  (App (Var 1) (Var 0)))))
            (Neg
              (App (Var 1)
                (App pp_T6_liar (shift_by 2 r)))))"
      using core r2_type X2_type q2_type
      by (rule CEV_T5_liar_matrix_from_two)
    have shift_d:
      "shift_by 2 ?d = App pp_T6_liar (shift_by 2 r)"
    proof -
      have d_shift:
        "shift (shift ?d) =
          App pp_T6_liar (shift (shift r))"
        by (simp add: shift_pp_T6_liar)
      show ?thesis
        using d_shift
          shift_shift_eq_shift_by_2[of ?d]
          shift_shift_eq_shift_by_2[of r]
        by simp
    qed
    have shift_H:
      "shift_by 2 ?H =
        Conj
          (pp_fun_prime (shift_by 2 r))
          (pp_T5_two_fun_prime (shift_by 2 r))"
    proof -
      have h_shift:
        "shift (shift ?H) =
          Conj
            (pp_fun_prime (shift (shift r)))
            (pp_T5_two_fun_prime (shift (shift r)))"
        by simp
      show ?thesis
        using h_shift
          shift_shift_eq_shift_by_2[of ?H]
          shift_shift_eq_shift_by_2[of r]
        by simp
    qed
    show ?thesis
      using raw by (simp only: shift_d shift_H)
  qed
  have parameter_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile>
      Imp (shift_by 2 ?H) ?M : Prop"
    using parameter by (rule CEV_axiom_proves_formula)
  have M_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?M : Prop"
    using parameter_type by (auto elim: has_type.cases)
  have H1_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift ?H : Prop"
    using H_type by (rule typed_shift_ctx)
  have inner:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?H) (Forall Prop ?M)"
  proof (rule CEV_axiom_proves.Gen)
    show "pp_unary_ty # \<Gamma> \<turnstile> shift ?H : Prop"
      by (rule H1_type)
    show "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?M : Prop"
      by (rule M_type)
    show "Prop # pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (shift ?H)) ?M"
      using parameter
        shift_shift_eq_shift_by_2[of ?H]
      by simp
  qed
  have forall_type:
    "pp_unary_ty # \<Gamma> \<turnstile> Forall Prop ?M : Prop"
    using M_type by (rule has_type.Forall)
  have outer:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?H (Forall pp_unary_ty (Forall Prop ?M))"
  proof (rule CEV_axiom_proves.Gen)
    show "\<Gamma> \<turnstile> ?H : Prop" by (rule H_type)
    show "pp_unary_ty # \<Gamma> \<turnstile> Forall Prop ?M : Prop"
      by (rule forall_type)
    show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?H) (Forall Prop ?M)"
      by (rule inner)
  qed
  have liar_at_rule:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?H (pp_T5_liar_at ?d)"
    using outer by (simp only: pp_T5_liar_at_explicit)
  let ?L = "pp_T5_liar_at ?d"
  let ?P = "App ?D ?d"
  have L_type: "\<Gamma> \<turnstile> ?L : Prop"
    using d_type by (rule typed_pp_T5_liar_at)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using D_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have d_H:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using H_type by (intro CEV_axiom_from.Assumption) simp
  have local_rule:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?H ?L"
    using liar_at_rule by (rule CEV_axiom_from.Theorem)
  have d_L:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?L"
    using d_H local_rule by (rule CEV_axiom_from.MP)
  have PL:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?P ?L"
    using CEV_pp_T6_liar_apply_eq[OF d_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have LP:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?L ?P"
    using P_type L_type PL by (rule CEV_axiom_from_eq_sym)
  have d_P:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using L_type P_type d_L LP
    by (rule CEV_axiom_from_eq_prop_elim)
  show ?thesis
    using H_type d_P by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_Goodman_T5_no_two_fun_prime:
  assumes core: "pp_T5_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg (pp_T5_two_fun_prime r))"
proof -
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?P = "App ?D ?d"
  let ?F = "pp_fun_prime r"
  let ?C = "pp_T5_two_fun_prime r"
  let ?H = "Conj ?F ?C"
  let ?S = "insert ?C {?F}"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using D_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using r_type by (rule typed_pp_T5_two_fun_prime)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using F_type C_type by (rule has_type.Conj)
  have d_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_C:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?C"
    using C_type by (intro CEV_axiom_from.Assumption) simp
  have d_H:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using d_F d_C by (rule CEV_axiom_from_conj_intro)
  have true_rule:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?H ?P"
    using CEV_T5_liar_true_from_two[OF core r_type]
    by (rule CEV_axiom_from.Theorem)
  have d_P:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using d_H true_rule by (rule CEV_axiom_from.MP)
  have not_rule:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F (Neg ?P)"
    using CEV_T5_not_Dd[OF core r_type]
    by (rule CEV_axiom_from.Theorem)
  have not_P:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?P"
    using d_F not_rule by (rule CEV_axiom_from.MP)
  have false:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_P not_P by (rule CEV_axiom_from_contradiction)
  have C_imp_false:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?C ObjFalse"
    using C_type false by (rule CEV_axiom_from_deduction)
  have to_neg:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?C ObjFalse) (Neg ?C)"
    using CEV_proves_imp_false_to_neg[OF C_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have not_C:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?C"
    using C_imp_false to_neg by (rule CEV_axiom_from.MP)
  show ?thesis
    using F_type not_C by (rule CEV_axiom_from_singleton_imp)
qed

subsection \<open>The explicit proliferation theorem\<close>

lemma CEV_axiom_imp_trans_plus:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and AB: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
    and BC: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp B C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A C"
proof -
  have taut:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp A B)
        (Imp (Imp B C) (Imp A C))"
    using A_type B_type C_type
    by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
        C_proves.H H_proves.PC prop_tautology_imp_trans)
  have step:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp B C) (Imp A C)"
    using AB taut by (rule CEV_axiom_proves.MP)
  show ?thesis
    using BC step by (rule CEV_axiom_proves.MP)
qed

lemma CEV_axiom_exists_mono:
  assumes A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and B_type: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and AB:
      "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Exists \<sigma> A) (Exists \<sigma> B)"
proof -
  let ?Q = "Exists \<sigma> B"
  have Q_type: "\<Gamma> \<turnstile> ?Q : Prop"
    using B_type by (rule has_type.Exists)
  have shift_Q_type: "\<sigma> # \<Gamma> \<turnstile> shift ?Q : Prop"
    using Q_type by (rule typed_shift_ctx)
  have lift_B_type:
    "\<sigma> # \<sigma> # \<Gamma> \<turnstile>
      rename (lift_ren Suc) B : Prop"
    using B_type
    by (rule renaming_preserves_typing) (case_tac n; simp)
  have var0_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by (rule typed_var0)
  have B_to_shift_Q:
    "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp B (shift ?Q)"
  proof -
    have subst_lift:
      "subst0 (Var 0) (rename (lift_ren Suc) B) = B"
      by (rule subst0_rename_lift_Suc_var0)
    have shift_Q:
      "shift ?Q = Exists \<sigma> (rename (lift_ren Suc) B)"
      by (simp add: shift_def)
    have eg:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (subst0 (Var 0) (rename (lift_ren Suc) B))
          (Exists \<sigma> (rename (lift_ren Suc) B))"
      using lift_B_type var0_type
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.EG)
    show ?thesis
      using eg by (simp only: subst_lift shift_Q CEV_axiom_proves.Base)
  qed
  have A_to_shift_Q:
    "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp A (shift ?Q)"
    using A_type B_type shift_Q_type AB B_to_shift_Q
    by (rule CEV_axiom_imp_trans_plus)
  show ?thesis
    using A_type Q_type A_to_shift_Q
    by (rule CEV_axiom_proves.Inst)
qed

theorem CEV_Goodman_T5_proliferation:
  assumes core: "pp_T5_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (pp_T5_proliferation r)"
proof -
  let ?F = "pp_fun_prime r"
  let ?C = "pp_T5_two_fun_prime r"
  let ?A =
    "Imp
      (pp_fun_prime (Var 0))
      (Disj
        (Eq Prop (Var 0) (shift r))
        (Eq Prop (Var 0) (Neg (shift r))))"
  let ?B =
    "Conj
      (pp_fun_prime (Var 0))
      (Conj
        (Neg (Eq Prop (Var 0) (shift r)))
        (Neg (Eq Prop (Var 0) (Neg (shift r)))))"
  let ?E1 = "Exists Prop (Neg ?A)"
  let ?E2 = "Exists Prop ?B"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using r_type by (rule typed_pp_T5_two_fun_prime)
  have A_type: "Prop # \<Gamma> \<turnstile> ?A : Prop"
  proof -
    have q_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    have r_shift: "Prop # \<Gamma> \<turnstile> shift r : Prop"
      using r_type by (rule typed_shift_ctx)
    show ?thesis
      using typed_pp_fun_prime[OF q_type] q_type r_shift
      by (intro has_type.Imp has_type.Disj has_type.Eq has_type.Neg)
  qed
  have B_type: "Prop # \<Gamma> \<turnstile> ?B : Prop"
  proof -
    have q_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    have r_shift: "Prop # \<Gamma> \<turnstile> shift r : Prop"
      using r_type by (rule typed_shift_ctx)
    show ?thesis
      using typed_pp_fun_prime[OF q_type] q_type r_shift
      by (intro has_type.Conj has_type.Neg has_type.Eq)
  qed
  have E1_type: "\<Gamma> \<turnstile> ?E1 : Prop"
    using has_type.Neg[OF A_type] by (rule has_type.Exists)
  have E2_type: "\<Gamma> \<turnstile> ?E2 : Prop"
    using B_type by (rule has_type.Exists)
  have no_two:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?F (Neg ?C)"
    using core r_type by (rule CEV_Goodman_T5_no_two_fun_prime)
  have not_forall:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Neg ?C) ?E1"
  proof -
    have base:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Neg (Forall Prop ?A)) ?E1"
      using A_type
      by (intro CEV_proves.CE CE_proves.C C_proves.H
          H_proves_not_forall_imp_exists_neg)
    show ?thesis
      using base unfolding pp_T5_two_fun_prime_def
      by (rule CEV_axiom_proves.Base)
  qed
  have body_transform:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Neg ?A) ?B"
  proof (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.H H_proves.PC)
    have formula_type:
      "Prop # \<Gamma> \<turnstile> Imp (Neg ?A) ?B : Prop"
      using A_type B_type by auto
    show "prop_tautology (Prop # \<Gamma>) (Imp (Neg ?A) ?B)"
      unfolding prop_tautology_def
      using formula_type by auto
  qed
  have exists_transform:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?E1 ?E2"
    using has_type.Neg[OF A_type] B_type body_transform
    by (rule CEV_axiom_exists_mono)
  have first:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?F ?E1"
    using F_type has_type.Neg[OF C_type] E1_type no_two not_forall
    by (rule CEV_axiom_imp_trans_plus)
  have final:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?F ?E2"
    using F_type E1_type E2_type first exists_transform
    by (rule CEV_axiom_imp_trans_plus)
  show ?thesis
    using final unfolding pp_T5_proliferation_def .
qed

theorem CEV_Goodman_T5:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; pp_T5_axioms \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (pp_T5_proliferation r)"
  using subset_refl r_type by (rule CEV_Goodman_T5_proliferation)

corollary CEV_Goodman_T5_mono:
  assumes core: "pp_T5_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (pp_T5_proliferation r)"
  using core r_type by (rule CEV_Goodman_T5_proliferation)

end
