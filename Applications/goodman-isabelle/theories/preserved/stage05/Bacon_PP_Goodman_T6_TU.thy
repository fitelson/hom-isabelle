theory Bacon_PP_Goodman_T6_TU
  imports 
    "Goodman_Legacy_05.Bacon_PP_Goodman_T6_Inv"
begin

section \<open>Goodman T6 from truth-uniformity\<close>

text \<open>
  Truth-uniformity classifies a pure reversible operator by its uniform
  action on truth values, not by identity at the proposition type.  The
  distinction matters intensionally: neither branch licenses replacing
  \<open>Zp\<close> by \<open>p\<close> or \<open>\<not>p\<close> inside the liar operator.
\<close>

definition pp_truth_preserving :: "oterm \<Rightarrow> oterm" where
  "pp_truth_preserving Z =
    Forall Prop
      (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0)"

definition pp_truth_flipping :: "oterm \<Rightarrow> oterm" where
  "pp_truth_flipping Z =
    Forall Prop
      (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Neg (Var 0))"

definition pp_TU :: oterm where
  "pp_TU =
    Forall pp_unary_ty
      (Imp
        (pp_group_member (Var 0))
        (Disj
          (pp_truth_preserving (Var 0))
          (pp_truth_flipping (Var 0))))"

definition pp_T6_TU_axioms :: "oterm set" where
  "pp_T6_TU_axioms =
    insert pp_TU
      (insert pp_L2
        (insert pp_exists_fun_prime pp_T6_core_PP_axioms))"

lemma typed_pp_truth_preserving:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_truth_preserving Z : Prop"
proof -
  have Z_shift:
    "Prop # \<Gamma> \<turnstile> shift Z : pp_unary_ty"
    using Z_type by (rule typed_shift_ctx)
  have p_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have Zp_type:
    "Prop # \<Gamma> \<turnstile> App (shift Z) (Var 0) : Prop"
    using Z_shift p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_truth_preserving_def
    using Zp_type p_type
    by (intro has_type.Forall has_type.Conj has_type.Imp)
qed

lemma typed_pp_truth_flipping:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_truth_flipping Z : Prop"
proof -
  have Z_shift:
    "Prop # \<Gamma> \<turnstile> shift Z : pp_unary_ty"
    using Z_type by (rule typed_shift_ctx)
  have p_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have Zp_type:
    "Prop # \<Gamma> \<turnstile> App (shift Z) (Var 0) : Prop"
    using Z_shift p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_truth_flipping_def
    using Zp_type p_type
    by (intro has_type.Forall has_type.Conj has_type.Imp has_type.Neg)
qed

lemma typed_pp_TU:
  "\<Gamma> \<turnstile> pp_TU : Prop"
  unfolding pp_TU_def
  using typed_pp_group_member[
      of "pp_unary_ty # \<Gamma>" "Var 0"]
    typed_pp_truth_preserving[
      of "pp_unary_ty # \<Gamma>" "Var 0"]
    typed_pp_truth_flipping[
      of "pp_unary_ty # \<Gamma>" "Var 0"]
  by (intro has_type.Forall has_type.Imp has_type.Disj has_type.Var)
    (simp_all add: lookup_def)

lemma subst_pp_truth_preserving[simp]:
  "subst s (pp_truth_preserving Z) =
    pp_truth_preserving (subst s Z)"
  by (simp add: pp_truth_preserving_def subst_lift_shift)

lemma subst_pp_truth_flipping[simp]:
  "subst s (pp_truth_flipping Z) =
    pp_truth_flipping (subst s Z)"
  by (simp add: pp_truth_flipping_def subst_lift_shift)

lemma rename_pp_pure_term_TU[simp]:
  "rename r (pp_pure \<sigma> X) =
    pp_pure \<sigma> (rename r X)"
  by (simp add: pp_pure_def pp_Pure_def)

lemma rename_pp_identity_operator_TU[simp]:
  "rename r pp_identity_operator = pp_identity_operator"
  by (simp add: pp_identity_operator_def)

lemma rename_pp_reversible_term[simp]:
  "rename r (pp_reversible Z) =
    pp_reversible (rename r Z)"
  by (simp add: pp_reversible_def rename_pp_compose
      shift_rename_lift)

lemma rename_pp_group_member_term[simp]:
  "rename r (pp_group_member Z) =
    pp_group_member (rename r Z)"
  by (simp add: pp_group_member_def)

lemma rename_pp_truth_preserving_term[simp]:
  "rename r (pp_truth_preserving Z) =
    pp_truth_preserving (rename r Z)"
  by (simp add: pp_truth_preserving_def shift_rename_lift)

lemma rename_pp_truth_flipping_term[simp]:
  "rename r (pp_truth_flipping Z) =
    pp_truth_flipping (rename r Z)"
  by (simp add: pp_truth_flipping_def shift_rename_lift)

lemma shift_pp_group_member_TU[simp]:
  "shift (pp_group_member Z) = pp_group_member (shift Z)"
  by (simp add: shift_def)

lemma shift_pp_truth_preserving_TU[simp]:
  "shift (pp_truth_preserving Z) = pp_truth_preserving (shift Z)"
  by (simp add: shift_def)

lemma shift_pp_truth_flipping_TU[simp]:
  "shift (pp_truth_flipping Z) = pp_truth_flipping (shift Z)"
  by (simp add: shift_def)

lemma shift_Neg_term_TU[simp]:
  "shift (Neg A) = Neg (shift A)"
  by (simp add: shift_def)

lemma CEV_axiom_TU_instance:
  assumes TU_in: "pp_TU \<in> T"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_group_member Z)
      (Disj
        (pp_truth_preserving Z)
        (pp_truth_flipping Z))"
proof -
  have TU_type: "\<Gamma> \<turnstile> pp_TU : Prop"
    by (rule typed_pp_TU)
  have d_TU: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_TU"
    using TU_in TU_type by (rule CEV_axiom_proves.Axiom)
  have raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 Z
        (Imp
          (pp_group_member (Var 0))
          (Disj
            (pp_truth_preserving (Var 0))
            (pp_truth_flipping (Var 0))))"
    using TU_type Z_type d_TU
    unfolding pp_TU_def
    by (rule CEV_axiom_UI_typed)
  show ?thesis
    using raw by (simp add: subst0_def)
qed

lemma CEV_axiom_truth_preserving_instance:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_truth_preserving Z)
      (App Z p \<longleftrightarrow>\<^sub>o p)"
proof -
  have preserving_type:
    "\<Gamma> \<turnstile> pp_truth_preserving Z : Prop"
    using Z_type by (rule typed_pp_truth_preserving)
  have d:
    "\<Gamma> ; T ; {pp_truth_preserving Z}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_truth_preserving Z"
    using preserving_type
    by (intro CEV_axiom_from.Assumption) simp
  have raw:
    "\<Gamma> ; T ; {pp_truth_preserving Z} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 p
        (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0)"
  proof (rule CEV_axiom_from_UI_typed)
    show "\<Gamma> \<turnstile>
      Forall Prop
        (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0) : Prop"
      using preserving_type
      unfolding pp_truth_preserving_def .
    show "\<Gamma> \<turnstile> p : Prop" by (rule p_type)
    show "\<Gamma> ; T ; {pp_truth_preserving Z}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Forall Prop
          (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Var 0)"
      using d unfolding pp_truth_preserving_def .
  qed
  have inst:
    "\<Gamma> ; T ; {pp_truth_preserving Z} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (App Z p \<longleftrightarrow>\<^sub>o p)"
    using raw
    by (simp add: subst0_def
        subst0_shift[of p Z, unfolded subst0_def])
  show ?thesis
    using preserving_type inst by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_axiom_truth_flipping_instance:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_truth_flipping Z)
      (App Z p \<longleftrightarrow>\<^sub>o Neg p)"
proof -
  have flipping_type:
    "\<Gamma> \<turnstile> pp_truth_flipping Z : Prop"
    using Z_type by (rule typed_pp_truth_flipping)
  have d:
    "\<Gamma> ; T ; {pp_truth_flipping Z}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_truth_flipping Z"
    using flipping_type
    by (intro CEV_axiom_from.Assumption) simp
  have raw:
    "\<Gamma> ; T ; {pp_truth_flipping Z} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 p
        (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Neg (Var 0))"
  proof (rule CEV_axiom_from_UI_typed)
    show "\<Gamma> \<turnstile>
      Forall Prop
        (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Neg (Var 0)) :
          Prop"
      using flipping_type
      unfolding pp_truth_flipping_def .
    show "\<Gamma> \<turnstile> p : Prop" by (rule p_type)
    show "\<Gamma> ; T ; {pp_truth_flipping Z}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Forall Prop
          (App (shift Z) (Var 0) \<longleftrightarrow>\<^sub>o Neg (Var 0))"
      using d unfolding pp_truth_flipping_def .
  qed
  have inst:
    "\<Gamma> ; T ; {pp_truth_flipping Z} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (App Z p \<longleftrightarrow>\<^sub>o Neg p)"
    using raw
    by (simp add: subst0_def
        subst0_shift[of p Z, unfolded subst0_def])
  show ?thesis
    using flipping_type inst by (rule CEV_axiom_from_singleton_imp)
qed

subsection \<open>The truth-preserving diagonal\<close>

lemma CEV_T6_TU_preserving_diagonal_false:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Imp
        (pp_group_member Z)
        (Imp
          (pp_truth_preserving Z)
          (Neg
            (App pp_T6_liar
              (App Z (App pp_T6_liar r))))))"
proof -
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?p = "App Z ?d"
  let ?A = "App ?D ?p"
  let ?X = "pp_compose Z ?D"
  let ?Za = "App Z ?A"
  let ?F = "pp_fun_prime r"
  let ?G = "pp_group_member Z"
  let ?TP = "pp_truth_preserving Z"
  let ?Base = "insert ?TP (insert ?G {?F})"
  let ?S = "insert ?A ?Base"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have p_type: "\<Gamma> \<turnstile> ?p : Prop"
    using Z_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using D_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have X_type: "\<Gamma> \<turnstile> ?X : pp_unary_ty"
    using Z_type D_type by (rule typed_pp_compose)
  have Za_type: "\<Gamma> \<turnstile> ?Za : Prop"
    using Z_type A_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have G_type: "\<Gamma> \<turnstile> ?G : Prop"
    using Z_type by (rule typed_pp_group_member)
  have TP_type: "\<Gamma> \<turnstile> ?TP : Prop"
    using Z_type by (rule typed_pp_truth_preserving)
  have d_A:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    using A_type by (intro CEV_axiom_from.Assumption) simp
  have d_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_G:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?G"
    using G_type by (intro CEV_axiom_from.Assumption) simp
  have d_TP:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?TP"
    using TP_type by (intro CEV_axiom_from.Assumption) simp
  have pure_Z:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty Z"
    using d_G unfolding pp_group_member_def
    by (rule CEV_axiom_from_conj_left)
  have pure_D:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?D"
    using CEV_axiom_proves_mono[OF pp_T6_liar_pure core]
    by (rule CEV_axiom_from.Theorem)
  have pure_X:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?X"
    using core Z_type D_type pure_Z pure_D
    by (rule pp_compose_pure_from)
  have Xr_eq:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?X r) ?p"
    using CEV_pp_compose_apply_eq[OF Z_type D_type r_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have decomposition:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?p (App ?X r)"
    using
      has_type.App[OF X_type[unfolded pp_unary_ty_def] r_type]
      p_type Xr_eq
    by (rule CEV_axiom_from_eq_sym)
  have not_Xp:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (App ?X ?p)"
    using p_type X_type r_type d_A pure_X d_F decomposition
    by (rule CEV_axiom_from_T5_liar_elim)
  have Xp_eq:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?X ?p) ?Za"
    using CEV_pp_compose_apply_eq[OF Z_type D_type p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have neg_eq:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg (App ?X ?p)) (Neg ?Za)"
    using
      has_type.App[OF X_type[unfolded pp_unary_ty_def] p_type]
      Za_type Xp_eq
    by (rule CEV_axiom_from_T5_neg_cong)
  have not_Za:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?Za"
    using
      has_type.Neg[
        OF has_type.App[OF X_type[unfolded pp_unary_ty_def] p_type]]
      has_type.Neg[OF Za_type] not_Xp neg_eq
    by (rule CEV_axiom_from_eq_prop_elim)
  have TP_rule:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?TP (?Za \<longleftrightarrow>\<^sub>o ?A)"
    using CEV_axiom_truth_preserving_instance[
      OF A_type Z_type, where T = T]
    by (rule CEV_axiom_from.Theorem)
  have TP_at_A:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?Za \<longleftrightarrow>\<^sub>o ?A)"
    using d_TP TP_rule by (rule CEV_axiom_from.MP)
  have A_to_Za:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?A ?Za"
    using TP_at_A by (rule CEV_axiom_from_conj_right)
  have d_Za:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Za"
    using d_A A_to_Za by (rule CEV_axiom_from.MP)
  have false:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_Za not_Za by (rule CEV_axiom_from_contradiction)
  have A_imp_false:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?A ObjFalse"
  proof (rule CEV_axiom_from_deduction)
    show "\<Gamma> \<turnstile> ?A : Prop" by (rule A_type)
    show "\<Gamma> ; T ; insert ?A ?Base
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
      by (rule false)
  qed
  have to_neg:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?A ObjFalse) (Neg ?A)"
    using CEV_proves_imp_false_to_neg[OF A_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have not_A:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?A"
    using A_imp_false to_neg by (rule CEV_axiom_from.MP)
  have under_G_F:
    "\<Gamma> ; T ; insert ?G {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?TP (Neg ?A)"
  proof (rule CEV_axiom_from_deduction)
    show "\<Gamma> \<turnstile> ?TP : Prop" by (rule TP_type)
    show "\<Gamma> ; T ; insert ?TP (insert ?G {?F})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?A"
      by (rule not_A)
  qed
  have under_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?G (Imp ?TP (Neg ?A))"
  proof (rule CEV_axiom_from_deduction)
    show "\<Gamma> \<turnstile> ?G : Prop" by (rule G_type)
    show "\<Gamma> ; T ; insert ?G {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?TP (Neg ?A)"
      by (rule under_G_F)
  qed
  show ?thesis
    using F_type under_F by (rule CEV_axiom_from_singleton_imp)
qed

subsection \<open>Cancellation through an explicit inverse\<close>

definition pp_inverse_witness :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_inverse_witness Z W =
    Conj
      (pp_pure pp_unary_ty W)
      (Conj
        (Eq pp_unary_ty
          (pp_compose Z W)
          pp_identity_operator)
        (Eq pp_unary_ty
          (pp_compose W Z)
          pp_identity_operator))"

lemma typed_pp_inverse_witness:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and W_type: "\<Gamma> \<turnstile> W : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_inverse_witness Z W : Prop"
  unfolding pp_inverse_witness_def
  using typed_pp_pure[OF W_type]
    typed_pp_compose[OF Z_type W_type]
    typed_pp_compose[OF W_type Z_type]
    typed_pp_identity_operator
  by (intro has_type.Conj has_type.Eq)

lemma subst_pp_inverse_witness[simp]:
  "subst s (pp_inverse_witness Z W) =
    pp_inverse_witness (subst s Z) (subst s W)"
  by (simp add: pp_inverse_witness_def)

lemma pp_reversible_as_inverse_witness:
  "pp_reversible Z =
    Exists pp_unary_ty
      (pp_inverse_witness (shift Z) (Var 0))"
  by (simp add: pp_reversible_def pp_inverse_witness_def)

lemma CEV_axiom_from_T6_inverse_cancel:
  assumes W_type: "\<Gamma> \<turnstile> W : pp_unary_ty"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and WZ:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (pp_compose W Z)
          pp_identity_operator"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App W (App Z p)) p"
proof -
  let ?C = "pp_compose W Z"
  let ?I = pp_identity_operator
  have C_type: "\<Gamma> \<turnstile> ?C : pp_unary_ty"
    using W_type Z_type by (rule typed_pp_compose)
  have I_type: "\<Gamma> \<turnstile> ?I : pp_unary_ty"
    by (rule typed_pp_identity_operator)
  have Zp_type: "\<Gamma> \<turnstile> App Z p : Prop"
    using Z_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have WZp_type: "\<Gamma> \<turnstile> App W (App Z p) : Prop"
    using W_type Zp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Cp_type: "\<Gamma> \<turnstile> App ?C p : Prop"
    using C_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Ip_type: "\<Gamma> \<turnstile> App ?I p : Prop"
    using I_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?C p) (App W (App Z p))"
    using CEV_pp_compose_apply_eq[OF W_type Z_type p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have beta_sym:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App W (App Z p)) (App ?C p)"
    using Cp_type WZp_type beta by (rule CEV_axiom_from_eq_sym)
  have congr:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?C p) (App ?I p)"
    using C_type I_type p_type WZ
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have first:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App W (App Z p)) (App ?I p)"
    using WZp_type Cp_type Ip_type beta_sym congr
    by (rule CEV_axiom_from_eq_trans)
  have id:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I p) p"
  proof (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
    show "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (App ?I p) p"
      using Ip_type p_type CEV_pp_identity_apply[OF p_type]
      by (rule CEV_zeroary_equivalence)
  qed
  show ?thesis
    using WZp_type Ip_type p_type first id
    by (rule CEV_axiom_from_eq_trans)
qed

lemma CEV_axiom_from_T6_conjugate_cancel:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and W_type: "\<Gamma> \<turnstile> W : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and WZ:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (pp_compose W Z)
          pp_identity_operator"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop
      (App
        (pp_compose Z (pp_compose pp_T6_liar W))
        (App Z p))
      (App Z (App pp_T6_liar p))"
proof -
  let ?D = pp_T6_liar
  let ?DW = "pp_compose ?D W"
  let ?Y = "pp_compose Z ?DW"
  let ?q = "App Z p"
  let ?DWq = "App ?DW ?q"
  let ?Wq = "App W ?q"
  let ?D_Wq = "App ?D ?Wq"
  let ?Z_DWq = "App Z ?DWq"
  let ?Z_D_Wq = "App Z ?D_Wq"
  let ?target = "App Z (App ?D p)"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have DW_type: "\<Gamma> \<turnstile> ?DW : pp_unary_ty"
    using D_type W_type by (rule typed_pp_compose)
  have Y_type: "\<Gamma> \<turnstile> ?Y : pp_unary_ty"
    using Z_type DW_type by (rule typed_pp_compose)
  have q_type: "\<Gamma> \<turnstile> ?q : Prop"
    using Z_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Wq_type: "\<Gamma> \<turnstile> ?Wq : Prop"
    using W_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have DWq_type: "\<Gamma> \<turnstile> ?DWq : Prop"
    using DW_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have D_Wq_type: "\<Gamma> \<turnstile> ?D_Wq : Prop"
    using D_type Wq_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Z_DWq_type: "\<Gamma> \<turnstile> ?Z_DWq : Prop"
    using Z_type DWq_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Z_D_Wq_type: "\<Gamma> \<turnstile> ?Z_D_Wq : Prop"
    using Z_type D_Wq_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have left_type: "\<Gamma> \<turnstile> App ?Y ?q : Prop"
    using Y_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Dp_type: "\<Gamma> \<turnstile> App ?D p : Prop"
    using D_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have target_type: "\<Gamma> \<turnstile> ?target : Prop"
    using Z_type Dp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have outer_beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?Y ?q) ?Z_DWq"
    using CEV_pp_compose_apply_eq[OF Z_type DW_type q_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have inner_beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?DWq ?D_Wq"
    using CEV_pp_compose_apply_eq[OF D_type W_type q_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have inner_cong:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?Z_DWq ?Z_D_Wq"
    using Z_type DWq_type D_Wq_type inner_beta
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have first:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?Y ?q) ?Z_D_Wq"
    using left_type Z_DWq_type Z_D_Wq_type outer_beta inner_cong
    by (rule CEV_axiom_from_eq_trans)
  have cancel:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?Wq p"
    using W_type Z_type p_type WZ
    by (rule CEV_axiom_from_T6_inverse_cancel)
  have D_cong:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?D_Wq (App ?D p)"
    using D_type Wq_type p_type cancel
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have Z_cong:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?Z_D_Wq ?target"
    using Z_type D_Wq_type Dp_type D_cong
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  show ?thesis
    using left_type Z_D_Wq_type target_type first Z_cong
    by (rule CEV_axiom_from_eq_trans)
qed

subsection \<open>The truth-flipping diagonal\<close>

lemma CEV_T6_TU_flipping_diagonal_false_with_inverse:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and W_type: "\<Gamma> \<turnstile> W : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_inverse_witness Z W)
      (Imp
        (pp_fun_prime r)
        (Imp
          (pp_group_member Z)
          (Imp
            (pp_truth_flipping Z)
            (Neg
              (App pp_T6_liar
                (App Z (App pp_T6_liar r)))))))"
proof -
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?p = "App Z ?d"
  let ?A = "App ?D ?p"
  let ?DW = "pp_compose ?D W"
  let ?Y = "pp_compose Z ?DW"
  let ?q = "App Z r"
  let ?ZDd = "App Z (App ?D ?d)"
  let ?WB = "pp_inverse_witness Z W"
  let ?F = "pp_fun_prime r"
  let ?G = "pp_group_member Z"
  let ?TF = "pp_truth_flipping Z"
  let ?Base = "insert ?TF (insert ?G (insert ?F {?WB}))"
  let ?WithA = "insert ?A ?Base"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have p_type: "\<Gamma> \<turnstile> ?p : Prop"
    using Z_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using D_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have DW_type: "\<Gamma> \<turnstile> ?DW : pp_unary_ty"
    using D_type W_type by (rule typed_pp_compose)
  have Y_type: "\<Gamma> \<turnstile> ?Y : pp_unary_ty"
    using Z_type DW_type by (rule typed_pp_compose)
  have q_type: "\<Gamma> \<turnstile> ?q : Prop"
    using Z_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Dd_type: "\<Gamma> \<turnstile> App ?D ?d : Prop"
    using D_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have ZDd_type: "\<Gamma> \<turnstile> ?ZDd : Prop"
    using Z_type Dd_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have WB_type: "\<Gamma> \<turnstile> ?WB : Prop"
    using Z_type W_type by (rule typed_pp_inverse_witness)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have G_type: "\<Gamma> \<turnstile> ?G : Prop"
    using Z_type by (rule typed_pp_group_member)
  have TF_type: "\<Gamma> \<turnstile> ?TF : Prop"
    using Z_type by (rule typed_pp_truth_flipping)
  have d_A:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    using A_type by (intro CEV_axiom_from.Assumption) simp
  have d_WB:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?WB"
    using WB_type by (intro CEV_axiom_from.Assumption) simp
  have d_F:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_G:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?G"
    using G_type by (intro CEV_axiom_from.Assumption) simp
  have d_TF:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?TF"
    using TF_type by (intro CEV_axiom_from.Assumption) simp
  have pure_W:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty W"
    using d_WB unfolding pp_inverse_witness_def
    by (rule CEV_axiom_from_conj_left)
  have inverse_pair:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (Eq pp_unary_ty
          (pp_compose Z W)
          pp_identity_operator)
        (Eq pp_unary_ty
          (pp_compose W Z)
          pp_identity_operator)"
    using d_WB unfolding pp_inverse_witness_def
    by (rule CEV_axiom_from_conj_right)
  have WZ:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty
        (pp_compose W Z)
        pp_identity_operator"
    using inverse_pair by (rule CEV_axiom_from_conj_right)
  have pure_Z:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty Z"
    using d_G unfolding pp_group_member_def
    by (rule CEV_axiom_from_conj_left)
  have pure_D:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?D"
    using CEV_axiom_proves_mono[OF pp_T6_liar_pure core]
    by (rule CEV_axiom_from.Theorem)
  have pure_DW:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?DW"
    using core D_type W_type pure_D pure_W
    by (rule pp_compose_pure_from)
  have pure_Y:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?Y"
    using core Z_type DW_type pure_Z pure_DW
    by (rule pp_compose_pure_from)
  have fun_pair:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj ?F ?G"
    using d_F d_G by (rule CEV_axiom_from_conj_intro)
  have fun_rule:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Conj ?F ?G) (pp_fun_prime ?q)"
    using CEV_fun_prime_under_group_member[
      OF core r_type Z_type]
    by (rule CEV_axiom_from.Theorem)
  have fun_q:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime ?q"
    using fun_pair fun_rule by (rule CEV_axiom_from.MP)
  have Yq_eq:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?Y ?q) ?p"
    using Z_type W_type r_type WZ
    by (rule CEV_axiom_from_T6_conjugate_cancel)
  have decomposition:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?p (App ?Y ?q)"
    using
      has_type.App[OF Y_type[unfolded pp_unary_ty_def] q_type]
      p_type Yq_eq
    by (rule CEV_axiom_from_eq_sym)
  have not_Yp:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (App ?Y ?p)"
    using p_type Y_type q_type d_A pure_Y fun_q decomposition
    by (rule CEV_axiom_from_T5_liar_elim)
  have Yp_eq:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?Y ?p) ?ZDd"
    using Z_type W_type d_type WZ
    by (rule CEV_axiom_from_T6_conjugate_cancel)
  have neg_eq:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg (App ?Y ?p)) (Neg ?ZDd)"
    using
      has_type.App[OF Y_type[unfolded pp_unary_ty_def] p_type]
      ZDd_type Yp_eq
    by (rule CEV_axiom_from_T5_neg_cong)
  have not_ZDd:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?ZDd"
    using
      has_type.Neg[
        OF has_type.App[OF Y_type[unfolded pp_unary_ty_def] p_type]]
      has_type.Neg[OF ZDd_type] not_Yp neg_eq
    by (rule CEV_axiom_from_eq_prop_elim)
  have core_T5: "pp_T5_axioms \<subseteq> T"
    using core unfolding pp_T5_axioms_def .
  have not_Dd_rule:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F (Neg (App ?D ?d))"
    using CEV_T5_not_Dd[OF core_T5 r_type]
    by (rule CEV_axiom_from.Theorem)
  have not_Dd:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (App ?D ?d)"
    using d_F not_Dd_rule by (rule CEV_axiom_from.MP)
  have TF_rule:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?TF
        (?ZDd \<longleftrightarrow>\<^sub>o Neg (App ?D ?d))"
    using CEV_axiom_truth_flipping_instance[
      OF Dd_type Z_type, where T = T]
    by (rule CEV_axiom_from.Theorem)
  have TF_at_Dd:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      (?ZDd \<longleftrightarrow>\<^sub>o Neg (App ?D ?d))"
    using d_TF TF_rule by (rule CEV_axiom_from.MP)
  have not_Dd_to_ZDd:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Neg (App ?D ?d)) ?ZDd"
    using TF_at_Dd by (rule CEV_axiom_from_conj_right)
  have d_ZDd:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?ZDd"
    using not_Dd not_Dd_to_ZDd by (rule CEV_axiom_from.MP)
  have false:
    "\<Gamma> ; T ; ?WithA \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_ZDd not_ZDd by (rule CEV_axiom_from_contradiction)
  have A_imp_false:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?A ObjFalse"
  proof (rule CEV_axiom_from_deduction)
    show "\<Gamma> \<turnstile> ?A : Prop" by (rule A_type)
    show "\<Gamma> ; T ; insert ?A ?Base
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
      by (rule false)
  qed
  have to_neg:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?A ObjFalse) (Neg ?A)"
    using CEV_proves_imp_false_to_neg[OF A_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have not_A:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?A"
    using A_imp_false to_neg by (rule CEV_axiom_from.MP)
  have under_G_F_WB:
    "\<Gamma> ; T ; insert ?G (insert ?F {?WB})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?TF (Neg ?A)"
  proof (rule CEV_axiom_from_deduction)
    show "\<Gamma> \<turnstile> ?TF : Prop" by (rule TF_type)
    show "\<Gamma> ; T ; insert ?TF (insert ?G (insert ?F {?WB}))
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?A"
      by (rule not_A)
  qed
  have under_F_WB:
    "\<Gamma> ; T ; insert ?F {?WB} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?G (Imp ?TF (Neg ?A))"
  proof (rule CEV_axiom_from_deduction)
    show "\<Gamma> \<turnstile> ?G : Prop" by (rule G_type)
    show "\<Gamma> ; T ; insert ?G (insert ?F {?WB})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?TF (Neg ?A)"
      by (rule under_G_F_WB)
  qed
  have under_WB:
    "\<Gamma> ; T ; {?WB} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F (Imp ?G (Imp ?TF (Neg ?A)))"
  proof (rule CEV_axiom_from_deduction)
    show "\<Gamma> \<turnstile> ?F : Prop" by (rule F_type)
    show "\<Gamma> ; T ; insert ?F {?WB} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?G (Imp ?TF (Neg ?A))"
      by (rule under_F_WB)
  qed
  show ?thesis
    using WB_type under_WB by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_T6_TU_flipping_diagonal_false:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Imp
        (pp_group_member Z)
        (Imp
          (pp_truth_flipping Z)
          (Neg
            (App pp_T6_liar
              (App Z (App pp_T6_liar r))))))"
proof -
  let ?D = pp_T6_liar
  let ?A = "App ?D (App Z (App ?D r))"
  let ?F = "pp_fun_prime r"
  let ?G = "pp_group_member Z"
  let ?TF = "pp_truth_flipping Z"
  let ?Target = "Imp ?F (Imp ?G (Imp ?TF (Neg ?A)))"
  let ?W = "Var 0"
  let ?Zs = "shift Z"
  let ?WB = "pp_inverse_witness ?Zs ?W"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have G_type: "\<Gamma> \<turnstile> ?G : Prop"
    using Z_type by (rule typed_pp_group_member)
  have TF_type: "\<Gamma> \<turnstile> ?TF : Prop"
    using Z_type by (rule typed_pp_truth_flipping)
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have d_type: "\<Gamma> \<turnstile> App ?D r : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Zd_type: "\<Gamma> \<turnstile> App Z (App ?D r) : Prop"
    using Z_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using D_type Zd_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Target_type: "\<Gamma> \<turnstile> ?Target : Prop"
    using F_type G_type TF_type A_type
    by (intro has_type.Imp has_type.Neg)
  have Zs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Zs : pp_unary_ty"
    using Z_type by (rule typed_shift_ctx)
  have W_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?W : pp_unary_ty"
    by (rule typed_var0)
  have WB_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?WB : Prop"
    using Zs_type W_type by (rule typed_pp_inverse_witness)
  have r_shift_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have bound:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?WB (shift ?Target)"
  proof -
    have d:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?WB
          (Imp
            (pp_fun_prime (shift r))
            (Imp
              (pp_group_member ?Zs)
              (Imp
                (pp_truth_flipping ?Zs)
                (Neg
                  (App ?D
                    (App ?Zs (App ?D (shift r))))))))"
      using CEV_T6_TU_flipping_diagonal_false_with_inverse[
        OF core r_shift_type Zs_type W_type] .
    show ?thesis
      using d
      by (simp add: shift_pp_T6_liar)
  qed
  have eliminated:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Exists pp_unary_ty ?WB) ?Target"
    using WB_type Target_type bound
    by (rule CEV_axiom_proves.Inst)
  have rev_to_target:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_reversible Z) ?Target"
    using eliminated
    by (simp add: pp_reversible_as_inverse_witness)
  let ?Base = "insert ?TF (insert ?G {?F})"
  have d_F:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_G:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?G"
    using G_type by (intro CEV_axiom_from.Assumption) simp
  have d_TF:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?TF"
    using TF_type by (intro CEV_axiom_from.Assumption) simp
  have d_rev:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_reversible Z"
    using d_G unfolding pp_group_member_def
    by (rule CEV_axiom_from_conj_right)
  have rule:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_reversible Z) ?Target"
    using rev_to_target by (rule CEV_axiom_from.Theorem)
  have target:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Target"
    using d_rev rule by (rule CEV_axiom_from.MP)
  have step_F:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?G (Imp ?TF (Neg ?A))"
    using d_F target by (rule CEV_axiom_from.MP)
  have step_G:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?TF (Neg ?A)"
    using d_G step_F by (rule CEV_axiom_from.MP)
  have not_A:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?A"
    using d_TF step_G by (rule CEV_axiom_from.MP)
  have under_G_F:
    "\<Gamma> ; T ; insert ?G {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?TF (Neg ?A)"
  proof (rule CEV_axiom_from_deduction)
    show "\<Gamma> \<turnstile> ?TF : Prop" by (rule TF_type)
    show "\<Gamma> ; T ; insert ?TF (insert ?G {?F})
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?A"
      by (rule not_A)
  qed
  have under_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?G (Imp ?TF (Neg ?A))"
  proof (rule CEV_axiom_from_deduction)
    show "\<Gamma> \<turnstile> ?G : Prop" by (rule G_type)
    show "\<Gamma> ; T ; insert ?G {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?TF (Neg ?A)"
      by (rule under_G_F)
  qed
  show ?thesis
    using F_type under_F by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_T6_TU_group_diagonal_false:
  assumes axioms: "pp_T6_TU_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Imp
        (pp_group_member Z)
        (Neg
          (App pp_T6_liar
            (App Z (App pp_T6_liar r)))))"
proof -
  let ?D = pp_T6_liar
  let ?A = "App ?D (App Z (App ?D r))"
  let ?F = "pp_fun_prime r"
  let ?G = "pp_group_member Z"
  let ?TP = "pp_truth_preserving Z"
  let ?TF = "pp_truth_flipping Z"
  let ?Base = "insert ?G {?F}"
  have core: "pp_T6_core_PP_axioms \<subseteq> T"
    using axioms unfolding pp_T6_TU_axioms_def by blast
  have TU_in: "pp_TU \<in> T"
    using axioms unfolding pp_T6_TU_axioms_def by blast
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have G_type: "\<Gamma> \<turnstile> ?G : Prop"
    using Z_type by (rule typed_pp_group_member)
  have TP_type: "\<Gamma> \<turnstile> ?TP : Prop"
    using Z_type by (rule typed_pp_truth_preserving)
  have TF_type: "\<Gamma> \<turnstile> ?TF : Prop"
    using Z_type by (rule typed_pp_truth_flipping)
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have d_type: "\<Gamma> \<turnstile> App ?D r : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Zd_type: "\<Gamma> \<turnstile> App Z (App ?D r) : Prop"
    using Z_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using D_type Zd_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have d_F:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_G:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?G"
    using G_type by (intro CEV_axiom_from.Assumption) simp
  have TU_rule:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?G (Disj ?TP ?TF)"
    using CEV_axiom_TU_instance[OF TU_in Z_type]
    by (rule CEV_axiom_from.Theorem)
  have cases:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Disj ?TP ?TF"
    using d_G TU_rule by (rule CEV_axiom_from.MP)
  have left:
    "\<Gamma> ; T ; insert ?TP ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?A"
  proof -
    let ?WithTP = "insert ?TP ?Base"
    have local_F:
      "\<Gamma> ; T ; ?WithTP \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
      using d_F by (rule CEV_axiom_from_mono) simp
    have local_G:
      "\<Gamma> ; T ; ?WithTP \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?G"
      using d_G by (rule CEV_axiom_from_mono) simp
    have local_TP:
      "\<Gamma> ; T ; ?WithTP \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?TP"
      using TP_type by (intro CEV_axiom_from.Assumption) simp
    have rule:
      "\<Gamma> ; T ; ?WithTP \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?F (Imp ?G (Imp ?TP (Neg ?A)))"
      using CEV_T6_TU_preserving_diagonal_false[
        OF core r_type Z_type]
      by (rule CEV_axiom_from.Theorem)
    have step1:
      "\<Gamma> ; T ; ?WithTP \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?G (Imp ?TP (Neg ?A))"
      using local_F rule by (rule CEV_axiom_from.MP)
    have step2:
      "\<Gamma> ; T ; ?WithTP \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?TP (Neg ?A)"
      using local_G step1 by (rule CEV_axiom_from.MP)
    show ?thesis
      using local_TP step2 by (rule CEV_axiom_from.MP)
  qed
  have right:
    "\<Gamma> ; T ; insert ?TF ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?A"
  proof -
    let ?WithTF = "insert ?TF ?Base"
    have local_F:
      "\<Gamma> ; T ; ?WithTF \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
      using d_F by (rule CEV_axiom_from_mono) simp
    have local_G:
      "\<Gamma> ; T ; ?WithTF \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?G"
      using d_G by (rule CEV_axiom_from_mono) simp
    have local_TF:
      "\<Gamma> ; T ; ?WithTF \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?TF"
      using TF_type by (intro CEV_axiom_from.Assumption) simp
    have rule:
      "\<Gamma> ; T ; ?WithTF \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?F (Imp ?G (Imp ?TF (Neg ?A)))"
      using CEV_T6_TU_flipping_diagonal_false[
        OF core r_type Z_type]
      by (rule CEV_axiom_from.Theorem)
    have step1:
      "\<Gamma> ; T ; ?WithTF \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?G (Imp ?TF (Neg ?A))"
      using local_F rule by (rule CEV_axiom_from.MP)
    have step2:
      "\<Gamma> ; T ; ?WithTF \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?TF (Neg ?A)"
      using local_G step1 by (rule CEV_axiom_from.MP)
    show ?thesis
      using local_TF step2 by (rule CEV_axiom_from.MP)
  qed
  have not_A:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?A"
    using TP_type TF_type has_type.Neg[OF A_type]
      cases left right
    by (rule CEV_axiom_from_T5_disj_cases)
  have under_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?G (Neg ?A)"
  proof (rule CEV_axiom_from_deduction)
    show "\<Gamma> \<turnstile> ?G : Prop" by (rule G_type)
    show "\<Gamma> ; T ; insert ?G {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?A"
      by (rule not_A)
  qed
  show ?thesis
    using F_type under_F by (rule CEV_axiom_from_singleton_imp)
qed

subsection \<open>Weak L2 transfers the group diagonal\<close>

lemma CEV_T6_TU_same_kind_refutes:
  assumes axioms: "pp_T6_TU_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Imp
        (pp_same_kind X pp_T6_liar)
        (Neg (App X (App pp_T6_liar r))))"
proof -
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?R = "Neg (App X ?d)"
  let ?F = "pp_fun_prime r"
  let ?Target = "Imp ?F ?R"
  let ?Z = "Var 0"
  let ?Xs = "shift X"
  let ?rs = "shift r"
  let ?ds = "App ?D ?rs"
  let ?GZ = "pp_group_member ?Z"
  let ?E = "Eq pp_unary_ty ?Xs (pp_compose ?D ?Z)"
  let ?P = "Conj ?GZ ?E"
  let ?aZ = "App ?D (App ?Z ?ds)"
  let ?Xsds = "App ?Xs ?ds"
  let ?Fs = "pp_fun_prime ?rs"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xd_type: "\<Gamma> \<turnstile> App X ?d : Prop"
    using X_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using Xd_type by (rule has_type.Neg)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have Target_type: "\<Gamma> \<turnstile> ?Target : Prop"
    using F_type R_type by (rule has_type.Imp)
  have Z_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Z : pp_unary_ty"
    by (rule typed_var0)
  have Xs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Xs : pp_unary_ty"
    using X_type by (rule typed_shift_ctx)
  have rs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?rs : Prop"
    using r_type by (rule typed_shift_ctx)
  have ds_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?ds : Prop"
    using typed_pp_T6_liar rs_type
    unfolding pp_unary_ty_def
    by (rule has_type.App)
  have DZ_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      pp_compose ?D ?Z : pp_unary_ty"
    using typed_pp_T6_liar Z_type by (rule typed_pp_compose)
  have GZ_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?GZ : Prop"
    using Z_type by (rule typed_pp_group_member)
  have E_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?E : Prop"
    using Xs_type DZ_type by (rule has_type.Eq)
  have P_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?P : Prop"
    using GZ_type E_type by (rule has_type.Conj)
  have Fs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Fs : Prop"
    using rs_type by (rule typed_pp_fun_prime)
  have Zds_type:
    "pp_unary_ty # \<Gamma> \<turnstile> App ?Z ?ds : Prop"
    using Z_type ds_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have aZ_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?aZ : Prop"
    using typed_pp_T6_liar Zds_type
    unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xsds_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Xsds : Prop"
    using Xs_type ds_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have d_P:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have d_Fs:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Fs"
    using Fs_type by (intro CEV_axiom_from.Assumption) simp
  have d_GZ:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?GZ"
    using d_P by (rule CEV_axiom_from_conj_left)
  have d_E:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using d_P by (rule CEV_axiom_from_conj_right)
  have group_rule:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?Fs (Imp ?GZ (Neg ?aZ))"
    using CEV_T6_TU_group_diagonal_false[
      OF axioms rs_type Z_type]
    by (rule CEV_axiom_from.Theorem)
  have group_step:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?GZ (Neg ?aZ)"
    using d_Fs group_rule by (rule CEV_axiom_from.MP)
  have not_aZ:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?aZ"
    using d_GZ group_step by (rule CEV_axiom_from.MP)
  have app_cong:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop ?Xsds (App (pp_compose ?D ?Z) ?ds)"
    using Xs_type DZ_type ds_type d_E
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have beta:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App (pp_compose ?D ?Z) ?ds) ?aZ"
    using CEV_pp_compose_apply_eq[
      OF typed_pp_T6_liar Z_type ds_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have DZds_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      App (pp_compose ?D ?Z) ?ds : Prop"
    using DZ_type ds_type
    unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xd_eq:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?Xsds ?aZ"
    using Xsds_type DZds_type aZ_type app_cong beta
    by (rule CEV_axiom_from_eq_trans)
  have neg_eq:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (Neg ?Xsds) (Neg ?aZ)"
    using Xsds_type aZ_type Xd_eq
    by (rule CEV_axiom_from_T5_neg_cong)
  have neg_eq_sym:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (Neg ?aZ) (Neg ?Xsds)"
    using has_type.Neg[OF Xsds_type] has_type.Neg[OF aZ_type] neg_eq
    by (rule CEV_axiom_from_eq_sym)
  have not_Xd:
    "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?Xsds"
    using has_type.Neg[OF aZ_type] has_type.Neg[OF Xsds_type]
      not_aZ neg_eq_sym
    by (rule CEV_axiom_from_eq_prop_elim)
  have under_P:
    "pp_unary_ty # \<Gamma> ; T ; {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?Fs (Neg ?Xsds)"
  proof (rule CEV_axiom_from_deduction)
    show "pp_unary_ty # \<Gamma> \<turnstile> ?Fs : Prop"
      by (rule Fs_type)
    show "pp_unary_ty # \<Gamma> ; T ; insert ?Fs {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?Xsds"
      by (rule not_Xd)
  qed
  have P_to_target:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P (shift ?Target)"
  proof -
    have raw:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?P (Imp ?Fs (Neg ?Xsds))"
      using P_type under_P by (rule CEV_axiom_from_singleton_imp)
    show ?thesis
      using raw by (simp add: shift_pp_T6_liar)
  qed
  have eliminated:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Exists pp_unary_ty ?P) ?Target"
    using P_type Target_type P_to_target
    by (rule CEV_axiom_proves.Inst)
  have same_to_target:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_same_kind X ?D) ?Target"
    using eliminated
    unfolding pp_same_kind_def
    by (simp add: shift_pp_T6_liar)
  let ?Base = "insert (pp_same_kind X ?D) {?F}"
  have d_F:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_same:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_same_kind X ?D"
    using typed_pp_same_kind[OF X_type D_type]
    by (intro CEV_axiom_from.Assumption) simp
  have rule:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_same_kind X ?D) ?Target"
    using same_to_target by (rule CEV_axiom_from.Theorem)
  have target:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Target"
    using d_same rule by (rule CEV_axiom_from.MP)
  have not_Xd_local:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
    using d_F target by (rule CEV_axiom_from.MP)
  have under_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_same_kind X ?D) ?R"
  proof (rule CEV_axiom_from_deduction)
    show "\<Gamma> \<turnstile> pp_same_kind X ?D : Prop"
      using X_type D_type by (rule typed_pp_same_kind)
    show "\<Gamma> ; T ; insert (pp_same_kind X ?D) {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
      by (rule not_Xd_local)
  qed
  show ?thesis
    using F_type under_F by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_T6_TU_liar_matrix:
  assumes axioms: "pp_T6_TU_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
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
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?F = "pp_fun_prime r"
  let ?P =
    "Conj
      (pp_pure pp_unary_ty X)
      (Conj
        (pp_fun_prime q)
        (Eq Prop ?d (App X q)))"
  let ?R = "Neg (App X ?d)"
  let ?Base = "insert ?P {?F}"
  have core: "pp_T6_core_PP_axioms \<subseteq> T"
    using axioms unfolding pp_T6_TU_axioms_def by blast
  have L2_in: "pp_L2 \<in> T"
    using axioms unfolding pp_T6_TU_axioms_def by blast
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
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_pure[OF X_type] typed_pp_fun_prime[OF q_type]
      d_type Xq_type
    by (intro has_type.Conj has_type.Eq)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using Xd_type by (rule has_type.Neg)
  have d_F:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_P:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have pure_X:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty X"
    using d_P by (rule CEV_axiom_from_conj_left)
  have d_tail:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_fun_prime q) (Eq Prop ?d (App X q))"
    using d_P by (rule CEV_axiom_from_conj_right)
  have fun_q:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime q"
    using d_tail by (rule CEV_axiom_from_conj_left)
  have decomp:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?d (App X q)"
    using d_tail by (rule CEV_axiom_from_conj_right)
  have pure_D:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?D"
    using CEV_axiom_proves_mono[OF pp_T6_liar_pure core]
    by (rule CEV_axiom_from.Theorem)
  have same:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App X q) (App ?D r)"
    using d_type Xq_type decomp
    by (rule CEV_axiom_from_eq_sym)
  have l2_tail:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_fun_prime q)
        (Conj
          (pp_fun_prime r)
          (Eq Prop (App X q) (App ?D r)))"
    using fun_q CEV_axiom_from_conj_intro[OF d_F same]
    by (rule CEV_axiom_from_conj_intro)
  have l2_middle:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty ?D)
        (Conj
          (pp_fun_prime q)
          (Conj
            (pp_fun_prime r)
            (Eq Prop (App X q) (App ?D r))))"
    using pure_D l2_tail by (rule CEV_axiom_from_conj_intro)
  have l2_prem:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty X)
        (Conj
          (pp_pure pp_unary_ty ?D)
          (Conj
            (pp_fun_prime q)
            (Conj
              (pp_fun_prime r)
              (Eq Prop (App X q) (App ?D r)))))"
    using pure_X l2_middle by (rule CEV_axiom_from_conj_intro)
  have l2_rule:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj
          (pp_pure pp_unary_ty X)
          (Conj
            (pp_pure pp_unary_ty ?D)
            (Conj
              (pp_fun_prime q)
              (Conj
                (pp_fun_prime r)
                (Eq Prop (App X q) (App ?D r))))))
        (pp_same_kind X ?D)"
    using CEV_axiom_L2_instance[
      OF L2_in X_type D_type q_type r_type]
    by (rule CEV_axiom_from.Theorem)
  have same_kind:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_same_kind X ?D"
    using l2_prem l2_rule by (rule CEV_axiom_from.MP)
  have refute_rule:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F (Imp (pp_same_kind X ?D) ?R)"
    using CEV_T6_TU_same_kind_refutes[
      OF axioms r_type X_type]
    by (rule CEV_axiom_from.Theorem)
  have refute_step:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_same_kind X ?D) ?R"
    using d_F refute_rule by (rule CEV_axiom_from.MP)
  have d_R:
    "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
    using same_kind refute_step by (rule CEV_axiom_from.MP)
  have under_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?P ?R"
  proof (rule CEV_axiom_from_deduction)
    show "\<Gamma> \<turnstile> ?P : Prop" by (rule P_type)
    show "\<Gamma> ; T ; insert ?P {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
      by (rule d_R)
  qed
  show ?thesis
    using F_type under_F by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_T6_TU_liar_true:
  assumes axioms: "pp_T6_TU_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (App pp_T6_liar (App pp_T6_liar r))"
proof -
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?F = "pp_fun_prime r"
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
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
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
      Imp (shift_by 2 ?F) ?M"
  proof -
    have raw:
      "Prop # pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (pp_fun_prime (shift_by 2 r))
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
      using axioms r2_type X2_type q2_type
      by (rule CEV_T6_TU_liar_matrix)
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
    have shift_F:
      "shift_by 2 ?F = pp_fun_prime (shift_by 2 r)"
    proof -
      have f_shift:
        "shift (shift ?F) =
          pp_fun_prime (shift (shift r))"
        by simp
      show ?thesis
        using f_shift
          shift_shift_eq_shift_by_2[of ?F]
          shift_shift_eq_shift_by_2[of r]
        by simp
    qed
    show ?thesis
      using raw by (simp only: shift_d shift_F)
  qed
  have parameter_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile>
      Imp (shift_by 2 ?F) ?M : Prop"
    using parameter by (rule CEV_axiom_proves_formula)
  have M_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?M : Prop"
    using parameter_type by (auto elim: has_type.cases)
  have F1_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift ?F : Prop"
    using F_type by (rule typed_shift_ctx)
  have inner:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?F) (Forall Prop ?M)"
  proof (rule CEV_axiom_proves.Gen)
    show "pp_unary_ty # \<Gamma> \<turnstile> shift ?F : Prop"
      by (rule F1_type)
    show "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?M : Prop"
      by (rule M_type)
    show "Prop # pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift (shift ?F)) ?M"
      using parameter
        shift_shift_eq_shift_by_2[of ?F]
      by simp
  qed
  have forall_type:
    "pp_unary_ty # \<Gamma> \<turnstile> Forall Prop ?M : Prop"
    using M_type by (rule has_type.Forall)
  have outer:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (Forall pp_unary_ty (Forall Prop ?M))"
  proof (rule CEV_axiom_proves.Gen)
    show "\<Gamma> \<turnstile> ?F : Prop" by (rule F_type)
    show "pp_unary_ty # \<Gamma> \<turnstile> Forall Prop ?M : Prop"
      by (rule forall_type)
    show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (shift ?F) (Forall Prop ?M)"
      by (rule inner)
  qed
  have liar_at_rule:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (pp_T5_liar_at ?d)"
    using outer by (simp only: pp_T5_liar_at_explicit)
  let ?L = "pp_T5_liar_at ?d"
  let ?P = "App ?D ?d"
  have L_type: "\<Gamma> \<turnstile> ?L : Prop"
    using d_type by (rule typed_pp_T5_liar_at)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using D_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have d_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have local_rule:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?F ?L"
    using liar_at_rule by (rule CEV_axiom_from.Theorem)
  have d_L:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?L"
    using d_F local_rule by (rule CEV_axiom_from.MP)
  have PL:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?P ?L"
    using CEV_pp_T6_liar_apply_eq[OF d_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have LP:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?L ?P"
    using P_type L_type PL by (rule CEV_axiom_from_eq_sym)
  have d_P:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using L_type P_type d_L LP
    by (rule CEV_axiom_from_eq_prop_elim)
  show ?thesis
    using F_type d_P by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_T6_TU_fun_prime_implies_false:
  assumes axioms: "pp_T6_TU_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) ObjFalse"
proof -
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?F = "pp_fun_prime r"
  let ?P = "App ?D ?d"
  have core: "pp_T5_axioms \<subseteq> T"
    using axioms
    unfolding pp_T6_TU_axioms_def pp_T5_axioms_def by blast
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
  have d_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have true_rule:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?F ?P"
    using CEV_T6_TU_liar_true[OF axioms r_type]
    by (rule CEV_axiom_from.Theorem)
  have d_P:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using d_F true_rule by (rule CEV_axiom_from.MP)
  have not_rule:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F (Neg ?P)"
    using CEV_T5_not_Dd[OF core r_type]
    by (rule CEV_axiom_from.Theorem)
  have not_P:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?P"
    using d_F not_rule by (rule CEV_axiom_from.MP)
  have false:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_P not_P by (rule CEV_axiom_from_contradiction)
  show ?thesis
    using F_type false by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_Goodman_T6_TU:
  "[] ; pp_T6_TU_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof -
  let ?F = "pp_fun_prime (Var 0)"
  have r_type: "[Prop] \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have F_type: "[Prop] \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have witness_rule:
    "[Prop] ; pp_T6_TU_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (shift ObjFalse)"
    using CEV_T6_TU_fun_prime_implies_false[
      OF subset_refl r_type]
    by simp
  have exists_rule_raw:
    "[] ; pp_T6_TU_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Exists Prop ?F) ObjFalse"
  proof (rule CEV_axiom_proves.Inst)
    show "[Prop] \<turnstile> ?F : Prop" by (rule F_type)
    show "[] \<turnstile> ObjFalse : Prop" by (rule typed_ObjFalse)
    show "[Prop] ; pp_T6_TU_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (shift ObjFalse)"
      by (rule witness_rule)
  qed
  have exists_rule:
    "[] ; pp_T6_TU_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp pp_exists_fun_prime ObjFalse"
    using exists_rule_raw
    unfolding pp_exists_fun_prime_def .
  have exists_fun:
    "[] ; pp_T6_TU_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_exists_fun_prime"
  proof (rule CEV_axiom_proves.Axiom)
    show "pp_exists_fun_prime \<in> pp_T6_TU_axioms"
      unfolding pp_T6_TU_axioms_def by blast
    show "[] \<turnstile> pp_exists_fun_prime : Prop"
      by (rule typed_pp_exists_fun_prime)
  qed
  show ?thesis
    using exists_fun exists_rule by (rule CEV_axiom_proves.MP)
qed

corollary CEV_Goodman_T6_TU_mono:
  assumes "pp_T6_TU_axioms \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  using CEV_Goodman_T6_TU assms
  by (rule CEV_axiom_proves_mono)

end
