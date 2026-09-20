theory Bacon_PP_Goodman_T8_Base_Kinds
  imports 
    "Goodman_Legacy_T8_Kind.Bacon_PP_Goodman_T8_Kind_Uniqueness"
begin

section \<open>Goodman T8a: the five base kinds are distinct\<close>

subsection \<open>Local transport tools\<close>

lemma shift_gd_box_op_T8[simp]:
  "shift gd_box_op = gd_box_op"
  by (simp add: shift_def gd_box_op_def ObjTrue_def)

lemma shift_pp_T8_diamond_operator[simp]:
  "shift pp_T8_diamond_operator = pp_T8_diamond_operator"
  by (simp add: shift_def pp_T8_diamond_operator_def
    ObjFalse_def ObjTrue_def)

lemma shift_gd_true_op_T8[simp]:
  "shift gd_true_op = gd_true_op"
  by (simp add: shift_def gd_true_op_def ObjTrue_def)

lemma shift_gd_false_op_T8[simp]:
  "shift gd_false_op = gd_false_op"
  by (simp add: shift_def gd_false_op_def ObjFalse_def ObjTrue_def)

lemma CEVs_T8_eq_truth_right:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and eq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop A B"
    and dA: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
  using A_type B_type dA eq
  by (rule CEV_axiom_from_eq_prop_elim)

lemma CEVs_T8_eq_truth_left:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and eq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop A B"
    and dB: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
proof -
  have eq_sym:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop B A"
    using A_type B_type eq by (rule CEV_axiom_from_eq_sym)
  show ?thesis
    using B_type A_type dB eq_sym
    by (rule CEV_axiom_from_eq_prop_elim)
qed

lemma CEVs_T8_eq_neg_right:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and eq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop A B"
    and dnA: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg B"
proof -
  have neg_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg A) (Neg B)"
    using A_type B_type eq by (rule CEV_axiom_from_T5_neg_cong)
  show ?thesis
    using has_type.Neg[OF A_type] has_type.Neg[OF B_type]
      dnA neg_eq
    by (rule CEV_axiom_from_eq_prop_elim)
qed

lemma CEVs_T8_eq_neg_left:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and eq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop A B"
    and dnB: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg A"
proof -
  have eq_sym:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop B A"
    using A_type B_type eq by (rule CEV_axiom_from_eq_sym)
  show ?thesis
    using B_type A_type eq_sym dnB
    by (rule CEVs_T8_eq_neg_right)
qed

lemma CEVs_T8_fun_prime_group_apply:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and fun_p:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
    and group_Z:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member Z"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_fun_prime (App Z p)"
proof -
  have pair:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_fun_prime p) (pp_group_member Z)"
    using fun_p group_Z by (rule CEV_axiom_from_conj_intro)
  have rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj (pp_fun_prime p) (pp_group_member Z))
        (pp_fun_prime (App Z p))"
    using CEV_fun_prime_under_group_member[
      OF core p_type Z_type]
    by (rule CEV_axiom_from.Theorem)
  show ?thesis
    using pair rule by (rule CEV_axiom_from.MP)
qed

lemma CEVs_T8_not_box_at_fun_prime:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and fun_p:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Neg (App gd_box_op p)"
proof (rule CEVs_app_false)
  show "\<Gamma> \<turnstile> gd_box_op : pp_unary_ty"
    by (rule typed_gd_box_op)
  show "\<Gamma> \<turnstile> p : Prop" by (rule p_type)
  show "\<Gamma> \<turnstile> Eq Prop p ObjTrue : Prop"
    using p_type typed_ObjTrue by (rule has_type.Eq)
  show "compatible_step beta_contract
      (App gd_box_op p) (Eq Prop p ObjTrue)"
    by (rule gd_box_op_beta)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop p ObjTrue)"
    using fun_p
      CEV_axiom_from.Theorem[
        OF CEV_fun_prime_neq_ObjTrue[
          OF pp_T2_min_axioms_into_T6_extension[OF core] p_type]]
    by (rule CEV_axiom_from.MP)
qed

lemma CEVs_T8_diamond_at_fun_prime:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and fun_p:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    App pp_T8_diamond_operator p"
proof (rule CEVs_app_true)
  show "\<Gamma> \<turnstile> pp_T8_diamond_operator : pp_unary_ty"
    by (rule typed_pp_T8_diamond_operator)
  show "\<Gamma> \<turnstile> p : Prop" by (rule p_type)
  show "\<Gamma> \<turnstile> Neg (Eq Prop p ObjFalse) : Prop"
    using p_type typed_ObjFalse by (intro has_type.Neg has_type.Eq)
  show "compatible_step beta_contract
      (App pp_T8_diamond_operator p)
      (Neg (Eq Prop p ObjFalse))"
    by (rule pp_T8_diamond_operator_beta)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop p ObjFalse)"
    using fun_p
      CEV_axiom_from.Theorem[
        OF CEV_fun_prime_neq_ObjFalse[
          OF pp_T2_min_axioms_into_T6_extension[OF core] p_type]]
    by (rule CEV_axiom_from.MP)
qed

lemma CEVs_T8_same_kind_witness_apply:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and op_eq:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty X (pp_compose Y Z)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App X p) (App Y (App Z p))"
proof -
  have YZ_type: "\<Gamma> \<turnstile> pp_compose Y Z : pp_unary_ty"
    using Y_type Z_type by (rule typed_pp_compose)
  have app_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App X p) (App (pp_compose Y Z) p)"
    using X_type YZ_type p_type op_eq
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have beta:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App (pp_compose Y Z) p) (App Y (App Z p))"
    using CEV_pp_compose_apply_eq[OF Y_type Z_type p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have left_type: "\<Gamma> \<turnstile> App X p : Prop"
    using X_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have middle_type:
    "\<Gamma> \<turnstile> App (pp_compose Y Z) p : Prop"
    using YZ_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Zp_type: "\<Gamma> \<turnstile> App Z p : Prop"
    using Z_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have right_type: "\<Gamma> \<turnstile> App Y (App Z p) : Prop"
    using Y_type Zp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    using left_type middle_type right_type app_eq beta
    by (rule CEV_axiom_from_eq_trans)
qed

lemma CEV_T8_refute_same_kind_under:
  assumes F_type: "\<Gamma> \<turnstile> F : Prop"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and witness_refutation:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (Conj
            (pp_group_member (Var 0))
            (Eq pp_unary_ty
              (shift X)
              (pp_compose (shift Y) (Var 0))))
          (shift (Imp F ObjFalse))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp F (Neg (pp_same_kind X Y))"
proof -
  let ?K = "pp_same_kind X Y"
  let ?P =
    "Conj
      (pp_group_member (Var 0))
      (Eq pp_unary_ty
        (shift X)
        (pp_compose (shift Y) (Var 0)))"
  have P_type: "pp_unary_ty # \<Gamma> \<turnstile> ?P : Prop"
  proof -
    have Z_type:
      "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
      by (rule typed_var0)
    have Xs_type:
      "pp_unary_ty # \<Gamma> \<turnstile> shift X : pp_unary_ty"
      using X_type by (rule typed_shift_ctx)
    have Ys_type:
      "pp_unary_ty # \<Gamma> \<turnstile> shift Y : pp_unary_ty"
      using Y_type by (rule typed_shift_ctx)
    have YZ_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_compose (shift Y) (Var 0) : pp_unary_ty"
      using Ys_type Z_type by (rule typed_pp_compose)
    show ?thesis
      using typed_pp_group_member[OF Z_type] Xs_type YZ_type
      by (intro has_type.Conj has_type.Eq)
  qed
  have target_type: "\<Gamma> \<turnstile> Imp F ObjFalse : Prop"
    using F_type typed_ObjFalse by (rule has_type.Imp)
  have eliminated:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?K (Imp F ObjFalse)"
    using P_type target_type witness_refutation
    unfolding pp_same_kind_def
    by (rule CEV_axiom_proves.Inst)
  have swap:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp ?K (Imp F ObjFalse))
        (Imp F (Imp ?K ObjFalse))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp ?K (Imp F ObjFalse))
        (Imp F (Imp ?K ObjFalse)))"
      using typed_pp_same_kind[OF X_type Y_type]
        F_type typed_ObjFalse
      by (rule prop_tautology_swap_imp)
  qed
  have swapped:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp F (Imp ?K ObjFalse)"
    using eliminated CEV_axiom_proves.Base[OF swap]
    by (rule CEV_axiom_proves.MP)
  let ?S = "{F}"
  have d_F: "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_swapped:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp F (Imp ?K ObjFalse)"
    using swapped by (rule CEV_axiom_from.Theorem)
  have k_false:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?K ObjFalse"
    using d_F d_swapped by (rule CEV_axiom_from.MP)
  have to_neg:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?K ObjFalse) (Neg ?K)"
    using CEV_proves_imp_false_to_neg[
      OF typed_pp_same_kind[OF X_type Y_type]]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_neg:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?K"
    using k_false to_neg by (rule CEV_axiom_from.MP)
  show ?thesis
    using F_type d_neg by (rule CEV_axiom_from_singleton_imp)
qed

subsection \<open>Identity is not of the necessity kind\<close>

theorem CEV_Goodman_T8a_Id_Box:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg (pp_same_kind pp_identity_operator gd_box_op))"
proof (rule CEV_T8_refute_same_kind_under)
  show "\<Gamma> \<turnstile> pp_fun_prime r : Prop"
    using r_type by (rule typed_pp_fun_prime)
  show "\<Gamma> \<turnstile> pp_identity_operator : pp_unary_ty"
    by (rule typed_pp_identity_operator)
  show "\<Gamma> \<turnstile> gd_box_op : pp_unary_ty"
    by (rule typed_gd_box_op)
  let ?Z = "Var 0"
  let ?rs = "shift r"
  let ?nrs = "Neg ?rs"
  let ?F = "pp_fun_prime ?rs"
  let ?P =
    "Conj
      (pp_group_member ?Z)
      (Eq pp_unary_ty
        (shift pp_identity_operator)
        (pp_compose (shift gd_box_op) ?Z))"
  let ?S = "insert ?F {?P}"
  have Z_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Z : pp_unary_ty"
    by (rule typed_var0)
  have rs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?rs : Prop"
    using r_type by (rule typed_shift_ctx)
  have nrs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?nrs : Prop"
    using rs_type by (rule has_type.Neg)
  have Ids_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      shift pp_identity_operator : pp_unary_ty"
    using typed_pp_identity_operator by (rule typed_shift_ctx)
  have Boxs_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      shift gd_box_op : pp_unary_ty"
    using typed_gd_box_op by (rule typed_shift_ctx)
  have BoxZ_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      pp_compose (shift gd_box_op) ?Z : pp_unary_ty"
    using Boxs_type Z_type by (rule typed_pp_compose)
  have P_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_group_member[OF Z_type] Ids_type BoxZ_type
    by (intro has_type.Conj has_type.Eq)
  have F_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?F : Prop"
    using rs_type by (rule typed_pp_fun_prime)
  have d_P:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have d_group:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member ?Z"
    using d_P by (rule CEV_axiom_from_conj_left)
  have d_op:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (shift pp_identity_operator)
          (pp_compose (shift gd_box_op) ?Z)"
    using d_P by (rule CEV_axiom_from_conj_right)
  have d_F:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_Fneg:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime ?nrs"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_fun_prime_under_negation[OF core rs_type]]
    by (rule CEV_axiom_from.MP)

  have Zr_type:
    "pp_unary_ty # \<Gamma> \<turnstile> App ?Z ?rs : Prop"
    using Z_type rs_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Znr_type:
    "pp_unary_ty # \<Gamma> \<turnstile> App ?Z ?nrs : Prop"
    using Z_type nrs_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have fun_Zr:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime (App ?Z ?rs)"
    using core rs_type Z_type d_F d_group
    by (rule CEVs_T8_fun_prime_group_apply)
  have fun_Znr:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime (App ?Z ?nrs)"
    using core nrs_type Z_type d_Fneg d_group
    by (rule CEVs_T8_fun_prime_group_apply)
  have not_box_Zr:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App (shift gd_box_op) (App ?Z ?rs))"
  proof -
    have raw:
      "pp_unary_ty # \<Gamma> ; T ; ?S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Neg (App gd_box_op (App ?Z ?rs))"
      using core Zr_type fun_Zr
      by (rule CEVs_T8_not_box_at_fun_prime)
    show ?thesis using raw by simp
  qed
  have not_box_Znr:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App (shift gd_box_op) (App ?Z ?nrs))"
  proof -
    have raw:
      "pp_unary_ty # \<Gamma> ; T ; ?S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Neg (App gd_box_op (App ?Z ?nrs))"
      using core Znr_type fun_Znr
      by (rule CEVs_T8_not_box_at_fun_prime)
    show ?thesis using raw by simp
  qed
  have eq_r:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop
          (App (shift pp_identity_operator) ?rs)
          (App (shift gd_box_op) (App ?Z ?rs))"
    using Ids_type Boxs_type Z_type rs_type d_op
    by (rule CEVs_T8_same_kind_witness_apply)
  have eq_nr:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop
          (App (shift pp_identity_operator) ?nrs)
          (App (shift gd_box_op) (App ?Z ?nrs))"
    using Ids_type Boxs_type Z_type nrs_type d_op
    by (rule CEVs_T8_same_kind_witness_apply)
  have not_Id_r:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App (shift pp_identity_operator) ?rs)"
  proof (rule CEVs_T8_eq_neg_left)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      App (shift pp_identity_operator) ?rs : Prop"
      using Ids_type rs_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      App (shift gd_box_op) (App ?Z ?rs) : Prop"
      using Boxs_type Zr_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop
        (App (shift pp_identity_operator) ?rs)
        (App (shift gd_box_op) (App ?Z ?rs))"
      by (rule eq_r)
    show "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App (shift gd_box_op) (App ?Z ?rs))"
      by (rule not_box_Zr)
  qed
  have not_Id_nr:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App (shift pp_identity_operator) ?nrs)"
  proof (rule CEVs_T8_eq_neg_left)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      App (shift pp_identity_operator) ?nrs : Prop"
      using Ids_type nrs_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      App (shift gd_box_op) (App ?Z ?nrs) : Prop"
      using Boxs_type Znr_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop
        (App (shift pp_identity_operator) ?nrs)
        (App (shift gd_box_op) (App ?Z ?nrs))"
      by (rule eq_nr)
    show "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App (shift gd_box_op) (App ?Z ?nrs))"
      by (rule not_box_Znr)
  qed
  have id_r_eq:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App (shift pp_identity_operator) ?rs) ?rs"
  proof -
    have raw:
      "pp_unary_ty # \<Gamma> ; T ; ?S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Eq Prop (App pp_identity_operator ?rs) ?rs"
      using CEV_pp_identity_operator_apply_eq[OF rs_type]
      by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
    show ?thesis using raw by simp
  qed
  have id_nr_eq:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App (shift pp_identity_operator) ?nrs) ?nrs"
  proof -
    have raw:
      "pp_unary_ty # \<Gamma> ; T ; ?S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Eq Prop (App pp_identity_operator ?nrs) ?nrs"
      using CEV_pp_identity_operator_apply_eq[OF nrs_type]
      by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
    show ?thesis using raw by simp
  qed
  have not_r:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?rs"
  proof (rule CEVs_T8_eq_neg_right)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      App (shift pp_identity_operator) ?rs : Prop"
      using Ids_type rs_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "pp_unary_ty # \<Gamma> \<turnstile> ?rs : Prop"
      by (rule rs_type)
    show "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App (shift pp_identity_operator) ?rs) ?rs"
      by (rule id_r_eq)
    show "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App (shift pp_identity_operator) ?rs)"
      by (rule not_Id_r)
  qed
  have not_not_r:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?nrs"
  proof (rule CEVs_T8_eq_neg_right)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      App (shift pp_identity_operator) ?nrs : Prop"
      using Ids_type nrs_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show "pp_unary_ty # \<Gamma> \<turnstile> ?nrs : Prop"
      by (rule nrs_type)
    show "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App (shift pp_identity_operator) ?nrs) ?nrs"
      by (rule id_nr_eq)
    show "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App (shift pp_identity_operator) ?nrs)"
      by (rule not_Id_nr)
  qed
  have d_false:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using not_r not_not_r by (rule CEV_axiom_from_contradiction)
  have under_F:
    "pp_unary_ty # \<Gamma> ; T ; {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?F ObjFalse"
    using F_type d_false by (rule CEV_axiom_from_deduction)
  have result:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P (Imp ?F ObjFalse)"
    using P_type under_F by (rule CEV_axiom_from_singleton_imp)
  show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P (shift (Imp (pp_fun_prime r) ObjFalse))"
    using result by simp
qed

subsection \<open>Identity is not of the possibility kind\<close>

lemma CEVs_T8_Id_Diamond_forces_input:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and fun_p:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
    and group_Z:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member Z"
    and op_eq:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          pp_identity_operator
          (pp_compose pp_T8_diamond_operator Z)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s p"
proof -
  have Zp_type: "\<Gamma> \<turnstile> App Z p : Prop"
    using Z_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have fun_Zp:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_fun_prime (App Z p)"
    using core p_type Z_type fun_p group_Z
    by (rule CEVs_T8_fun_prime_group_apply)
  have dia_Zp:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      App pp_T8_diamond_operator (App Z p)"
    using core Zp_type fun_Zp
    by (rule CEVs_T8_diamond_at_fun_prime)
  have app_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop
        (App pp_identity_operator p)
        (App pp_T8_diamond_operator (App Z p))"
    using typed_pp_identity_operator
      typed_pp_T8_diamond_operator Z_type p_type op_eq
    by (rule CEVs_T8_same_kind_witness_apply)
  have Idp_type: "\<Gamma> \<turnstile> App pp_identity_operator p : Prop"
    using typed_pp_identity_operator p_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have DiaZp_type:
    "\<Gamma> \<turnstile> App pp_T8_diamond_operator (App Z p) : Prop"
    using typed_pp_T8_diamond_operator Zp_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have d_Idp:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      App pp_identity_operator p"
    using Idp_type DiaZp_type app_eq dia_Zp
    by (rule CEVs_T8_eq_truth_left)
  have id_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_identity_operator p) p"
    using CEV_pp_identity_operator_apply_eq[OF p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using Idp_type p_type id_eq d_Idp
    by (rule CEVs_T8_eq_truth_right)
qed

theorem CEV_Goodman_T8a_Id_Diamond:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg
        (pp_same_kind
          pp_identity_operator
          pp_T8_diamond_operator))"
proof (rule CEV_T8_refute_same_kind_under)
  show "\<Gamma> \<turnstile> pp_fun_prime r : Prop"
    using r_type by (rule typed_pp_fun_prime)
  show "\<Gamma> \<turnstile> pp_identity_operator : pp_unary_ty"
    by (rule typed_pp_identity_operator)
  show "\<Gamma> \<turnstile> pp_T8_diamond_operator : pp_unary_ty"
    by (rule typed_pp_T8_diamond_operator)
  let ?Z = "Var 0"
  let ?rs = "shift r"
  let ?nrs = "Neg ?rs"
  let ?F = "pp_fun_prime ?rs"
  let ?P =
    "Conj
      (pp_group_member ?Z)
      (Eq pp_unary_ty
        (shift pp_identity_operator)
        (pp_compose (shift pp_T8_diamond_operator) ?Z))"
  let ?S = "insert ?F {?P}"
  have Z_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Z : pp_unary_ty"
    by (rule typed_var0)
  have rs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?rs : Prop"
    using r_type by (rule typed_shift_ctx)
  have nrs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?nrs : Prop"
    using rs_type by (rule has_type.Neg)
  have P_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_group_member[OF Z_type]
      typed_shift_ctx[OF typed_pp_identity_operator]
      typed_pp_compose[
        OF typed_shift_ctx[OF typed_pp_T8_diamond_operator] Z_type]
    by (intro has_type.Conj has_type.Eq)
  have F_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?F : Prop"
    using rs_type by (rule typed_pp_fun_prime)
  have d_P:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have d_group:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member ?Z"
    using d_P by (rule CEV_axiom_from_conj_left)
  have d_op_shift:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (shift pp_identity_operator)
          (pp_compose (shift pp_T8_diamond_operator) ?Z)"
    using d_P by (rule CEV_axiom_from_conj_right)
  have d_op:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          pp_identity_operator
          (pp_compose pp_T8_diamond_operator ?Z)"
    using d_op_shift by simp
  have d_F:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_Fneg:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime ?nrs"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_fun_prime_under_negation[OF core rs_type]]
    by (rule CEV_axiom_from.MP)
  have d_r:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?rs"
    using core rs_type Z_type d_F d_group d_op
    by (rule CEVs_T8_Id_Diamond_forces_input)
  have d_nr:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?nrs"
    using core nrs_type Z_type d_Fneg d_group d_op
    by (rule CEVs_T8_Id_Diamond_forces_input)
  have d_false:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_r d_nr by (rule CEV_axiom_from_contradiction)
  have under_F:
    "pp_unary_ty # \<Gamma> ; T ; {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?F ObjFalse"
    using F_type d_false by (rule CEV_axiom_from_deduction)
  have result:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P (Imp ?F ObjFalse)"
    using P_type under_F by (rule CEV_axiom_from_singleton_imp)
  show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P (shift (Imp (pp_fun_prime r) ObjFalse))"
    using result by simp
qed

subsection \<open>Necessity is not of the possibility kind\<close>

lemma CEVs_T8_Box_Diamond_contradiction:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and fun_p:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
    and group_Z:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member Z"
    and op_eq:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          gd_box_op
          (pp_compose pp_T8_diamond_operator Z)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
proof -
  have Zp_type: "\<Gamma> \<turnstile> App Z p : Prop"
    using Z_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have fun_Zp:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_fun_prime (App Z p)"
    using core p_type Z_type fun_p group_Z
    by (rule CEVs_T8_fun_prime_group_apply)
  have not_box:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (App gd_box_op p)"
    using core p_type fun_p
    by (rule CEVs_T8_not_box_at_fun_prime)
  have dia:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      App pp_T8_diamond_operator (App Z p)"
    using core Zp_type fun_Zp
    by (rule CEVs_T8_diamond_at_fun_prime)
  have app_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop
        (App gd_box_op p)
        (App pp_T8_diamond_operator (App Z p))"
    using typed_gd_box_op typed_pp_T8_diamond_operator
      Z_type p_type op_eq
    by (rule CEVs_T8_same_kind_witness_apply)
  have box_type: "\<Gamma> \<turnstile> App gd_box_op p : Prop"
    using typed_gd_box_op p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have dia_type:
    "\<Gamma> \<turnstile> App pp_T8_diamond_operator (App Z p) : Prop"
    using typed_pp_T8_diamond_operator Zp_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have d_box:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gd_box_op p"
    using box_type dia_type app_eq dia
    by (rule CEVs_T8_eq_truth_left)
  show ?thesis
    using d_box not_box by (rule CEV_axiom_from_contradiction)
qed

theorem CEV_Goodman_T8a_Box_Diamond:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg
        (pp_same_kind gd_box_op pp_T8_diamond_operator))"
proof (rule CEV_T8_refute_same_kind_under)
  show "\<Gamma> \<turnstile> pp_fun_prime r : Prop"
    using r_type by (rule typed_pp_fun_prime)
  show "\<Gamma> \<turnstile> gd_box_op : pp_unary_ty"
    by (rule typed_gd_box_op)
  show "\<Gamma> \<turnstile> pp_T8_diamond_operator : pp_unary_ty"
    by (rule typed_pp_T8_diamond_operator)
  let ?Z = "Var 0"
  let ?rs = "shift r"
  let ?F = "pp_fun_prime ?rs"
  let ?P =
    "Conj
      (pp_group_member ?Z)
      (Eq pp_unary_ty
        (shift gd_box_op)
        (pp_compose (shift pp_T8_diamond_operator) ?Z))"
  let ?S = "insert ?F {?P}"
  have Z_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Z : pp_unary_ty"
    by (rule typed_var0)
  have rs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?rs : Prop"
    using r_type by (rule typed_shift_ctx)
  have P_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_group_member[OF Z_type]
      typed_shift_ctx[OF typed_gd_box_op]
      typed_pp_compose[
        OF typed_shift_ctx[OF typed_pp_T8_diamond_operator] Z_type]
    by (intro has_type.Conj has_type.Eq)
  have F_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?F : Prop"
    using rs_type by (rule typed_pp_fun_prime)
  have d_P:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have d_group:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member ?Z"
    using d_P by (rule CEV_axiom_from_conj_left)
  have d_op_shift:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (shift gd_box_op)
          (pp_compose (shift pp_T8_diamond_operator) ?Z)"
    using d_P by (rule CEV_axiom_from_conj_right)
  have d_op:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty gd_box_op
          (pp_compose pp_T8_diamond_operator ?Z)"
    using d_op_shift by simp
  have d_F:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_false:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using core rs_type Z_type d_F d_group d_op
    by (rule CEVs_T8_Box_Diamond_contradiction)
  have under_F:
    "pp_unary_ty # \<Gamma> ; T ; {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?F ObjFalse"
    using F_type d_false by (rule CEV_axiom_from_deduction)
  have result:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P (Imp ?F ObjFalse)"
    using P_type under_F by (rule CEV_axiom_from_singleton_imp)
  show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P (shift (Imp (pp_fun_prime r) ObjFalse))"
    using result by simp
qed

subsection \<open>The two constant kinds\<close>

lemma CEV_pp_compose_gd_true_left:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (pp_compose gd_true_op Z)
      gd_true_op"
proof (rule CEV_unary_eq_of_beta_step)
  show "\<Gamma> \<turnstile> pp_compose gd_true_op Z : pp_unary_ty"
    using typed_gd_true_op Z_type by (rule typed_pp_compose)
  show "\<Gamma> \<turnstile> gd_true_op : pp_unary_ty"
    by (rule typed_gd_true_op)
  show "compatible_step beta_contract
      (pp_compose gd_true_op Z) gd_true_op"
  proof -
    have step:
      "beta_contract
        (App (Lam Prop ObjTrue)
          (App (shift Z) (Var 0)))
        (subst0 (App (shift Z) (Var 0)) ObjTrue)"
      by (rule beta_contract.beta)
    have root:
      "compatible_step beta_contract
        (App (shift gd_true_op)
          (App (shift Z) (Var 0)))
        ObjTrue"
    proof (rule compatible_step.root)
      show "beta_contract
        (App (shift gd_true_op)
          (App (shift Z) (Var 0)))
        ObjTrue"
        using step
        by (simp add: shift_def gd_true_op_def
          subst0_def ObjTrue_def)
    qed
    have lifted:
      "compatible_step beta_contract
        (Lam Prop
          (App (shift gd_true_op)
            (App (shift Z) (Var 0))))
        (Lam Prop ObjTrue)"
      using root by (rule compatible_step.Lam_body)
    show ?thesis
      using lifted
      by (simp add: pp_compose_def gd_true_op_def)
  qed
qed

lemma CEV_pp_compose_gd_false_left:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (pp_compose gd_false_op Z)
      gd_false_op"
proof (rule CEV_unary_eq_of_beta_step)
  show "\<Gamma> \<turnstile> pp_compose gd_false_op Z : pp_unary_ty"
    using typed_gd_false_op Z_type by (rule typed_pp_compose)
  show "\<Gamma> \<turnstile> gd_false_op : pp_unary_ty"
    by (rule typed_gd_false_op)
  show "compatible_step beta_contract
      (pp_compose gd_false_op Z) gd_false_op"
  proof -
    have step:
      "beta_contract
        (App (Lam Prop ObjFalse)
          (App (shift Z) (Var 0)))
        (subst0 (App (shift Z) (Var 0)) ObjFalse)"
      by (rule beta_contract.beta)
    have root:
      "compatible_step beta_contract
        (App (shift gd_false_op)
          (App (shift Z) (Var 0)))
        ObjFalse"
    proof (rule compatible_step.root)
      show "beta_contract
        (App (shift gd_false_op)
          (App (shift Z) (Var 0)))
        ObjFalse"
        using step
        by (simp add: shift_def gd_false_op_def
          subst0_def ObjFalse_def ObjTrue_def)
    qed
    have lifted:
      "compatible_step beta_contract
        (Lam Prop
          (App (shift gd_false_op)
            (App (shift Z) (Var 0))))
        (Lam Prop ObjFalse)"
      using root by (rule compatible_step.Lam_body)
    show ?thesis
      using lifted
      by (simp add: pp_compose_def gd_false_op_def)
  qed
qed

lemma CEV_T8_refute_same_kind_by_right_absorption:
  assumes F_type: "\<Gamma> \<turnstile> F : Prop"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and absorption:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Eq pp_unary_ty
          (pp_compose (shift Y) (Var 0))
          (shift Y)"
    and neq:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Neg (Eq pp_unary_ty (shift X) (shift Y))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp F (Neg (pp_same_kind X Y))"
proof (rule CEV_T8_refute_same_kind_under)
  show "\<Gamma> \<turnstile> F : Prop" by (rule F_type)
  show "\<Gamma> \<turnstile> X : pp_unary_ty" by (rule X_type)
  show "\<Gamma> \<turnstile> Y : pp_unary_ty" by (rule Y_type)
  let ?Z = "Var 0"
  let ?Fs = "shift F"
  let ?P =
    "Conj
      (pp_group_member ?Z)
      (Eq pp_unary_ty
        (shift X)
        (pp_compose (shift Y) ?Z))"
  let ?S = "insert ?Fs {?P}"
  have Z_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Z : pp_unary_ty"
    by (rule typed_var0)
  have Xs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift X : pp_unary_ty"
    using X_type by (rule typed_shift_ctx)
  have Ys_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift Y : pp_unary_ty"
    using Y_type by (rule typed_shift_ctx)
  have YZ_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      pp_compose (shift Y) ?Z : pp_unary_ty"
    using Ys_type Z_type by (rule typed_pp_compose)
  have P_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_group_member[OF Z_type] Xs_type YZ_type
    by (intro has_type.Conj has_type.Eq)
  have Fs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Fs : Prop"
    using F_type by (rule typed_shift_ctx)
  have d_P:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have d_op:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (shift X)
          (pp_compose (shift Y) ?Z)"
    using d_P by (rule CEV_axiom_from_conj_right)
  have d_abs:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (pp_compose (shift Y) ?Z)
          (shift Y)"
    using absorption by (rule CEV_axiom_from.Theorem)
  have d_eq:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty (shift X) (shift Y)"
    using Xs_type YZ_type Ys_type d_op d_abs
    by (rule CEV_axiom_from_eq_trans)
  have d_neq:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Eq pp_unary_ty (shift X) (shift Y))"
    using neq by (rule CEV_axiom_from.Theorem)
  have d_false:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_eq d_neq by (rule CEV_axiom_from_contradiction)
  have under_F:
    "pp_unary_ty # \<Gamma> ; T ; {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?Fs ObjFalse"
    using Fs_type d_false by (rule CEV_axiom_from_deduction)
  have result:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P (Imp ?Fs ObjFalse)"
    using P_type under_F by (rule CEV_axiom_from_singleton_imp)
  show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P (shift (Imp F ObjFalse))"
    using result by simp
qed

lemma CEV_T8_true_absorption:
  "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq pp_unary_ty
      (pp_compose (shift gd_true_op) (Var 0))
      (shift gd_true_op)"
  using CEV_pp_compose_gd_true_left[
    where \<Gamma> = "pp_unary_ty # \<Gamma>" and Z = "Var 0"]
  by (intro CEV_axiom_proves.Base) simp

lemma CEV_T8_false_absorption:
  "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq pp_unary_ty
      (pp_compose (shift gd_false_op) (Var 0))
      (shift gd_false_op)"
  using CEV_pp_compose_gd_false_left[
    where \<Gamma> = "pp_unary_ty # \<Gamma>" and Z = "Var 0"]
  by (intro CEV_axiom_proves.Base) simp

lemma CEV_T8_shifted_neq_Id_Ktop:
  "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Neg (Eq pp_unary_ty
      (shift pp_identity_operator) (shift gd_true_op))"
proof -
  have local:
    "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Eq pp_unary_ty pp_identity_operator gd_true_op)"
  proof (rule CEVs_neq_sym)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      gd_true_op : pp_unary_ty" by (rule typed_gd_true_op)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      pp_identity_operator : pp_unary_ty"
      by (rule typed_pp_identity_operator)
    show "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Eq pp_unary_ty gd_true_op pp_identity_operator)"
      by (rule opneq_Ktop_Id)
  qed
  show ?thesis using local CEV_axiom_from_empty_iff by simp
qed

lemma CEV_T8_shifted_neq_Box_Ktop:
  "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Neg (Eq pp_unary_ty (shift gd_box_op) (shift gd_true_op))"
proof -
  have local:
    "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Eq pp_unary_ty gd_box_op gd_true_op)"
  proof (rule CEVs_neq_sym)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      gd_true_op : pp_unary_ty" by (rule typed_gd_true_op)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      gd_box_op : pp_unary_ty" by (rule typed_gd_box_op)
    show "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Eq pp_unary_ty gd_true_op gd_box_op)"
      by (rule opneq_Ktop_Box)
  qed
  show ?thesis using local CEV_axiom_from_empty_iff by simp
qed

lemma CEV_T8_shifted_neq_Diamond_Ktop:
  "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Neg (Eq pp_unary_ty
      (shift pp_T8_diamond_operator) (shift gd_true_op))"
proof -
  have dia_false:
    "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App pp_T8_diamond_operator ObjFalse)"
  proof (rule CEVs_app_false)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      pp_T8_diamond_operator : pp_unary_ty"
      by (rule typed_pp_T8_diamond_operator)
    show "pp_unary_ty # \<Gamma> \<turnstile> ObjFalse : Prop"
      by (rule typed_ObjFalse)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      Neg (Eq Prop ObjFalse ObjFalse) : Prop"
      by (intro has_type.Neg has_type.Eq typed_ObjFalse)
    show "compatible_step beta_contract
      (App pp_T8_diamond_operator ObjFalse)
      (Neg (Eq Prop ObjFalse ObjFalse))"
      by (rule pp_T8_diamond_operator_beta)
    show "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Neg (Eq Prop ObjFalse ObjFalse))"
    proof -
      have ref:
        "pp_unary_ty # \<Gamma> ; T ; {}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ObjFalse ObjFalse"
        using typed_ObjFalse
        by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base
          CEV_proves.CE CE_proves.C C_proves.H H_proves.Ref)
      have dneg:
        "pp_unary_ty # \<Gamma> ; T ; {}
          \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
            Neg (Neg (Eq Prop ObjFalse ObjFalse))"
      proof -
        let ?E = "Eq Prop ObjFalse ObjFalse"
        have taut:
          "pp_unary_ty # \<Gamma> \<turnstile>\<^sub>CEV
            Imp ?E (Neg (Neg ?E))"
        proof (rule CEV_prop_tautology)
          show "prop_tautology (pp_unary_ty # \<Gamma>)
            (Imp ?E (Neg (Neg ?E)))"
            unfolding prop_tautology_def
            using has_type.Eq[OF typed_ObjFalse typed_ObjFalse]
            by auto
        qed
        have local_taut:
          "pp_unary_ty # \<Gamma> ; T ; {}
            \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
              Imp ?E (Neg (Neg ?E))"
          using taut
          by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
        show ?thesis
          using ref local_taut by (rule CEV_axiom_from.MP)
      qed
      show ?thesis by (rule dneg)
    qed
  qed
  have top_true:
    "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gd_true_op ObjFalse"
    by (rule val_Ktop_at_false)
  have reverse:
    "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Eq pp_unary_ty gd_true_op pp_T8_diamond_operator)"
    using typed_gd_true_op typed_pp_T8_diamond_operator
      typed_ObjFalse top_true dia_false
    by (rule CEVs_operator_neq_via_witness)
  have forward:
    "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Eq pp_unary_ty pp_T8_diamond_operator gd_true_op)"
    using typed_gd_true_op typed_pp_T8_diamond_operator reverse
    by (rule CEVs_neq_sym)
  show ?thesis using forward CEV_axiom_from_empty_iff by simp
qed

lemma CEV_T8_shifted_neq_Id_Kbot:
  "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Neg (Eq pp_unary_ty
      (shift pp_identity_operator) (shift gd_false_op))"
proof -
  have local:
    "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Eq pp_unary_ty pp_identity_operator gd_false_op)"
    using typed_pp_identity_operator typed_gd_false_op
      typed_ObjTrue val_Id_at_true val_Kbot_at_true
    by (rule CEVs_operator_neq_via_witness)
  show ?thesis using local CEV_axiom_from_empty_iff by simp
qed

lemma CEV_T8_shifted_neq_Box_Kbot:
  "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Neg (Eq pp_unary_ty (shift gd_box_op) (shift gd_false_op))"
proof -
  have local:
    "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Eq pp_unary_ty gd_box_op gd_false_op)"
    using typed_gd_box_op typed_gd_false_op
      typed_ObjTrue val_Box_at_true val_Kbot_at_true
    by (rule CEVs_operator_neq_via_witness)
  show ?thesis using local CEV_axiom_from_empty_iff by simp
qed

lemma CEV_T8_shifted_neq_Diamond_Kbot:
  "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Neg (Eq pp_unary_ty
      (shift pp_T8_diamond_operator) (shift gd_false_op))"
proof -
  have dia_true:
    "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        App pp_T8_diamond_operator ObjTrue"
  proof (rule CEVs_app_true)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      pp_T8_diamond_operator : pp_unary_ty"
      by (rule typed_pp_T8_diamond_operator)
    show "pp_unary_ty # \<Gamma> \<turnstile> ObjTrue : Prop"
      by (rule typed_ObjTrue)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      Neg (Eq Prop ObjTrue ObjFalse) : Prop"
      by (intro has_type.Neg has_type.Eq typed_ObjTrue typed_ObjFalse)
    show "compatible_step beta_contract
      (App pp_T8_diamond_operator ObjTrue)
      (Neg (Eq Prop ObjTrue ObjFalse))"
      by (rule pp_T8_diamond_operator_beta)
    show "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq Prop ObjTrue ObjFalse)"
      by (rule CEVs_true_neq_false)
  qed
  have local:
    "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Eq pp_unary_ty pp_T8_diamond_operator gd_false_op)"
    using typed_pp_T8_diamond_operator typed_gd_false_op
      typed_ObjTrue dia_true val_Kbot_at_true
    by (rule CEVs_operator_neq_via_witness)
  show ?thesis using local CEV_axiom_from_empty_iff by simp
qed

lemma CEV_T8_shifted_neq_Ktop_Kbot:
  "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Neg (Eq pp_unary_ty (shift gd_true_op) (shift gd_false_op))"
proof -
  have local:
    "pp_unary_ty # \<Gamma> ; T ; {}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Eq pp_unary_ty gd_true_op gd_false_op)"
    by (rule opneq_Ktop_Kbot)
  show ?thesis using local CEV_axiom_from_empty_iff by simp
qed

theorem CEV_Goodman_T8a_Id_Ktop:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r)
      (Neg (pp_same_kind pp_identity_operator gd_true_op))"
  using typed_pp_fun_prime[OF r_type]
    typed_pp_identity_operator typed_gd_true_op
    CEV_T8_true_absorption CEV_T8_shifted_neq_Id_Ktop
  by (rule CEV_T8_refute_same_kind_by_right_absorption)

theorem CEV_Goodman_T8a_Box_Ktop:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r)
      (Neg (pp_same_kind gd_box_op gd_true_op))"
  using typed_pp_fun_prime[OF r_type]
    typed_gd_box_op typed_gd_true_op
    CEV_T8_true_absorption CEV_T8_shifted_neq_Box_Ktop
  by (rule CEV_T8_refute_same_kind_by_right_absorption)

theorem CEV_Goodman_T8a_Diamond_Ktop:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r)
      (Neg
        (pp_same_kind pp_T8_diamond_operator gd_true_op))"
  using typed_pp_fun_prime[OF r_type]
    typed_pp_T8_diamond_operator typed_gd_true_op
    CEV_T8_true_absorption CEV_T8_shifted_neq_Diamond_Ktop
  by (rule CEV_T8_refute_same_kind_by_right_absorption)

theorem CEV_Goodman_T8a_Id_Kbot:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r)
      (Neg (pp_same_kind pp_identity_operator gd_false_op))"
  using typed_pp_fun_prime[OF r_type]
    typed_pp_identity_operator typed_gd_false_op
    CEV_T8_false_absorption CEV_T8_shifted_neq_Id_Kbot
  by (rule CEV_T8_refute_same_kind_by_right_absorption)

theorem CEV_Goodman_T8a_Box_Kbot:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r)
      (Neg (pp_same_kind gd_box_op gd_false_op))"
  using typed_pp_fun_prime[OF r_type]
    typed_gd_box_op typed_gd_false_op
    CEV_T8_false_absorption CEV_T8_shifted_neq_Box_Kbot
  by (rule CEV_T8_refute_same_kind_by_right_absorption)

theorem CEV_Goodman_T8a_Diamond_Kbot:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r)
      (Neg
        (pp_same_kind pp_T8_diamond_operator gd_false_op))"
  using typed_pp_fun_prime[OF r_type]
    typed_pp_T8_diamond_operator typed_gd_false_op
    CEV_T8_false_absorption CEV_T8_shifted_neq_Diamond_Kbot
  by (rule CEV_T8_refute_same_kind_by_right_absorption)

theorem CEV_Goodman_T8a_Ktop_Kbot:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r)
      (Neg (pp_same_kind gd_true_op gd_false_op))"
  using typed_pp_fun_prime[OF r_type]
    typed_gd_true_op typed_gd_false_op
    CEV_T8_false_absorption CEV_T8_shifted_neq_Ktop_Kbot
  by (rule CEV_T8_refute_same_kind_by_right_absorption)

fun pp_T8_not_same_all :: "oterm \<Rightarrow> oterm list \<Rightarrow> oterm" where
  "pp_T8_not_same_all X [] = ObjTrue"
| "pp_T8_not_same_all X (Y # Ys) =
    Conj
      (Neg (pp_same_kind X Y))
      (pp_T8_not_same_all X Ys)"

fun pp_T8_pairwise_kind_distinct :: "oterm list \<Rightarrow> oterm" where
  "pp_T8_pairwise_kind_distinct [] = ObjTrue"
| "pp_T8_pairwise_kind_distinct (X # Xs) =
    Conj
      (pp_T8_not_same_all X Xs)
      (pp_T8_pairwise_kind_distinct Xs)"

lemma typed_pp_T8_not_same_all:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Ys_type:
      "\<And>Y. Y \<in> set Ys \<Longrightarrow> \<Gamma> \<turnstile> Y : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_T8_not_same_all X Ys : Prop"
  using Ys_type
proof (induction Ys)
  case Nil
  then show ?case by (simp add: typed_ObjTrue)
next
  case (Cons Y Ys)
  have Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    using Cons.prems by simp
  have tail:
    "\<Gamma> \<turnstile> pp_T8_not_same_all X Ys : Prop"
    using Cons.IH Cons.prems by simp
  show ?case
    using typed_pp_same_kind[OF X_type Y_type] tail
    by (simp add: has_type.Conj has_type.Neg)
qed

lemma typed_pp_T8_pairwise_kind_distinct:
  assumes Xs_type:
    "\<And>X. X \<in> set Xs \<Longrightarrow> \<Gamma> \<turnstile> X : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_T8_pairwise_kind_distinct Xs : Prop"
  using Xs_type
proof (induction Xs)
  case Nil
  then show ?case by (simp add: typed_ObjTrue)
next
  case (Cons X Xs)
  have X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    using Cons.prems by simp
  have rest:
    "\<And>Y. Y \<in> set Xs \<Longrightarrow> \<Gamma> \<turnstile> Y : pp_unary_ty"
    using Cons.prems by simp
  have head:
    "\<Gamma> \<turnstile> pp_T8_not_same_all X Xs : Prop"
    using X_type rest by (rule typed_pp_T8_not_same_all)
  have tail:
    "\<Gamma> \<turnstile> pp_T8_pairwise_kind_distinct Xs : Prop"
    using Cons.IH rest by blast
  show ?case
    using head tail by (simp add: has_type.Conj)
qed

definition pp_T8_base_kind_claim :: oterm where
  "pp_T8_base_kind_claim =
    pp_T8_pairwise_kind_distinct pp_T8_base_operators"

lemma typed_pp_T8_base_kind_claim:
  "\<Gamma> \<turnstile> pp_T8_base_kind_claim : Prop"
  unfolding pp_T8_base_kind_claim_def
  using typed_pp_T8_pairwise_kind_distinct[
    OF typed_pp_T8_base_operators] .

theorem CEV_Goodman_T8a:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) pp_T8_base_kind_claim"
proof -
  let ?F = "pp_fun_prime r"
  let ?S = "{?F}"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have d_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_Id_Box:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (pp_same_kind pp_identity_operator gd_box_op)"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T8a_Id_Box[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have d_Id_Dia:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg
        (pp_same_kind
          pp_identity_operator pp_T8_diamond_operator)"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T8a_Id_Diamond[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have d_Id_T:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (pp_same_kind pp_identity_operator gd_true_op)"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T8a_Id_Ktop[OF r_type]]
    by (rule CEV_axiom_from.MP)
  have d_Id_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (pp_same_kind pp_identity_operator gd_false_op)"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T8a_Id_Kbot[OF r_type]]
    by (rule CEV_axiom_from.MP)
  have d_Box_Dia:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (pp_same_kind gd_box_op pp_T8_diamond_operator)"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T8a_Box_Diamond[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have d_Box_T:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (pp_same_kind gd_box_op gd_true_op)"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T8a_Box_Ktop[OF r_type]]
    by (rule CEV_axiom_from.MP)
  have d_Box_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (pp_same_kind gd_box_op gd_false_op)"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T8a_Box_Kbot[OF r_type]]
    by (rule CEV_axiom_from.MP)
  have d_Dia_T:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg
        (pp_same_kind pp_T8_diamond_operator gd_true_op)"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T8a_Diamond_Ktop[OF r_type]]
    by (rule CEV_axiom_from.MP)
  have d_Dia_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg
        (pp_same_kind pp_T8_diamond_operator gd_false_op)"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T8a_Diamond_Kbot[OF r_type]]
    by (rule CEV_axiom_from.MP)
  have d_T_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (pp_same_kind gd_true_op gd_false_op)"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T8a_Ktop_Kbot[OF r_type]]
    by (rule CEV_axiom_from.MP)
  have d_true:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjTrue"
    by (rule CEVs_ObjTrue)
  have d_claim:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T8_base_kind_claim"
    unfolding pp_T8_base_kind_claim_def
      pp_T8_base_operators_def
    using d_Id_Box d_Id_Dia d_Id_T d_Id_F
      d_Box_Dia d_Box_T d_Box_F
      d_Dia_T d_Dia_F d_T_F d_true
    by (simp only:
        pp_T8_pairwise_kind_distinct.simps
        pp_T8_not_same_all.simps)
      (intro CEV_axiom_from_conj_intro)
  show ?thesis
    using F_type d_claim by (rule CEV_axiom_from_singleton_imp)
qed

end
