theory Bacon_PP_Goodman_T7_Absorption
  imports 
    "Goodman_Legacy_05.Bacon_PP_Goodman_T6_TU"
begin

section \<open>Goodman T7a: absorption of the liar by the pure group\<close>

text \<open>
  Fix \<open>r\<close> with \<open>fun\<acute>(r)\<close>, put \<open>D = pp_T6_liar\<close> and
  \<open>d = D r\<close>, and define the liar family by
  \<open>a\<^sub>Z = D (Z d)\<close>.  T7a says that the identity member is false while
  some group member is true.  No classification principle is assumed.
\<close>

definition pp_T7_axioms :: "oterm set" where
  "pp_T7_axioms = insert pp_L2 pp_T6_core_PP_axioms"

definition pp_T7_full_axioms :: "oterm set" where
  "pp_T7_full_axioms = insert pp_exists_fun_prime pp_T7_axioms"

definition pp_T7_absorbed :: "oterm \<Rightarrow> oterm" where
  "pp_T7_absorbed r =
    Exists pp_unary_ty
      (Conj
        (pp_group_member (Var 0))
        (App pp_T6_liar
          (App (Var 0)
            (App pp_T6_liar (shift r)))))"

definition pp_T7_decomposition :: "oterm \<Rightarrow> oterm" where
  "pp_T7_decomposition r =
    Exists pp_unary_ty
      (Exists Prop
        (Conj
          (Conj
            (pp_pure pp_unary_ty (Var 1))
            (Conj
              (pp_fun_prime (Var 0))
              (Eq Prop
                (App pp_T6_liar (shift_by 2 r))
                (App (Var 1) (Var 0)))))
          (App (Var 1)
            (App pp_T6_liar (shift_by 2 r)))))"

definition pp_T7_absorption_result :: oterm where
  "pp_T7_absorption_result =
    Exists Prop
      (Conj
        (pp_fun_prime (Var 0))
        (Conj
          (Neg
            (App pp_T6_liar
              (App pp_T6_liar (Var 0))))
          (pp_T7_absorbed (Var 0))))"

lemma CEV_axiom_from_exists_intro_var0:
  assumes A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and d_A:
      "\<sigma> # \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
  shows "\<sigma> # \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    shift (Exists \<sigma> A)"
proof -
  have lifted_A_type:
    "\<sigma> # \<sigma> # \<Gamma> \<turnstile>
      rename (lift_ren Suc) A : Prop"
    using A_type
    by (rule renaming_preserves_typing) (case_tac n; simp)
  have var0_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by (rule typed_var0)
  have eg:
    "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (subst0 (Var 0) (rename (lift_ren Suc) A))
        (Exists \<sigma> (rename (lift_ren Suc) A))"
    using lifted_A_type var0_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.EG)
  have rule:
    "\<sigma> # \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp A (shift (Exists \<sigma> A))"
    using eg
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
      (simp add: shift_def subst0_rename_lift_Suc_var0)
  show ?thesis
    using d_A rule by (rule CEV_axiom_from.MP)
qed

lemma typed_pp_T7_absorbed:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> pp_T7_absorbed r : Prop"
proof -
  have Z_type:
    "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
    by (rule typed_var0)
  have rs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have ds_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      App pp_T6_liar (shift r) : Prop"
    using typed_pp_T6_liar rs_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have Zds_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      App (Var 0) (App pp_T6_liar (shift r)) : Prop"
    using Z_type ds_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have aZ_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      App pp_T6_liar
        (App (Var 0) (App pp_T6_liar (shift r))) : Prop"
    using typed_pp_T6_liar Zds_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  show ?thesis
    unfolding pp_T7_absorbed_def
    using typed_pp_group_member[OF Z_type] aZ_type
    by (intro has_type.Exists has_type.Conj)
qed

lemma typed_pp_T7_decomposition:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> pp_T7_decomposition r : Prop"
proof -
  have X_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> Var 1 : pp_unary_ty"
    by (rule has_type.Var) (simp add: lookup_def)
  have q_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have r2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> shift_by 2 r : Prop"
  proof -
    have "[Prop, pp_unary_ty] @ \<Gamma> \<turnstile>
      shift_by (length [Prop, pp_unary_ty]) r : Prop"
      using r_type by (rule shift_by_preserves_typing)
    then show ?thesis by (simp add: numeral_2_eq_2)
  qed
  have d2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile>
      App pp_T6_liar (shift_by 2 r) : Prop"
    using typed_pp_T6_liar r2_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have Xq_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile>
      App (Var 1) (Var 0) : Prop"
    using X_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xd_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile>
      App (Var 1)
        (App pp_T6_liar (shift_by 2 r)) : Prop"
    using X_type d2_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_T7_decomposition_def
    using typed_pp_pure[OF X_type] typed_pp_fun_prime[OF q_type]
      d2_type Xq_type Xd_type
    by (intro has_type.Exists has_type.Conj has_type.Eq)
qed

lemma typed_pp_T7_absorption_result:
  "\<Gamma> \<turnstile> pp_T7_absorption_result : Prop"
  unfolding pp_T7_absorption_result_def
  using typed_pp_fun_prime[OF typed_var0]
    has_type.Neg[
      OF has_type.App[
        OF typed_pp_T6_liar[unfolded pp_unary_ty_def]
          has_type.App[
            OF typed_pp_T6_liar[unfolded pp_unary_ty_def]
              typed_var0]]]
    typed_pp_T7_absorbed[OF typed_var0]
  by (intro has_type.Exists has_type.Conj)

lemma rename_lift_pp_T6_liar_T7[simp]:
  "rename (lift_ren Suc) pp_T6_liar = pp_T6_liar"
  by (simp add: pp_T6_liar_def pp_fun_prime_def
      pp_pure_def pp_Pure_def shift_by_def shift_ren_def
      eval_nat_numeral)

lemma shift_pp_T7_absorbed[simp]:
  "shift (pp_T7_absorbed r) =
    pp_T7_absorbed (shift r)"
  by (simp add: pp_T7_absorbed_def shift_def
      shift_pp_T6_liar rename_lift_Suc_after_shift)

lemma shift_by_2_pp_T7_absorbed[simp]:
  "shift_by 2 (pp_T7_absorbed r) =
    pp_T7_absorbed (shift_by 2 r)"
proof -
  have lhs:
    "shift_by 2 (pp_T7_absorbed r) =
      shift (shift (pp_T7_absorbed r))"
    using shift_shift_eq_shift_by_2[of "pp_T7_absorbed r"]
    by simp
  have rhs:
    "shift_by 2 r = shift (shift r)"
    using shift_shift_eq_shift_by_2[of r] by simp
  show ?thesis using lhs rhs by simp
qed

subsection \<open>The false identity member\<close>

theorem CEV_Goodman_T7a_identity_false:
  assumes axioms: "pp_T7_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg
        (App pp_T6_liar
          (App pp_T6_liar r)))"
proof -
  have core: "pp_T5_axioms \<subseteq> T"
    using axioms
    unfolding pp_T7_axioms_def pp_T5_axioms_def by blast
  show ?thesis
    using CEV_T5_not_Dd[OF core r_type] .
qed

subsection \<open>Failure of the identity member supplies a decomposition\<close>

lemma CEV_T7_not_Dd_implies_decomposition:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Neg
        (App pp_T6_liar
          (App pp_T6_liar r)))
      (pp_T7_decomposition r)"
proof -
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?Dd = "App ?D ?d"
  let ?P =
    "Conj
      (pp_pure pp_unary_ty (Var 1))
      (Conj
        (pp_fun_prime (Var 0))
        (Eq Prop
          (shift_by 2 ?d)
          (App (Var 1) (Var 0))))"
  let ?Xd = "App (Var 1) (shift_by 2 ?d)"
  let ?A = "Imp ?P (Neg ?Xd)"
  let ?E0 = "Exists Prop (Neg ?A)"
  let ?E1 = "Exists pp_unary_ty ?E0"
  let ?B = "Conj ?P ?Xd"
  let ?E2 = "Exists Prop ?B"
  let ?E3 = "Exists pp_unary_ty ?E2"
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using typed_pp_T6_liar r_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have Dd_type: "\<Gamma> \<turnstile> ?Dd : Prop"
    using typed_pp_T6_liar d_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have X_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> Var 1 : pp_unary_ty"
    by (rule has_type.Var) (simp add: lookup_def)
  have q_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have d2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> shift_by 2 ?d : Prop"
  proof -
    have "[Prop, pp_unary_ty] @ \<Gamma> \<turnstile>
      shift_by (length [Prop, pp_unary_ty]) ?d : Prop"
      using d_type by (rule shift_by_preserves_typing)
    then show ?thesis by (simp add: numeral_2_eq_2)
  qed
  have Xq_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile>
      App (Var 1) (Var 0) : Prop"
    using X_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xd_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?Xd : Prop"
    using X_type d2_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have P_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_pure[OF X_type] typed_pp_fun_prime[OF q_type]
      d2_type Xq_type
    by (intro has_type.Conj has_type.Eq)
  have A_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?A : Prop"
    using P_type Xd_type by (intro has_type.Imp has_type.Neg)
  have B_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?B : Prop"
    using P_type Xd_type by (rule has_type.Conj)
  have E0_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?E0 : Prop"
    using has_type.Neg[OF A_type] by (rule has_type.Exists)
  have E1_type: "\<Gamma> \<turnstile> ?E1 : Prop"
    using E0_type by (rule has_type.Exists)
  have E2_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?E2 : Prop"
    using B_type by (rule has_type.Exists)
  have E3_type: "\<Gamma> \<turnstile> ?E3 : Prop"
    using E2_type by (rule has_type.Exists)
  have liar_eq:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq Prop ?Dd (pp_T5_liar_at ?d)"
    using CEV_pp_T6_liar_apply_eq[OF d_type]
    by (rule CEV_axiom_proves.Base)
  have liar_type: "\<Gamma> \<turnstile> pp_T5_liar_at ?d : Prop"
    using d_type by (rule typed_pp_T5_liar_at)
  have neg_eq:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq Prop (Neg ?Dd) (Neg (pp_T5_liar_at ?d))"
  proof -
    have local:
      "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (Neg ?Dd) (Neg (pp_T5_liar_at ?d))"
      using Dd_type liar_type
        CEV_axiom_from.Theorem[OF liar_eq]
      by (rule CEV_axiom_from_T5_neg_cong)
    show ?thesis
      using local CEV_axiom_from_empty_iff by blast
  qed
  have neg_transfer:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Neg ?Dd) (Neg (pp_T5_liar_at ?d))"
  proof -
    have rule:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (Eq Prop (Neg ?Dd) (Neg (pp_T5_liar_at ?d)))
          (Imp (Neg ?Dd) (Neg (pp_T5_liar_at ?d)))"
      using CEV_eq_prop_implication[
        OF has_type.Neg[OF Dd_type] has_type.Neg[OF liar_type]]
      by (rule CEV_axiom_proves.Base)
    show ?thesis
      using neg_eq rule by (rule CEV_axiom_proves.MP)
  qed
  have first_dual:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Neg (pp_T5_liar_at ?d)) ?E1"
  proof -
    have raw:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (Neg (Forall pp_unary_ty (Forall Prop ?A)))
          (Exists pp_unary_ty (Neg (Forall Prop ?A)))"
      using has_type.Forall[OF A_type]
      by (intro CEV_proves.CE CE_proves.C C_proves.H
          H_proves_not_forall_imp_exists_neg)
    have inner_dual:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Neg (Forall Prop ?A)) ?E0"
    proof -
      have base:
        "pp_unary_ty # \<Gamma> \<turnstile>\<^sub>CEV
          Imp (Neg (Forall Prop ?A)) ?E0"
        using A_type
        by (intro CEV_proves.CE CE_proves.C C_proves.H
            H_proves_not_forall_imp_exists_neg)
      show ?thesis by (rule CEV_axiom_proves.Base[OF base])
    qed
    have lifted:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (Exists pp_unary_ty (Neg (Forall Prop ?A)))
          ?E1"
      using has_type.Neg[OF has_type.Forall[OF A_type]]
        E0_type inner_dual
      by (rule CEV_axiom_exists_mono)
    have first:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (Neg (Forall pp_unary_ty (Forall Prop ?A)))
          (Exists pp_unary_ty (Neg (Forall Prop ?A)))"
      by (rule CEV_axiom_proves.Base[OF raw])
    have lhs_type:
      "\<Gamma> \<turnstile>
        Neg (Forall pp_unary_ty (Forall Prop ?A)) : Prop"
      using A_type by (intro has_type.Neg has_type.Forall)
    have mid_type:
      "\<Gamma> \<turnstile>
        Exists pp_unary_ty (Neg (Forall Prop ?A)) : Prop"
      using A_type by (intro has_type.Exists has_type.Neg has_type.Forall)
    have chained:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (Neg (Forall pp_unary_ty (Forall Prop ?A)))
          ?E1"
      using lhs_type mid_type E1_type first lifted
      by (rule CEV_axiom_imp_trans_plus)
    show ?thesis
      using chained
      by (simp only: pp_T5_liar_at_explicit)
  qed
  have body_transform:
    "Prop # pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Neg ?A) ?B"
  proof (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.H H_proves.PC)
    have formula_type:
      "Prop # pp_unary_ty # \<Gamma> \<turnstile>
        Imp (Neg ?A) ?B : Prop"
      using A_type B_type by auto
    show "prop_tautology (Prop # pp_unary_ty # \<Gamma>)
      (Imp (Neg ?A) ?B)"
      unfolding prop_tautology_def
      using formula_type by auto
  qed
  have inner_transform:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?E0 ?E2"
    using has_type.Neg[OF A_type] B_type body_transform
    by (rule CEV_axiom_exists_mono)
  have outer_transform:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?E1 ?E3"
    using E0_type E2_type inner_transform
    by (rule CEV_axiom_exists_mono)
  have first:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Neg ?Dd) ?E1"
    using has_type.Neg[OF Dd_type] has_type.Neg[OF liar_type]
      E1_type neg_transfer first_dual
    by (rule CEV_axiom_imp_trans_plus)
  have final:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Neg ?Dd) ?E3"
    using has_type.Neg[OF Dd_type] E1_type E3_type
      first outer_transform
    by (rule CEV_axiom_imp_trans_plus)
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
  show ?thesis
    using final
    unfolding pp_T7_decomposition_def
    by (simp only: shift_d)
qed

subsection \<open>Same-kind transport into the liar family\<close>

lemma CEV_T7_same_kind_truth_absorbs:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (App X (App pp_T6_liar r))
      (Imp
        (pp_same_kind X pp_T6_liar)
        (pp_T7_absorbed r))"
proof -
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?H = "App X ?d"
  let ?R = "pp_T7_absorbed r"
  let ?Target = "Imp ?H ?R"
  let ?Z = "Var 0"
  let ?Xs = "shift X"
  let ?ds = "App ?D (shift r)"
  let ?GZ = "pp_group_member ?Z"
  let ?E = "Eq pp_unary_ty ?Xs (pp_compose ?D ?Z)"
  let ?P = "Conj ?GZ ?E"
  let ?aZ = "App ?D (App ?Z ?ds)"
  let ?Hs = "App ?Xs ?ds"
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using X_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using r_type by (rule typed_pp_T7_absorbed)
  have Target_type: "\<Gamma> \<turnstile> ?Target : Prop"
    using H_type R_type by (rule has_type.Imp)
  have Z_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Z : pp_unary_ty"
    by (rule typed_var0)
  have Xs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Xs : pp_unary_ty"
    using X_type by (rule typed_shift_ctx)
  have rs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have ds_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?ds : Prop"
    using typed_pp_T6_liar rs_type
    unfolding pp_unary_ty_def by (rule has_type.App)
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
  have Zds_type:
    "pp_unary_ty # \<Gamma> \<turnstile> App ?Z ?ds : Prop"
    using Z_type ds_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have aZ_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?aZ : Prop"
    using typed_pp_T6_liar Zds_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have Hs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Hs : Prop"
    using Xs_type ds_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  let ?S = "insert ?Hs {?P}"
  have d_P:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have d_Hs:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Hs"
    using Hs_type by (intro CEV_axiom_from.Assumption) simp
  have d_GZ:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?GZ"
    using d_P by (rule CEV_axiom_from_conj_left)
  have d_E:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using d_P by (rule CEV_axiom_from_conj_right)
  have app_cong:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop ?Hs (App (pp_compose ?D ?Z) ?ds)"
    using Xs_type DZ_type ds_type d_E
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have beta:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App (pp_compose ?D ?Z) ?ds) ?aZ"
    using CEV_pp_compose_apply_eq[
      OF typed_pp_T6_liar Z_type ds_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have DZds_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      App (pp_compose ?D ?Z) ?ds : Prop"
    using DZ_type ds_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Hs_eq_aZ:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?Hs ?aZ"
    using Hs_type DZds_type aZ_type app_cong beta
    by (rule CEV_axiom_from_eq_trans)
  have d_aZ:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?aZ"
    using Hs_type aZ_type d_Hs Hs_eq_aZ
    by (rule CEV_axiom_from_eq_prop_elim)
  have d_body:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj ?GZ ?aZ"
    using d_GZ d_aZ by (rule CEV_axiom_from_conj_intro)
  have body_type:
    "pp_unary_ty # \<Gamma> \<turnstile> Conj ?GZ ?aZ : Prop"
    using GZ_type aZ_type by (rule has_type.Conj)
  have d_shift_R:
    "pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s shift ?R"
    using CEV_axiom_from_exists_intro_var0[
      OF body_type d_body]
    unfolding pp_T7_absorbed_def .
  have under_Hs:
    "pp_unary_ty # \<Gamma> ; T ; {?P}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?Hs (shift ?R)"
    using Hs_type d_shift_R by (rule CEV_axiom_from_deduction)
  have P_to_target:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P (shift ?Target)"
  proof -
    have raw:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?P (Imp ?Hs (shift ?R))"
      using P_type under_Hs by (rule CEV_axiom_from_singleton_imp)
    show ?thesis using raw by (simp add: shift_pp_T6_liar)
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
  have swap:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp (pp_same_kind X ?D) (Imp ?H ?R))
        (Imp ?H (Imp (pp_same_kind X ?D) ?R))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp (pp_same_kind X ?D) (Imp ?H ?R))
        (Imp ?H (Imp (pp_same_kind X ?D) ?R)))"
      using typed_pp_same_kind[OF X_type D_type]
        H_type R_type
      by (rule prop_tautology_swap_imp)
  qed
  show ?thesis
    using same_to_target CEV_axiom_proves.Base[OF swap]
    by (rule CEV_axiom_proves.MP)
qed

subsection \<open>Weak L2 turns every liar decomposition into absorption\<close>

lemma CEV_T7_decomposition_absorbs:
  assumes axioms: "pp_T7_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Imp
        (pp_T7_decomposition r)
        (pp_T7_absorbed r))"
proof -
  let ?D = pp_T6_liar
  let ?d = "App ?D r"
  let ?F = "pp_fun_prime r"
  let ?R = "pp_T7_absorbed r"
  let ?X = "Var 1"
  let ?q = "Var 0"
  let ?r2 = "shift_by 2 r"
  let ?d2 = "App ?D ?r2"
  let ?P =
    "Conj
      (pp_pure pp_unary_ty ?X)
      (Conj
        (pp_fun_prime ?q)
        (Eq Prop ?d2 (App ?X ?q)))"
  let ?Xd = "App ?X ?d2"
  let ?B = "Conj ?P ?Xd"
  let ?F2 = "pp_fun_prime ?r2"
  let ?R2 = "pp_T7_absorbed ?r2"
  let ?S = "insert ?B {?F2}"
  have core: "pp_T6_core_PP_axioms \<subseteq> T"
    using axioms unfolding pp_T7_axioms_def by blast
  have L2_in: "pp_L2 \<in> T"
    using axioms unfolding pp_T7_axioms_def by blast
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using r_type by (rule typed_pp_T7_absorbed)
  have X_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?X : pp_unary_ty"
    by (rule has_type.Var) (simp add: lookup_def)
  have q_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?q : Prop"
    by (rule typed_var0)
  have r2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?r2 : Prop"
  proof -
    have "[Prop, pp_unary_ty] @ \<Gamma> \<turnstile>
      shift_by (length [Prop, pp_unary_ty]) r : Prop"
      using r_type by (rule shift_by_preserves_typing)
    then show ?thesis by (simp add: numeral_2_eq_2)
  qed
  have d2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?d2 : Prop"
    using typed_pp_T6_liar r2_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have Xq_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> App ?X ?q : Prop"
    using X_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xd_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?Xd : Prop"
    using X_type d2_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have P_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_pure[OF X_type] typed_pp_fun_prime[OF q_type]
      d2_type Xq_type
    by (intro has_type.Conj has_type.Eq)
  have B_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?B : Prop"
    using P_type Xd_type by (rule has_type.Conj)
  have F2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?F2 : Prop"
    using r2_type by (rule typed_pp_fun_prime)
  have R2_type:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?R2 : Prop"
    using r2_type by (rule typed_pp_T7_absorbed)
  have d_F2:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F2"
    using F2_type by (intro CEV_axiom_from.Assumption) simp
  have d_B:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?B"
    using B_type by (intro CEV_axiom_from.Assumption) simp
  have d_P:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using d_B by (rule CEV_axiom_from_conj_left)
  have d_Xd:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Xd"
    using d_B by (rule CEV_axiom_from_conj_right)
  have pure_X:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty ?X"
    using d_P by (rule CEV_axiom_from_conj_left)
  have tail:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Conj (pp_fun_prime ?q)
          (Eq Prop ?d2 (App ?X ?q))"
    using d_P by (rule CEV_axiom_from_conj_right)
  have fun_q:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime ?q"
    using tail by (rule CEV_axiom_from_conj_left)
  have decomp:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop ?d2 (App ?X ?q)"
    using tail by (rule CEV_axiom_from_conj_right)
  have collision:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App ?X ?q) (App ?D ?r2)"
    using d2_type Xq_type decomp
    by (rule CEV_axiom_from_eq_sym)
  have pure_D:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty ?D"
    using CEV_axiom_proves_mono[
      OF pp_T6_liar_pure core]
    by (rule CEV_axiom_from.Theorem)
  have l2_tail:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Conj (pp_fun_prime ?q)
          (Conj ?F2
            (Eq Prop (App ?X ?q) (App ?D ?r2)))"
    using fun_q CEV_axiom_from_conj_intro[OF d_F2 collision]
    by (rule CEV_axiom_from_conj_intro)
  have l2_middle:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Conj (pp_pure pp_unary_ty ?D)
          (Conj (pp_fun_prime ?q)
            (Conj ?F2
              (Eq Prop (App ?X ?q) (App ?D ?r2))))"
    using pure_D l2_tail by (rule CEV_axiom_from_conj_intro)
  have l2_prem:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Conj (pp_pure pp_unary_ty ?X)
          (Conj (pp_pure pp_unary_ty ?D)
            (Conj (pp_fun_prime ?q)
              (Conj ?F2
                (Eq Prop (App ?X ?q) (App ?D ?r2)))))"
    using pure_X l2_middle by (rule CEV_axiom_from_conj_intro)
  have l2_rule:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp
          (Conj (pp_pure pp_unary_ty ?X)
            (Conj (pp_pure pp_unary_ty ?D)
              (Conj (pp_fun_prime ?q)
                (Conj ?F2
                  (Eq Prop (App ?X ?q) (App ?D ?r2))))))
          (pp_same_kind ?X ?D)"
    using CEV_axiom_L2_instance[
      OF L2_in X_type typed_pp_T6_liar q_type r2_type]
    by (rule CEV_axiom_from.Theorem)
  have same:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_same_kind ?X ?D"
    using l2_prem l2_rule by (rule CEV_axiom_from.MP)
  have carry:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?Xd (Imp (pp_same_kind ?X ?D) ?R2)"
    using CEV_T7_same_kind_truth_absorbs[
      OF r2_type X_type]
    by (rule CEV_axiom_from.Theorem)
  have carry_step:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp (pp_same_kind ?X ?D) ?R2"
    using d_Xd carry by (rule CEV_axiom_from.MP)
  have d_R2:
    "Prop # pp_unary_ty # \<Gamma> ; T ; ?S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R2"
    using same carry_step by (rule CEV_axiom_from.MP)
  have under_B:
    "Prop # pp_unary_ty # \<Gamma> ; T ; {?F2}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?B ?R2"
    using B_type d_R2 by (rule CEV_axiom_from_deduction)
  have F2_to_B_R2:
    "Prop # pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F2 (Imp ?B ?R2)"
    using F2_type under_B by (rule CEV_axiom_from_singleton_imp)
  have swap:
    "Prop # pp_unary_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp ?F2 (Imp ?B ?R2))
        (Imp ?B (Imp ?F2 ?R2))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology (Prop # pp_unary_ty # \<Gamma>)
      (Imp
        (Imp ?F2 (Imp ?B ?R2))
        (Imp ?B (Imp ?F2 ?R2)))"
      using F2_type B_type R2_type
      by (rule prop_tautology_swap_imp)
  qed
  have deepest:
    "Prop # pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?B (Imp ?F2 ?R2)"
    using F2_to_B_R2 CEV_axiom_proves.Base[OF swap]
    by (rule CEV_axiom_proves.MP)
  let ?K1 = "Exists Prop ?B"
  have K1_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?K1 : Prop"
    using B_type by (rule has_type.Exists)
  have F1_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift ?F : Prop"
    using F_type by (rule typed_shift_ctx)
  have R1_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift ?R : Prop"
    using R_type by (rule typed_shift_ctx)
  have inner:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?K1 (Imp (shift ?F) (shift ?R))"
  proof (rule CEV_axiom_proves.Inst)
    show "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?B : Prop"
      by (rule B_type)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      Imp (shift ?F) (shift ?R) : Prop"
      using F1_type R1_type by (rule has_type.Imp)
    show "Prop # pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?B (shift (Imp (shift ?F) (shift ?R)))"
      using deepest
      by (simp add: shift_shift_eq_shift_by_2
          shift_pp_T6_liar)
  qed
  have outer:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Exists pp_unary_ty ?K1)
        (Imp ?F ?R)"
  proof (rule CEV_axiom_proves.Inst)
    show "pp_unary_ty # \<Gamma> \<turnstile> ?K1 : Prop"
      by (rule K1_type)
    show "\<Gamma> \<turnstile> Imp ?F ?R : Prop"
      using F_type R_type by (rule has_type.Imp)
    show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?K1 (shift (Imp ?F ?R))"
      using inner by simp
  qed
  have decomp_to:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_T7_decomposition r) (Imp ?F ?R)"
    using outer
    unfolding pp_T7_decomposition_def .
  have final_swap:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp (pp_T7_decomposition r) (Imp ?F ?R))
        (Imp ?F (Imp (pp_T7_decomposition r) ?R))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp (pp_T7_decomposition r) (Imp ?F ?R))
        (Imp ?F (Imp (pp_T7_decomposition r) ?R)))"
      using typed_pp_T7_decomposition[OF r_type]
        F_type R_type
      by (rule prop_tautology_swap_imp)
  qed
  show ?thesis
    using decomp_to CEV_axiom_proves.Base[OF final_swap]
    by (rule CEV_axiom_proves.MP)
qed

subsection \<open>The complete T7a theorem\<close>

theorem CEV_Goodman_T7a_parameter:
  assumes axioms: "pp_T7_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Conj
        (Neg
          (App pp_T6_liar
            (App pp_T6_liar r)))
        (pp_T7_absorbed r))"
proof -
  let ?F = "pp_fun_prime r"
  let ?N =
    "Neg (App pp_T6_liar (App pp_T6_liar r))"
  let ?D = "pp_T7_decomposition r"
  let ?R = "pp_T7_absorbed r"
  let ?S = "{?F}"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have N_type: "\<Gamma> \<turnstile> ?N : Prop"
    using typed_pp_T6_liar r_type
    unfolding pp_unary_ty_def
    by (intro has_type.Neg has_type.App)
  have D_type: "\<Gamma> \<turnstile> ?D : Prop"
    using r_type by (rule typed_pp_T7_decomposition)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using r_type by (rule typed_pp_T7_absorbed)
  have d_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have not_rule:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?F ?N"
    using CEV_Goodman_T7a_identity_false[
      OF axioms r_type]
    by (rule CEV_axiom_from.Theorem)
  have d_N:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?N"
    using d_F not_rule by (rule CEV_axiom_from.MP)
  have decomp_rule:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?N ?D"
    using CEV_T7_not_Dd_implies_decomposition[
      OF r_type]
    by (rule CEV_axiom_from.Theorem)
  have d_D:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?D"
    using d_N decomp_rule by (rule CEV_axiom_from.MP)
  have absorption_rule:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F (Imp ?D ?R)"
    using CEV_T7_decomposition_absorbs[
      OF axioms r_type]
    by (rule CEV_axiom_from.Theorem)
  have absorption_step:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?D ?R"
    using d_F absorption_rule by (rule CEV_axiom_from.MP)
  have d_R:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
    using d_D absorption_step by (rule CEV_axiom_from.MP)
  have pair:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj ?N ?R"
    using d_N d_R by (rule CEV_axiom_from_conj_intro)
  show ?thesis
    using F_type pair by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_Goodman_T7a:
  "[] ; pp_T7_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_T7_absorption_result"
proof -
  let ?r = "Var 0"
  let ?F = "pp_fun_prime ?r"
  let ?N =
    "Neg (App pp_T6_liar (App pp_T6_liar ?r))"
  let ?R = "pp_T7_absorbed ?r"
  let ?B = "Conj ?F (Conj ?N ?R)"
  have r_type: "[Prop] \<turnstile> ?r : Prop"
    by (rule typed_var0)
  have F_type: "[Prop] \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have N_type: "[Prop] \<turnstile> ?N : Prop"
    using typed_pp_T6_liar r_type
    unfolding pp_unary_ty_def
    by (intro has_type.Neg has_type.App)
  have R_type: "[Prop] \<turnstile> ?R : Prop"
    using r_type by (rule typed_pp_T7_absorbed)
  have B_type: "[Prop] \<turnstile> ?B : Prop"
    using F_type N_type R_type
    by (intro has_type.Conj)
  have core: "pp_T7_axioms \<subseteq> pp_T7_full_axioms"
    unfolding pp_T7_full_axioms_def by blast
  have pair_rule:
    "[Prop] ; pp_T7_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (Conj ?N ?R)"
    using CEV_Goodman_T7a_parameter[
      OF core r_type] .
  have repack:
    "[Prop] ; pp_T7_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F ?B"
  proof -
    have taut:
      "[Prop] \<turnstile>\<^sub>CEV
        Imp
          (Imp ?F (Conj ?N ?R))
          (Imp ?F ?B)"
    proof (rule CEV_prop_tautology)
      show "prop_tautology [Prop]
        (Imp
          (Imp ?F (Conj ?N ?R))
          (Imp ?F ?B))"
        unfolding prop_tautology_def
        using F_type N_type R_type by auto
    qed
    show ?thesis
      using pair_rule CEV_axiom_proves.Base[OF taut]
      by (rule CEV_axiom_proves.MP)
  qed
  have under_F:
    "[Prop] ; pp_T7_full_axioms ; {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?B"
  proof -
    have d_F:
      "[Prop] ; pp_T7_full_axioms ; {?F}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
      using F_type by (intro CEV_axiom_from.Assumption) simp
    have rule:
      "[Prop] ; pp_T7_full_axioms ; {?F}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?F ?B"
      using repack by (rule CEV_axiom_from.Theorem)
    show ?thesis
      using d_F rule by (rule CEV_axiom_from.MP)
  qed
  have witness:
    "[Prop] ; pp_T7_full_axioms ; {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        shift pp_T7_absorption_result"
    using CEV_axiom_from_exists_intro_var0[
      OF B_type under_F]
    unfolding pp_T7_absorption_result_def .
  have witness_rule:
    "[Prop] ; pp_T7_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (shift pp_T7_absorption_result)"
    using F_type witness by (rule CEV_axiom_from_singleton_imp)
  have exists_rule:
    "[] ; pp_T7_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp pp_exists_fun_prime pp_T7_absorption_result"
  proof -
    have raw:
      "[] ; pp_T7_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Exists Prop ?F) pp_T7_absorption_result"
    proof (rule CEV_axiom_proves.Inst)
      show "[Prop] \<turnstile> ?F : Prop" by (rule F_type)
      show "[] \<turnstile> pp_T7_absorption_result : Prop"
        by (rule typed_pp_T7_absorption_result)
      show "[Prop] ; pp_T7_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?F (shift pp_T7_absorption_result)"
        by (rule witness_rule)
    qed
    show ?thesis
      using raw unfolding pp_exists_fun_prime_def .
  qed
  have exists_fun:
    "[] ; pp_T7_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_exists_fun_prime"
  proof (rule CEV_axiom_proves.Axiom)
    show "pp_exists_fun_prime \<in> pp_T7_full_axioms"
      unfolding pp_T7_full_axioms_def by blast
    show "[] \<turnstile> pp_exists_fun_prime : Prop"
      by (rule typed_pp_exists_fun_prime)
  qed
  show ?thesis
    using exists_fun exists_rule by (rule CEV_axiom_proves.MP)
qed

corollary CEV_Goodman_T7a_mono:
  assumes "pp_T7_full_axioms \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_T7_absorption_result"
  using CEV_Goodman_T7a assms
  by (rule CEV_axiom_proves_mono)

end
