theory Bacon_PP_Goodman_T6_Inv
  imports 
    "Goodman_Legacy_04.Bacon_PP_Goodman_Proliferation"
begin

section \<open>Goodman T6 with weak L2 and Inv\<close>

text \<open>
  This theory proves the first of Goodman's four T6 inconsistency results.
  Its exact closed axiom stock is the one fixed in
  \<open>Bacon_PP_T6_Encoding\<close>: purity, application closure, PP at the unary
  operator type, existence of a \<open>fun\<acute>\<close> proposition, weak L2, and Inv.
\<close>

subsection \<open>Elimination rules for weak L2 and Inv\<close>

lemma rename_Suc_eq_shift_T6:
  "rename Suc M = shift M"
  by (simp add: shift_def)

lemma subst_pp_pure_term[simp]:
  "subst s (pp_pure \<sigma> M) = pp_pure \<sigma> (subst s M)"
  by (simp add: pp_pure_def pp_Pure_def)

lemma subst_pp_fun_prime_term[simp]:
  "subst s (pp_fun_prime p) = pp_fun_prime (subst s p)"
  by (simp add: pp_fun_prime_def
      shift_shift_eq_shift_by_2[symmetric] subst_lift_shift)

lemma subst_pp_identity_operator[simp]:
  "subst s pp_identity_operator = pp_identity_operator"
  by (simp add: pp_identity_operator_def)

lemma subst_pp_compose_term[simp]:
  "subst s (pp_compose F G) =
    pp_compose (subst s F) (subst s G)"
  by (simp add: pp_compose_def subst_lift_shift)

lemma subst_pp_group_member_term[simp]:
  "subst s (pp_group_member Z) = pp_group_member (subst s Z)"
  by (simp add: pp_group_member_def pp_reversible_def subst_lift_shift)

lemma subst_pp_same_kind_term[simp]:
  "subst s (pp_same_kind X Y) =
    pp_same_kind (subst s X) (subst s Y)"
  by (simp add: pp_same_kind_def subst_lift_shift)

lemma lift3_subst_outer[simp]:
  "lift_subst (lift_subst (lift_subst (case_nat X Var))) 3 =
    shift (shift (shift X))"
  by (simp add: shift_def rename_comp comp_def eval_nat_numeral)

lemma lift3_subst_middle[simp]:
  "lift_subst (lift_subst (lift_subst (case_nat X Var))) 2 = Var 2"
  by (simp add: eval_nat_numeral)

lemma lift2_subst_outer[simp]:
  "lift_subst (lift_subst (case_nat X Var)) 2 = shift (shift X)"
  by (simp add: shift_def rename_comp comp_def eval_nat_numeral)

lemma lift2_subst_middle[simp]:
  "lift_subst (lift_subst (case_nat X Var)) 1 = Var 1"
  by (simp add: eval_nat_numeral)

lemma lift1_subst_outer[simp]:
  "lift_subst (case_nat X Var) 1 = shift X"
  by (simp add: shift_def eval_nat_numeral)

lemma subst_lift2_shift3_cancel[simp]:
  "subst (lift_subst (lift_subst (case_nat Y Var)))
      (shift (shift (shift X))) = shift (shift X)"
proof -
  have cancel:
    "subst (case_nat Y Var) (shift X) = X"
    using subst0_shift[of Y X] unfolding subst0_def .
  show ?thesis
    by (simp only: subst_lift_shift cancel)
qed

lemma subst_lift1_shift2_cancel[simp]:
  "subst (lift_subst (case_nat p Var))
      (shift (shift X)) = shift X"
proof -
  have cancel:
    "subst (case_nat p Var) (shift X) = X"
    using subst0_shift[of p X] unfolding subst0_def .
  show ?thesis
    by (simp only: subst_lift_shift cancel)
qed

lemma CEV_axiom_L2_instance:
  assumes L2_in: "pp_L2 \<in> T"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure pp_unary_ty X)
        (Conj
          (pp_pure pp_unary_ty Y)
          (Conj
            (pp_fun_prime p)
            (Conj
              (pp_fun_prime q)
              (Eq Prop (App X p) (App Y q))))))
      (pp_same_kind X Y)"
proof -
  have L2_type: "\<Gamma> \<turnstile> pp_L2 : Prop"
    by (rule infer_type_sound)
      (simp add: pp_L2_def pp_fun_prime_def pp_same_kind_def
        pp_group_member_def pp_reversible_def pp_compose_def
        pp_identity_operator_def pp_unary_ty_def pp_pure_def pp_Pure_def
        shift_by_def shift_ren_def shift_def lookup_def)
  have d0: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_L2"
    using L2_in L2_type by (rule CEV_axiom_proves.Axiom)
  have d1:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall pp_unary_ty
        (Forall Prop
          (Forall Prop
            (Imp
              (Conj
                (pp_pure pp_unary_ty (shift (shift (shift X))))
                (Conj
                  (pp_pure pp_unary_ty (Var 2))
                  (Conj
                    (pp_fun_prime (Var 1))
                    (Conj
                      (pp_fun_prime (Var 0))
                      (Eq Prop
                        (App (shift (shift (shift X))) (Var 1))
                        (App (Var 2) (Var 0)))))))
              (pp_same_kind (shift (shift (shift X))) (Var 2)))))"
  proof -
    have raw:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        subst0 X
          (Forall pp_unary_ty
            (Forall Prop
              (Forall Prop
                (Imp
                  (Conj
                    (pp_pure pp_unary_ty (Var 3))
                    (Conj
                      (pp_pure pp_unary_ty (Var 2))
                      (Conj
                        (pp_fun_prime (Var 1))
                        (Conj
                          (pp_fun_prime (Var 0))
                          (Eq Prop
                            (App (Var 3) (Var 1))
                            (App (Var 2) (Var 0)))))))
                  (pp_same_kind (Var 3) (Var 2))))))"
      using L2_type X_type d0
      unfolding pp_L2_def
      by (rule CEV_axiom_UI_typed)
    show ?thesis
      using raw
      by (simp add: subst0_def)
  qed
  have d2:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall Prop
        (Forall Prop
          (Imp
            (Conj
              (pp_pure pp_unary_ty (shift (shift X)))
              (Conj
                (pp_pure pp_unary_ty (shift (shift Y)))
                (Conj
                  (pp_fun_prime (Var 1))
                  (Conj
                    (pp_fun_prime (Var 0))
                    (Eq Prop
                      (App (shift (shift X)) (Var 1))
                      (App (shift (shift Y)) (Var 0)))))))
            (pp_same_kind (shift (shift X)) (shift (shift Y)))))"
  proof -
    have raw:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        subst0 Y
          (Forall Prop
            (Forall Prop
              (Imp
                (Conj
                  (pp_pure pp_unary_ty (shift (shift (shift X))))
                  (Conj
                    (pp_pure pp_unary_ty (Var 2))
                    (Conj
                      (pp_fun_prime (Var 1))
                      (Conj
                        (pp_fun_prime (Var 0))
                        (Eq Prop
                          (App (shift (shift (shift X))) (Var 1))
                          (App (Var 2) (Var 0)))))))
                (pp_same_kind (shift (shift (shift X))) (Var 2)))))"
      using CEV_axiom_proves_formula[OF d1] Y_type d1
      by (rule CEV_axiom_UI_typed)
    show ?thesis
      using raw
      by (simp add: subst0_def subst_lift_shift
          subst0_shift[of Y X, unfolded subst0_def])
  qed
  have d3:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Forall Prop
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift X))
            (Conj
              (pp_pure pp_unary_ty (shift Y))
              (Conj
                (pp_fun_prime (shift p))
                (Conj
                  (pp_fun_prime (Var 0))
                  (Eq Prop
                    (App (shift X) (shift p))
                    (App (shift Y) (Var 0)))))))
          (pp_same_kind (shift X) (shift Y)))"
  proof -
    have raw:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        subst0 p
          (Forall Prop
            (Imp
              (Conj
                (pp_pure pp_unary_ty (shift (shift X)))
                (Conj
                  (pp_pure pp_unary_ty (shift (shift Y)))
                  (Conj
                    (pp_fun_prime (Var 1))
                    (Conj
                      (pp_fun_prime (Var 0))
                      (Eq Prop
                        (App (shift (shift X)) (Var 1))
                        (App (shift (shift Y)) (Var 0)))))))
              (pp_same_kind (shift (shift X)) (shift (shift Y)))))"
      using CEV_axiom_proves_formula[OF d2] p_type d2
      by (rule CEV_axiom_UI_typed)
    show ?thesis
      using raw
      by (simp add: subst0_def subst_lift_shift
          rename_Suc_eq_shift_T6
          subst0_shift[of p X, unfolded subst0_def]
          subst0_shift[of p Y, unfolded subst0_def])
  qed
  have raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 q
        (Imp
          (Conj
            (pp_pure pp_unary_ty (shift X))
            (Conj
              (pp_pure pp_unary_ty (shift Y))
              (Conj
                (pp_fun_prime (shift p))
                (Conj
                  (pp_fun_prime (Var 0))
                  (Eq Prop
                    (App (shift X) (shift p))
                    (App (shift Y) (Var 0)))))))
          (pp_same_kind (shift X) (shift Y)))"
    using CEV_axiom_proves_formula[OF d3] q_type d3
    by (rule CEV_axiom_UI_typed)
  show ?thesis
    using raw
    by (simp add: subst0_def subst_lift_shift
        subst0_shift[of q X, unfolded subst0_def]
        subst0_shift[of q Y, unfolded subst0_def]
        subst0_shift[of q p, unfolded subst0_def])
qed

lemma subst_pp_negation_operator[simp]:
  "subst s pp_negation_operator = pp_negation_operator"
  by (simp add: pp_negation_operator_def)

lemma CEV_axiom_Inv_instance:
  assumes Inv_in: "pp_Inv \<in> T"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_group_member Z)
      (Disj
        (Eq pp_unary_ty Z pp_identity_operator)
        (Eq pp_unary_ty Z pp_negation_operator))"
proof -
  have Inv_type: "\<Gamma> \<turnstile> pp_Inv : Prop"
    by (rule infer_type_sound)
      (simp add: pp_Inv_def pp_group_member_def pp_reversible_def
        pp_compose_def pp_identity_operator_def pp_negation_operator_def
        pp_unary_ty_def pp_pure_def pp_Pure_def shift_def lookup_def)
  have d_Inv: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_Inv"
    using Inv_in Inv_type by (rule CEV_axiom_proves.Axiom)
  have raw:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 Z
        (pp_group_member (Var 0) \<longleftrightarrow>\<^sub>o
          Disj
            (Eq pp_unary_ty (Var 0) pp_identity_operator)
            (Eq pp_unary_ty (Var 0) pp_negation_operator))"
    using Inv_type Z_type d_Inv
    unfolding pp_Inv_def
    by (rule CEV_axiom_UI_typed)
  have bicond:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (pp_group_member Z \<longleftrightarrow>\<^sub>o
        Disj
          (Eq pp_unary_ty Z pp_identity_operator)
          (Eq pp_unary_ty Z pp_negation_operator))"
    using raw by (simp add: subst0_def)
  have local:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (pp_group_member Z)
        (Disj
          (Eq pp_unary_ty Z pp_identity_operator)
          (Eq pp_unary_ty Z pp_negation_operator))"
    using CEV_axiom_from.Theorem[OF bicond]
    by (rule CEV_axiom_from_conj_left)
  show ?thesis
    using local CEV_axiom_from_empty_iff by blast
qed

lemma CEV_axiom_from_disj_left_intro:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and d_A: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Disj A B"
proof -
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Disj A B)"
    using A_type B_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_disj_left_intro)
  show ?thesis
    using d_A
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[OF taut]]
    by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_disj_right_intro:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and d_B: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Disj A B"
proof -
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp B (Disj A B)"
    using A_type B_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_disj_right_intro)
  show ?thesis
    using d_B
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[OF taut]]
    by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_same_kind_Inv_cases:
  assumes Inv_in: "pp_Inv \<in> T"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_same_kind X Y)
      (Disj
        (Eq pp_unary_ty X
          (pp_compose Y pp_identity_operator))
        (Eq pp_unary_ty X
          (pp_compose Y pp_negation_operator)))"
proof -
  let ?I = pp_identity_operator
  let ?N = pp_negation_operator
  let ?Z = "Var 0"
  let ?Xs = "shift X"
  let ?Ys = "shift Y"
  let ?GZ = "pp_group_member ?Z"
  let ?E = "Eq pp_unary_ty ?Xs (pp_compose ?Ys ?Z)"
  let ?P = "Conj ?GZ ?E"
  let ?QI = "Eq pp_unary_ty X (pp_compose Y ?I)"
  let ?QN = "Eq pp_unary_ty X (pp_compose Y ?N)"
  let ?Q = "Disj ?QI ?QN"
  let ?Z_I = "Eq pp_unary_ty ?Z ?I"
  let ?Z_N = "Eq pp_unary_ty ?Z ?N"
  have Z_type: "pp_unary_ty # \<Gamma> \<turnstile> ?Z : pp_unary_ty"
    by (rule typed_var0)
  have Xs_type: "pp_unary_ty # \<Gamma> \<turnstile> ?Xs : pp_unary_ty"
    using X_type by (rule typed_shift_ctx)
  have Ys_type: "pp_unary_ty # \<Gamma> \<turnstile> ?Ys : pp_unary_ty"
    using Y_type by (rule typed_shift_ctx)
  have I_type: "pp_unary_ty # \<Gamma> \<turnstile> ?I : pp_unary_ty"
    by (rule typed_pp_identity_operator)
  have N_type: "pp_unary_ty # \<Gamma> \<turnstile> ?N : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  have YZ_type:
    "pp_unary_ty # \<Gamma> \<turnstile> pp_compose ?Ys ?Z : pp_unary_ty"
    using Ys_type Z_type by (rule typed_pp_compose)
  have YI_type:
    "pp_unary_ty # \<Gamma> \<turnstile> pp_compose ?Ys ?I : pp_unary_ty"
    using Ys_type I_type by (rule typed_pp_compose)
  have YN_type:
    "pp_unary_ty # \<Gamma> \<turnstile> pp_compose ?Ys ?N : pp_unary_ty"
    using Ys_type N_type by (rule typed_pp_compose)
  have E_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?E : Prop"
    using Xs_type YZ_type by (rule has_type.Eq)
  have GZ_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?GZ : Prop"
    using Z_type by (rule typed_pp_group_member)
  have P_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?P : Prop"
    using GZ_type E_type by (rule has_type.Conj)
  have QI_type: "\<Gamma> \<turnstile> ?QI : Prop"
    using X_type typed_pp_compose[OF Y_type typed_pp_identity_operator]
    by (rule has_type.Eq)
  have QN_type: "\<Gamma> \<turnstile> ?QN : Prop"
    using X_type typed_pp_compose[OF Y_type typed_pp_negation_operator]
    by (rule has_type.Eq)
  have Q_type: "\<Gamma> \<turnstile> ?Q : Prop"
    using QI_type QN_type by (rule has_type.Disj)
  have QI_shift_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      Eq pp_unary_ty ?Xs (pp_compose ?Ys ?I) : Prop"
    using Xs_type YI_type by (rule has_type.Eq)
  have QN_shift_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      Eq pp_unary_ty ?Xs (pp_compose ?Ys ?N) : Prop"
    using Xs_type YN_type by (rule has_type.Eq)
  have ZI_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Z_I : Prop"
    using Z_type I_type by (rule has_type.Eq)
  have ZN_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Z_N : Prop"
    using Z_type N_type by (rule has_type.Eq)
  have P_to_shift_Q:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?P (shift ?Q)"
  proof -
    let ?S = "{?P}"
    have d_P:
      "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
      using P_type by (intro CEV_axiom_from.Assumption) simp
    have d_GZ:
      "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?GZ"
      using d_P by (rule CEV_axiom_from_conj_left)
    have d_E:
      "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
      using d_P by (rule CEV_axiom_from_conj_right)
    have inv_rule:
      "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?GZ (Disj ?Z_I ?Z_N)"
      using CEV_axiom_Inv_instance[OF Inv_in Z_type]
      by (rule CEV_axiom_from.Theorem)
    have z_cases:
      "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Disj ?Z_I ?Z_N"
      using d_GZ inv_rule by (rule CEV_axiom_from.MP)
    have left:
      "pp_unary_ty # \<Gamma> ; T ; insert ?Z_I ?S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Disj
            (Eq pp_unary_ty ?Xs (pp_compose ?Ys ?I))
            (Eq pp_unary_ty ?Xs (pp_compose ?Ys ?N))"
    proof -
      let ?U = "insert ?Z_I ?S"
      have z_i:
        "pp_unary_ty # \<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Z_I"
        using ZI_type
        by (intro CEV_axiom_from.Assumption) simp
      have e:
        "pp_unary_ty # \<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
        using d_E by (rule CEV_axiom_from_mono) simp
      have comp:
        "pp_unary_ty # \<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Eq pp_unary_ty
            (pp_compose ?Ys ?Z)
            (pp_compose ?Ys ?I)"
        using Z_type I_type Ys_type z_i
        by (rule CEV_axiom_from_pp_compose_cong_right)
      have result:
        "pp_unary_ty # \<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Eq pp_unary_ty ?Xs (pp_compose ?Ys ?I)"
        using Xs_type YZ_type YI_type e comp
        by (rule CEV_axiom_from_eq_trans)
      show ?thesis
        using QI_shift_type QN_shift_type result
        by (rule CEV_axiom_from_disj_left_intro)
    qed
    have right:
      "pp_unary_ty # \<Gamma> ; T ; insert ?Z_N ?S
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Disj
            (Eq pp_unary_ty ?Xs (pp_compose ?Ys ?I))
            (Eq pp_unary_ty ?Xs (pp_compose ?Ys ?N))"
    proof -
      let ?U = "insert ?Z_N ?S"
      have z_n:
        "pp_unary_ty # \<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Z_N"
        using ZN_type
        by (intro CEV_axiom_from.Assumption) simp
      have e:
        "pp_unary_ty # \<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
        using d_E by (rule CEV_axiom_from_mono) simp
      have comp:
        "pp_unary_ty # \<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Eq pp_unary_ty
            (pp_compose ?Ys ?Z)
            (pp_compose ?Ys ?N)"
        using Z_type N_type Ys_type z_n
        by (rule CEV_axiom_from_pp_compose_cong_right)
      have result:
        "pp_unary_ty # \<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Eq pp_unary_ty ?Xs (pp_compose ?Ys ?N)"
        using Xs_type YZ_type YN_type e comp
        by (rule CEV_axiom_from_eq_trans)
      show ?thesis
        using QI_shift_type QN_shift_type result
        by (rule CEV_axiom_from_disj_right_intro)
    qed
    have d_shift_Q:
      "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        shift ?Q"
    proof -
      have d_cases:
        "pp_unary_ty # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Disj
            (Eq pp_unary_ty ?Xs (pp_compose ?Ys ?I))
            (Eq pp_unary_ty ?Xs (pp_compose ?Ys ?N))"
        using
          ZI_type ZN_type
          has_type.Disj[OF QI_shift_type QN_shift_type]
          z_cases left right
        by (rule CEV_axiom_from_T5_disj_cases)
      show ?thesis
        using d_cases
        by (simp add: shift_def pp_compose_def
            pp_identity_operator_def pp_negation_operator_def
            rename_comp comp_def)
    qed
    show ?thesis
      using P_type d_shift_Q by (rule CEV_axiom_from_singleton_imp)
  qed
  have exists_to_Q:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Exists pp_unary_ty ?P) ?Q"
    using P_type Q_type P_to_shift_Q
    by (rule CEV_axiom_proves.Inst)
  show ?thesis
    using exists_to_Q
    unfolding pp_same_kind_def
    by simp
qed

subsection \<open>The Inv-classified liar matrix\<close>

lemma CEV_T6_Inv_liar_matrix:
  assumes axioms: "pp_T6_Inv_axioms \<subseteq> T"
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
  let ?I = pp_identity_operator
  let ?N = pp_negation_operator
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
  let ?XI = "Eq pp_unary_ty X (pp_compose ?D ?I)"
  let ?XN = "Eq pp_unary_ty X (pp_compose ?D ?N)"
  let ?S = "insert ?P {?F}"
  have core: "pp_T6_core_PP_axioms \<subseteq> T"
    using axioms unfolding pp_T6_Inv_axioms_def by blast
  have core_T5: "pp_T5_axioms \<subseteq> T"
    using core unfolding pp_T5_axioms_def .
  have L2_in: "pp_L2 \<in> T"
    using axioms unfolding pp_T6_Inv_axioms_def by blast
  have Inv_in: "pp_Inv \<in> T"
    using axioms unfolding pp_T6_Inv_axioms_def by blast
  have I_type: "\<Gamma> \<turnstile> ?I : pp_unary_ty"
    by (rule typed_pp_identity_operator)
  have N_type: "\<Gamma> \<turnstile> ?N : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  have D_type: "\<Gamma> \<turnstile> ?D : pp_unary_ty"
    by (rule typed_pp_T6_liar)
  have DI_type: "\<Gamma> \<turnstile> pp_compose ?D ?I : pp_unary_ty"
    using D_type I_type by (rule typed_pp_compose)
  have DN_type: "\<Gamma> \<turnstile> pp_compose ?D ?N : pp_unary_ty"
    using D_type N_type by (rule typed_pp_compose)
  have d_type: "\<Gamma> \<turnstile> ?d : Prop"
    using D_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xq_type: "\<Gamma> \<turnstile> App X q : Prop"
    using X_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xd_type: "\<Gamma> \<turnstile> App X ?d : Prop"
    using X_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Dd_type: "\<Gamma> \<turnstile> App ?D ?d : Prop"
    using D_type d_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have nd_type: "\<Gamma> \<turnstile> Neg ?d : Prop"
    using d_type by (rule has_type.Neg)
  have Dnd_type: "\<Gamma> \<turnstile> App ?D (Neg ?d) : Prop"
    using D_type nd_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_pure[OF X_type] typed_pp_fun_prime[OF q_type]
      d_type Xq_type
    by (intro has_type.Conj has_type.Eq)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using Xd_type by (rule has_type.Neg)
  have XI_type: "\<Gamma> \<turnstile> ?XI : Prop"
    using X_type DI_type by (rule has_type.Eq)
  have XN_type: "\<Gamma> \<turnstile> ?XN : Prop"
    using X_type DN_type by (rule has_type.Eq)
  have d_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_P:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have pure_X:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty X"
    using d_P by (rule CEV_axiom_from_conj_left)
  have d_tail:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_fun_prime q) (Eq Prop ?d (App X q))"
    using d_P by (rule CEV_axiom_from_conj_right)
  have fun_q:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime q"
    using d_tail by (rule CEV_axiom_from_conj_left)
  have decomp:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?d (App X q)"
    using d_tail by (rule CEV_axiom_from_conj_right)
  have pure_D:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?D"
    using CEV_axiom_proves_mono[OF pp_T6_liar_pure core]
    by (rule CEV_axiom_from.Theorem)
  have same:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App X q) (App ?D r)"
    using d_type Xq_type decomp
    by (rule CEV_axiom_from_eq_sym)
  have l2_prem:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty X)
        (Conj
          (pp_pure pp_unary_ty ?D)
          (Conj
            (pp_fun_prime q)
            (Conj
              (pp_fun_prime r)
              (Eq Prop (App X q) (App ?D r)))))"
    using pure_X
      CEV_axiom_from_conj_intro[
        OF pure_D
          CEV_axiom_from_conj_intro[
            OF fun_q
              CEV_axiom_from_conj_intro[OF d_F same]]]
    by (rule CEV_axiom_from_conj_intro)
  have l2_rule:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
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
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_same_kind X ?D"
    using l2_prem l2_rule by (rule CEV_axiom_from.MP)
  have inv_rule:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_same_kind X ?D) (Disj ?XI ?XN)"
    using CEV_axiom_same_kind_Inv_cases[
      OF Inv_in X_type D_type]
    by (rule CEV_axiom_from.Theorem)
  have cases:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Disj ?XI ?XN"
    using same_kind inv_rule by (rule CEV_axiom_from.MP)
  have left:
    "\<Gamma> ; T ; insert ?XI ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
  proof -
    let ?U = "insert ?XI ?S"
    have x_di:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?XI"
      using XI_type by (intro CEV_axiom_from.Assumption) simp
    have di_d:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty (pp_compose ?D ?I) ?D"
      using CEV_pp_compose_right_identity[OF D_type]
      by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
    have x_d:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty X ?D"
      using X_type DI_type D_type x_di di_d
      by (rule CEV_axiom_from_eq_trans)
    have xd_dd:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App X ?d) (App ?D ?d)"
      using X_type D_type d_type x_d
      by (rule CEV_axiom_from_pp_apply_cong_left)
    have not_dd:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App ?D ?d)"
    proof -
      have rule:
        "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Imp ?F (Neg (App ?D ?d))"
        using CEV_T5_not_Dd[OF core_T5 r_type]
        by (rule CEV_axiom_from.Theorem)
      have fun_r:
        "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
        using d_F by (rule CEV_axiom_from_mono) simp
      show ?thesis
        using fun_r rule by (rule CEV_axiom_from.MP)
    qed
    have neg_eq:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (Neg (App X ?d)) (Neg (App ?D ?d))"
      using Xd_type Dd_type xd_dd
      by (rule CEV_axiom_from_T5_neg_cong)
    have neg_eq_sym:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (Neg (App ?D ?d)) (Neg (App X ?d))"
      using has_type.Neg[OF Xd_type] has_type.Neg[OF Dd_type]
        neg_eq
      by (rule CEV_axiom_from_eq_sym)
    show ?thesis
      using has_type.Neg[OF Dd_type] R_type not_dd neg_eq_sym
      by (rule CEV_axiom_from_eq_prop_elim)
  qed
  have right:
    "\<Gamma> ; T ; insert ?XN ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
  proof -
    let ?U = "insert ?XN ?S"
    have x_dn:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?XN"
      using XN_type by (intro CEV_axiom_from.Assumption) simp
    have xd_comp:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop
          (App X ?d)
          (App (pp_compose ?D ?N) ?d)"
      using X_type DN_type d_type x_dn
      by (rule CEV_axiom_from_pp_apply_cong_left)
    have comp_app:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop
          (App (pp_compose ?D ?N) ?d)
          (App ?D (App ?N ?d))"
      using CEV_pp_compose_apply_eq[OF D_type N_type d_type]
      by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
    have n_beta:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App ?N ?d) (Neg ?d)"
      using CEV_pp_negation_apply_eq[OF d_type]
      by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
    have DNd_Dnd:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App ?D (App ?N ?d)) (App ?D (Neg ?d))"
      using D_type
        has_type.App[OF N_type[unfolded pp_unary_ty_def] d_type]
        nd_type n_beta
      unfolding pp_unary_ty_def
      by (rule CEV_axiom_from_eq_app_right)
    have mid:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App X ?d) (App ?D (App ?N ?d))"
      using Xd_type
        has_type.App[
          OF DN_type[unfolded pp_unary_ty_def] d_type]
        has_type.App[
          OF D_type[unfolded pp_unary_ty_def]
            has_type.App[
              OF N_type[unfolded pp_unary_ty_def] d_type]]
        xd_comp comp_app
      by (rule CEV_axiom_from_eq_trans)
    have xd_dnd:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App X ?d) (App ?D (Neg ?d))"
      using Xd_type
        has_type.App[
          OF D_type[unfolded pp_unary_ty_def]
            has_type.App[
              OF N_type[unfolded pp_unary_ty_def] d_type]]
        Dnd_type mid DNd_Dnd
      by (rule CEV_axiom_from_eq_trans)
    have not_dnd:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App ?D (Neg ?d))"
    proof -
      have rule:
        "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Imp ?F (Neg (App ?D (Neg ?d)))"
        using CEV_T5_not_D_neg_d[OF core_T5 r_type]
        by (rule CEV_axiom_from.Theorem)
      have fun_r:
        "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
        using d_F by (rule CEV_axiom_from_mono) simp
      show ?thesis
        using fun_r rule by (rule CEV_axiom_from.MP)
    qed
    have neg_eq:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (Neg (App X ?d)) (Neg (App ?D (Neg ?d)))"
      using Xd_type Dnd_type xd_dnd
      by (rule CEV_axiom_from_T5_neg_cong)
    have neg_eq_sym:
      "\<Gamma> ; T ; ?U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (Neg (App ?D (Neg ?d))) (Neg (App X ?d))"
      using has_type.Neg[OF Xd_type] has_type.Neg[OF Dnd_type]
        neg_eq
      by (rule CEV_axiom_from_eq_sym)
    show ?thesis
      using has_type.Neg[OF Dnd_type] R_type not_dnd neg_eq_sym
      by (rule CEV_axiom_from_eq_prop_elim)
  qed
  have d_R:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?R"
    using XI_type XN_type R_type cases left right
    by (rule CEV_axiom_from_T5_disj_cases)
  have P_imp_R:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?P ?R"
    using P_type d_R by (rule CEV_axiom_from_deduction)
  show ?thesis
    using F_type P_imp_R by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_T6_Inv_liar_true:
  assumes axioms: "pp_T6_Inv_axioms \<subseteq> T"
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
      by (rule CEV_T6_Inv_liar_matrix)
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

theorem CEV_T6_Inv_fun_prime_implies_false:
  assumes axioms: "pp_T6_Inv_axioms \<subseteq> T"
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
    unfolding pp_T6_Inv_axioms_def pp_T5_axioms_def by blast
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
    using CEV_T6_Inv_liar_true[OF axioms r_type]
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

theorem CEV_Goodman_T6_Inv:
  "[] ; pp_T6_Inv_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof -
  let ?F = "pp_fun_prime (Var 0)"
  have r_type: "[Prop] \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have F_type: "[Prop] \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have witness_rule:
    "[Prop] ; pp_T6_Inv_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (shift ObjFalse)"
    using CEV_T6_Inv_fun_prime_implies_false[
      OF subset_refl r_type]
    by simp
  have exists_rule_raw:
    "[] ; pp_T6_Inv_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Exists Prop ?F) ObjFalse"
  proof (rule CEV_axiom_proves.Inst)
    show "[Prop] \<turnstile> ?F : Prop" by (rule F_type)
    show "[] \<turnstile> ObjFalse : Prop" by (rule typed_ObjFalse)
    show "[Prop] ; pp_T6_Inv_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (shift ObjFalse)"
      by (rule witness_rule)
  qed
  have exists_rule:
    "[] ; pp_T6_Inv_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp pp_exists_fun_prime ObjFalse"
    using exists_rule_raw
    unfolding pp_exists_fun_prime_def .
  have exists_fun:
    "[] ; pp_T6_Inv_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_exists_fun_prime"
  proof (rule CEV_axiom_proves.Axiom)
    show "pp_exists_fun_prime \<in> pp_T6_Inv_axioms"
      unfolding pp_T6_Inv_axioms_def by blast
    show "[] \<turnstile> pp_exists_fun_prime : Prop"
      by (rule typed_pp_exists_fun_prime)
  qed
  show ?thesis
    using exists_fun exists_rule by (rule CEV_axiom_proves.MP)
qed

corollary CEV_Goodman_T6_Inv_mono:
  assumes "pp_T6_Inv_axioms \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  using CEV_Goodman_T6_Inv assms
  by (rule CEV_axiom_proves_mono)

corollary pp_T6_Inv_inconsistency_target_verified:
  "pp_T6_Inv_inconsistency_target"
  unfolding pp_T6_Inv_inconsistency_target_def
  using CEV_Goodman_T6_Inv .

end
