theory Bacon_PP_Goodman_T6_RS
  imports 
    "Goodman_Legacy_05.Bacon_PP_Goodman_T6_RS_Encoding"
begin

section \<open>Goodman T6 from strong L2 and rigid specification\<close>

subsection \<open>Instantiation rules\<close>

lemma CEV_axiom_strong_L2_instance:
  assumes L2_in: "pp_strong_L2 \<in> T"
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
      (pp_strong_same_kind X Y p q)"
proof -
  have L2_type: "\<Gamma> \<turnstile> pp_strong_L2 : Prop"
    by (rule typed_pp_strong_L2)
  have d0: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_strong_L2"
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
              (pp_strong_same_kind
                (shift (shift (shift X))) (Var 2) (Var 1) (Var 0)))))"
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
                  (pp_strong_same_kind
                    (Var 3) (Var 2) (Var 1) (Var 0))))))"
      using L2_type X_type d0
      unfolding pp_strong_L2_def
      by (rule CEV_axiom_UI_typed)
    show ?thesis
      using raw by (simp add: subst0_def)
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
            (pp_strong_same_kind
              (shift (shift X)) (shift (shift Y)) (Var 1) (Var 0))))"
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
                (pp_strong_same_kind
                  (shift (shift (shift X))) (Var 2) (Var 1) (Var 0)))))"
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
          (pp_strong_same_kind
            (shift X) (shift Y) (shift p) (Var 0)))"
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
              (pp_strong_same_kind
                (shift (shift X)) (shift (shift Y)) (Var 1) (Var 0))))"
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
          (pp_strong_same_kind
            (shift X) (shift Y) (shift p) (Var 0)))"
    using CEV_axiom_proves_formula[OF d3] q_type d3
    by (rule CEV_axiom_UI_typed)
  show ?thesis
    using raw
    by (simp add: subst0_def subst_lift_shift
        subst0_shift[of q X, unfolded subst0_def]
        subst0_shift[of q Y, unfolded subst0_def]
        subst0_shift[of q p, unfolded subst0_def])
qed

lemma CEV_axiom_spec_only_fun_prime_instance:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj (pp_spec_only_fun_prime R) (App R p))
      (pp_fun_prime p)"
proof -
  let ?H = "Conj (pp_spec_only_fun_prime R) (App R p)"
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_spec_only_fun_prime[OF R_type]
      R_type p_type
    unfolding pp_unary_ty_def
    by (intro has_type.Conj has_type.App)
  have d_H:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using H_type
    by (intro CEV_axiom_from.Assumption) simp
  have d_only:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_spec_only_fun_prime R"
    using d_H by (rule CEV_axiom_from_conj_left)
  have d_Rp:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App R p"
    using d_H by (rule CEV_axiom_from_conj_right)
  have raw:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 p
        (Imp
          (App (shift R) (Var 0))
          (pp_fun_prime (Var 0)))"
    using typed_pp_spec_only_fun_prime[OF R_type]
      p_type d_only
    unfolding pp_spec_only_fun_prime_def
    by (rule CEV_axiom_from_UI_typed)
  have rule:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (App R p) (pp_fun_prime p)"
    using raw
    by (simp add: subst0_def subst_lift_shift)
  have d_fun:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_fun_prime p"
    using d_Rp rule by (rule CEV_axiom_from.MP)
  show ?thesis
    using H_type d_fun by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_axiom_spec_rigid_instance:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
    and Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_spec_rigid R)
        (Conj
          (pp_group_member Z)
          (Conj
            (App R p)
            (Conj
              (App R q)
              (Eq Prop q (App Z p))))))
      (Eq Prop p q)"
proof -
  let ?A =
    "Conj
      (pp_spec_rigid R)
      (Conj
        (pp_group_member Z)
        (Conj
          (App R p)
          (Conj
            (App R q)
            (Eq Prop q (App Z p)))))"
  have Rp_type: "\<Gamma> \<turnstile> App R p : Prop"
    using R_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Rq_type: "\<Gamma> \<turnstile> App R q : Prop"
    using R_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Zp_type: "\<Gamma> \<turnstile> App Z p : Prop"
    using Z_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using typed_pp_spec_rigid[OF R_type]
      typed_pp_group_member[OF Z_type]
      Rp_type Rq_type q_type Zp_type
    by (intro has_type.Conj has_type.Eq)
  have d_A:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    using A_type
    by (intro CEV_axiom_from.Assumption) simp
  have d_rigid:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_spec_rigid R"
    using d_A by (rule CEV_axiom_from_conj_left)
  have d_tail:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_group_member Z)
        (Conj
          (App R p)
          (Conj (App R q) (Eq Prop q (App Z p))))"
    using d_A by (rule CEV_axiom_from_conj_right)
  have d_group:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member Z"
    using d_tail by (rule CEV_axiom_from_conj_left)
  have d_tail2:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (App R p)
        (Conj (App R q) (Eq Prop q (App Z p)))"
    using d_tail by (rule CEV_axiom_from_conj_right)
  have d_Rp:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App R p"
    using d_tail2 by (rule CEV_axiom_from_conj_left)
  have d_tail3:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (App R q) (Eq Prop q (App Z p))"
    using d_tail2 by (rule CEV_axiom_from_conj_right)
  have d_Rq:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App R q"
    using d_tail3 by (rule CEV_axiom_from_conj_left)
  have d_qZp:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop q (App Z p)"
    using d_tail3 by (rule CEV_axiom_from_conj_right)
  have d1:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall Prop
        (Forall Prop
          (Imp
            (Conj
              (pp_group_member (shift (shift Z)))
              (Conj
                (App (shift (shift R)) (Var 1))
                (Conj
                  (App (shift (shift R)) (Var 0))
                  (Eq Prop
                    (Var 0)
                    (App (shift (shift Z)) (Var 1))))))
            (Eq Prop (Var 1) (Var 0))))"
  proof -
    have raw:
      "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        subst0 Z
          (Forall Prop
            (Forall Prop
              (Imp
                (Conj
                  (pp_group_member (Var 2))
                  (Conj
                    (App (shift (shift (shift R))) (Var 1))
                    (Conj
                      (App (shift (shift (shift R))) (Var 0))
                      (Eq Prop
                        (Var 0)
                        (App (Var 2) (Var 1))))))
                (Eq Prop (Var 1) (Var 0)))))"
      using typed_pp_spec_rigid[OF R_type] Z_type d_rigid
      unfolding pp_spec_rigid_def
      by (rule CEV_axiom_from_UI_typed)
    show ?thesis
      using raw
      by (simp add: subst0_def subst_lift_shift
          rename_Suc_eq_shift_T6
          eval_nat_numeral)
  qed
  have d2:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Forall Prop
        (Imp
          (Conj
            (pp_group_member (shift Z))
            (Conj
              (App (shift R) (shift p))
              (Conj
                (App (shift R) (Var 0))
                (Eq Prop
                  (Var 0)
                  (App (shift Z) (shift p))))))
          (Eq Prop (shift p) (Var 0)))"
  proof -
    have raw:
      "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        subst0 p
          (Forall Prop
            (Imp
              (Conj
                (pp_group_member (shift (shift Z)))
                (Conj
                  (App (shift (shift R)) (Var 1))
                  (Conj
                    (App (shift (shift R)) (Var 0))
                    (Eq Prop
                      (Var 0)
                      (App (shift (shift Z)) (Var 1))))))
              (Eq Prop (Var 1) (Var 0))))"
      using CEV_axiom_from_formula[OF d1] p_type d1
      by (rule CEV_axiom_from_UI_typed)
    show ?thesis
      using raw
      by (simp add: subst0_def subst_lift_shift
          rename_Suc_eq_shift_T6
          subst0_shift[of p Z, unfolded subst0_def]
          subst0_shift[of p R, unfolded subst0_def])
  qed
  have raw:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      subst0 q
        (Imp
          (Conj
            (pp_group_member (shift Z))
            (Conj
              (App (shift R) (shift p))
              (Conj
                (App (shift R) (Var 0))
                (Eq Prop
                  (Var 0)
                  (App (shift Z) (shift p))))))
          (Eq Prop (shift p) (Var 0)))"
    using CEV_axiom_from_formula[OF d2] q_type d2
    by (rule CEV_axiom_from_UI_typed)
  have rule:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj
          (pp_group_member Z)
          (Conj
            (App R p)
            (Conj (App R q) (Eq Prop q (App Z p)))))
        (Eq Prop p q)"
    using raw
    by (simp add: subst0_def subst_lift_shift
        subst0_shift[of q Z, unfolded subst0_def]
        subst0_shift[of q R, unfolded subst0_def]
        subst0_shift[of q p, unfolded subst0_def]
        eval_nat_numeral)
  have d_ant:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_group_member Z)
        (Conj
          (App R p)
          (Conj (App R q) (Eq Prop q (App Z p))))"
    using d_group d_Rp d_Rq d_qZp
    by (intro CEV_axiom_from_conj_intro)
  have result:
    "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p q"
    using d_ant rule by (rule CEV_axiom_from.MP)
  show ?thesis
    using A_type result by (rule CEV_axiom_from_singleton_imp)
qed

lemma prop_tautology_RS_repack:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and D_type: "\<Gamma> \<turnstile> D : Prop"
    and E_type: "\<Gamma> \<turnstile> E : Prop"
    and J_type: "\<Gamma> \<turnstile> J : Prop"
    and F_type: "\<Gamma> \<turnstile> F : Prop"
  shows "prop_tautology \<Gamma>
    (Imp
      (Imp
        (Conj A (Conj B (Conj C (Conj D E))))
        F)
      (Imp
        (Conj B (Conj J E))
        (Imp
          (Conj A (Conj C D))
          F)))"
proof -
  have formula_type:
    "\<Gamma> \<turnstile>
      Imp
        (Imp
          (Conj A (Conj B (Conj C (Conj D E))))
          F)
        (Imp
          (Conj B (Conj J E))
          (Imp
            (Conj A (Conj C D))
            F)) : Prop"
    using assms
    by (intro has_type.Imp has_type.Conj)
  have eval:
    "\<forall>v. prop_eval v
      (Imp
        (Imp
          (Conj A (Conj B (Conj C (Conj D E))))
          F)
        (Imp
          (Conj B (Conj J E))
          (Imp
            (Conj A (Conj C D))
            F)))"
  proof
    fix v
    show "prop_eval v
      (Imp
        (Imp
          (Conj A (Conj B (Conj C (Conj D E))))
          F)
        (Imp
          (Conj B (Conj J E))
          (Imp
            (Conj A (Conj C D))
            F)))"
      apply (simp only: prop_eval.simps)
      by blast
  qed
  show ?thesis
    unfolding prop_tautology_def
    using formula_type eval by blast
qed

lemma CEV_axiom_strong_same_kind_rigid_inputs:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_spec_rigid R)
        (Conj (App R p) (App R q)))
      (Imp
        (pp_strong_same_kind X Y p q)
        (Eq Prop p q))"
proof -
  let ?H =
    "Conj
      (pp_spec_rigid R)
      (Conj (App R p) (App R q))"
  let ?S = "pp_strong_same_kind X Y p q"
  let ?E = "Eq Prop p q"
  have Rp_type: "\<Gamma> \<turnstile> App R p : Prop"
    using R_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Rq_type: "\<Gamma> \<turnstile> App R q : Prop"
    using R_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_spec_rigid[OF R_type] Rp_type Rq_type
    by (intro has_type.Conj)
  have S_type: "\<Gamma> \<turnstile> ?S : Prop"
    using X_type Y_type p_type q_type
    by (rule typed_pp_strong_same_kind)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using p_type q_type by (rule has_type.Eq)
  let ?Z = "Var 0"
  let ?Rs = "shift R"
  let ?Xs = "shift X"
  let ?Ys = "shift Y"
  let ?ps = "shift p"
  let ?qs = "shift q"
  let ?G = "pp_group_member ?Z"
  let ?J =
    "Eq pp_unary_ty ?Xs (pp_compose ?Ys ?Z)"
  let ?K = "Eq Prop ?qs (App ?Z ?ps)"
  let ?B = "Conj ?G (Conj ?J ?K)"
  have Z_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Z : pp_unary_ty"
    by (rule typed_var0)
  have Rs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Rs : pp_unary_ty"
    using R_type by (rule typed_shift_ctx)
  have Xs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Xs : pp_unary_ty"
    using X_type by (rule typed_shift_ctx)
  have Ys_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Ys : pp_unary_ty"
    using Y_type by (rule typed_shift_ctx)
  have ps_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?ps : Prop"
    using p_type by (rule typed_shift_ctx)
  have qs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?qs : Prop"
    using q_type by (rule typed_shift_ctx)
  have G_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?G : Prop"
    using Z_type by (rule typed_pp_group_member)
  have compose_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      pp_compose ?Ys ?Z : pp_unary_ty"
    using Ys_type Z_type by (rule typed_pp_compose)
  have J_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?J : Prop"
    using Xs_type compose_type by (rule has_type.Eq)
  have Zp_type:
    "pp_unary_ty # \<Gamma> \<turnstile> App ?Z ?ps : Prop"
    using Z_type ps_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have K_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?K : Prop"
    using qs_type Zp_type by (rule has_type.Eq)
  have Rps_type:
    "pp_unary_ty # \<Gamma> \<turnstile> App ?Rs ?ps : Prop"
    using Rs_type ps_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Rqs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> App ?Rs ?qs : Prop"
    using Rs_type qs_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Eshift_type:
    "pp_unary_ty # \<Gamma> \<turnstile> Eq Prop ?ps ?qs : Prop"
    using ps_type qs_type by (rule has_type.Eq)
  have B_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?B : Prop"
    using G_type J_type K_type
    by (intro has_type.Conj)
  have Hs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift ?H : Prop"
    using H_type by (rule typed_shift_ctx)
  have Es_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift ?E : Prop"
    using E_type by (rule typed_shift_ctx)
  have rigid_rule:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Conj
          (pp_spec_rigid ?Rs)
          (Conj
            ?G
            (Conj
              (App ?Rs ?ps)
              (Conj (App ?Rs ?qs) ?K))))
        (Eq Prop ?ps ?qs)"
    using Rs_type Z_type ps_type qs_type
    by (rule CEV_axiom_spec_rigid_instance)
  have repack:
    "pp_unary_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp
          (Conj
            (pp_spec_rigid ?Rs)
            (Conj
              ?G
              (Conj
                (App ?Rs ?ps)
                (Conj (App ?Rs ?qs) ?K))))
          (Eq Prop ?ps ?qs))
        (Imp ?B (Imp (shift ?H) (shift ?E)))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology (pp_unary_ty # \<Gamma>)
      (Imp
        (Imp
          (Conj
            (pp_spec_rigid ?Rs)
            (Conj
              ?G
              (Conj
                (App ?Rs ?ps)
                (Conj (App ?Rs ?qs) ?K))))
          (Eq Prop ?ps ?qs))
        (Imp ?B (Imp (shift ?H) (shift ?E))))"
      apply (simp only: shift_Conj_term shift_App_term
          shift_Eq_term shift_pp_spec_rigid_RS)
      apply (rule prop_tautology_RS_repack)
      apply (rule typed_pp_spec_rigid[OF Rs_type])
      apply (rule G_type)
      apply (rule Rps_type)
      apply (rule Rqs_type)
      apply (rule K_type)
      apply (rule J_type)
      by (rule Eshift_type)
  qed
  have bound:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?B (shift (Imp ?H ?E))"
  proof -
    have d:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?B (Imp (shift ?H) (shift ?E))"
      using rigid_rule CEV_axiom_proves.Base[OF repack]
      by (rule CEV_axiom_proves.MP)
    show ?thesis
      using d by simp
  qed
  have eliminated:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?S (Imp ?H ?E)"
  proof -
    have raw:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Exists pp_unary_ty ?B) (Imp ?H ?E)"
    proof (rule CEV_axiom_proves.Inst)
      show "pp_unary_ty # \<Gamma> \<turnstile> ?B : Prop"
        by (rule B_type)
      show "\<Gamma> \<turnstile> Imp ?H ?E : Prop"
        using H_type E_type by (rule has_type.Imp)
      show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?B (shift (Imp ?H ?E))"
        by (rule bound)
    qed
    show ?thesis
      using raw unfolding pp_strong_same_kind_def .
  qed
  have swap:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp ?S (Imp ?H ?E))
        (Imp ?H (Imp ?S ?E))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp ?S (Imp ?H ?E))
        (Imp ?H (Imp ?S ?E)))"
      using S_type H_type E_type
      by (rule prop_tautology_swap_imp)
  qed
  show ?thesis
    using eliminated CEV_axiom_proves.Base[OF swap]
    by (rule CEV_axiom_proves.MP)
qed

subsection \<open>Collisions on rigid instances\<close>

lemma CEV_axiom_RS_collision:
  assumes L2_in: "pp_strong_L2 \<in> T"
    and R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
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
            (pp_spec_only_fun_prime R)
            (Conj
              (pp_spec_rigid R)
              (Conj
                (App R p)
                (Conj
                  (App R q)
                  (Eq Prop (App X p) (App Y q))))))))
      (Conj
        (Eq Prop p q)
        (Eq pp_unary_ty X Y))"
proof -
  let ?PX = "pp_pure pp_unary_ty X"
  let ?PY = "pp_pure pp_unary_ty Y"
  let ?O = "pp_spec_only_fun_prime R"
  let ?D = "pp_spec_rigid R"
  let ?Rp = "App R p"
  let ?Rq = "App R q"
  let ?V = "Eq Prop (App X p) (App Y q)"
  let ?H =
    "Conj ?PX
      (Conj ?PY
        (Conj ?O
          (Conj ?D
            (Conj ?Rp (Conj ?Rq ?V)))))"
  have Rp_type: "\<Gamma> \<turnstile> ?Rp : Prop"
    using R_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Rq_type: "\<Gamma> \<turnstile> ?Rq : Prop"
    using R_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xp_type: "\<Gamma> \<turnstile> App X p : Prop"
    using X_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Yp_type: "\<Gamma> \<turnstile> App Y p : Prop"
    using Y_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Yq_type: "\<Gamma> \<turnstile> App Y q : Prop"
    using Y_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_pure[OF X_type]
      typed_pp_pure[OF Y_type]
      typed_pp_spec_only_fun_prime[OF R_type]
      typed_pp_spec_rigid[OF R_type]
      Rp_type Rq_type Xp_type Yq_type
    by (intro has_type.Conj has_type.Eq)
  have d_H:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using H_type
    by (intro CEV_axiom_from.Assumption) simp
  have d_PX:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PX"
    using d_H by (rule CEV_axiom_from_conj_left)
  have d_t1:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj ?PY
        (Conj ?O
          (Conj ?D
            (Conj ?Rp (Conj ?Rq ?V))))"
    using d_H by (rule CEV_axiom_from_conj_right)
  have d_PY:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PY"
    using d_t1 by (rule CEV_axiom_from_conj_left)
  have d_t2:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj ?O
        (Conj ?D (Conj ?Rp (Conj ?Rq ?V)))"
    using d_t1 by (rule CEV_axiom_from_conj_right)
  have d_O:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?O"
    using d_t2 by (rule CEV_axiom_from_conj_left)
  have d_t3:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj ?D (Conj ?Rp (Conj ?Rq ?V))"
    using d_t2 by (rule CEV_axiom_from_conj_right)
  have d_D:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?D"
    using d_t3 by (rule CEV_axiom_from_conj_left)
  have d_t4:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj ?Rp (Conj ?Rq ?V)"
    using d_t3 by (rule CEV_axiom_from_conj_right)
  have d_Rp:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Rp"
    using d_t4 by (rule CEV_axiom_from_conj_left)
  have d_t5:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj ?Rq ?V"
    using d_t4 by (rule CEV_axiom_from_conj_right)
  have d_Rq:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?Rq"
    using d_t5 by (rule CEV_axiom_from_conj_left)
  have d_V:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?V"
    using d_t5 by (rule CEV_axiom_from_conj_right)
  have d_fun_p:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
  proof -
    have pair:
      "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj ?O ?Rp"
      using d_O d_Rp by (rule CEV_axiom_from_conj_intro)
    show ?thesis
      using pair CEV_axiom_from.Theorem[
        OF CEV_axiom_spec_only_fun_prime_instance[
          OF R_type p_type]]
      by (rule CEV_axiom_from.MP)
  qed
  have d_fun_q:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime q"
  proof -
    have pair:
      "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj ?O ?Rq"
      using d_O d_Rq by (rule CEV_axiom_from_conj_intro)
    show ?thesis
      using pair CEV_axiom_from.Theorem[
        OF CEV_axiom_spec_only_fun_prime_instance[
          OF R_type q_type]]
      by (rule CEV_axiom_from.MP)
  qed
  have l2_ant:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj ?PX
        (Conj ?PY
          (Conj
            (pp_fun_prime p)
            (Conj (pp_fun_prime q) ?V)))"
    using d_PX d_PY d_fun_p d_fun_q d_V
    by (intro CEV_axiom_from_conj_intro)
  have d_same:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_strong_same_kind X Y p q"
    using l2_ant CEV_axiom_from.Theorem[
      OF CEV_axiom_strong_L2_instance[
        OF L2_in X_type Y_type p_type q_type]]
    by (rule CEV_axiom_from.MP)
  have rigid_ant:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj ?D (Conj ?Rp ?Rq)"
    using d_D d_Rp d_Rq
    by (intro CEV_axiom_from_conj_intro)
  have rigid_step:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (pp_strong_same_kind X Y p q)
        (Eq Prop p q)"
    using rigid_ant CEV_axiom_from.Theorem[
      OF CEV_axiom_strong_same_kind_rigid_inputs[
        OF R_type X_type Y_type p_type q_type]]
    by (rule CEV_axiom_from.MP)
  have d_pq:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p q"
    using d_same rigid_step by (rule CEV_axiom_from.MP)
  have d_Yp_Yq:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App Y p) (App Y q)"
    using Y_type[unfolded pp_unary_ty_def] p_type q_type d_pq
    by (rule CEV_axiom_from_eq_app_right)
  have d_Yq_Yp:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App Y q) (App Y p)"
    using Yp_type Yq_type d_Yp_Yq
    by (rule CEV_axiom_from_eq_sym)
  have d_same_value:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App X p) (App Y p)"
    using Xp_type Yq_type Yp_type d_V d_Yq_Yp
    by (rule CEV_axiom_from_eq_trans)
  have d_XY:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty X Y"
    using p_type X_type Y_type d_fun_p d_PX d_PY d_same_value
    by (rule CEV_axiom_from_fun_prime)
  have result:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (Eq Prop p q) (Eq pp_unary_ty X Y)"
    using d_pq d_XY by (rule CEV_axiom_from_conj_intro)
  show ?thesis
    using H_type result by (rule CEV_axiom_from_singleton_imp)
qed

subsection \<open>Purity of the RS diagonal\<close>

lemma pp_RS_diagonal_builder_axiom:
  "pp_pure
      ((pp_unary_ty \<rightarrow>\<^sub>o Prop)
        \<rightarrow>\<^sub>o (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty))
      pp_RS_diagonal_builder
    \<in> pp_T6_core_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
proof (intro UnI1 CollectI exI conjI)
  show "[] \<turnstile> pp_RS_diagonal_builder :
      (pp_unary_ty \<rightarrow>\<^sub>o Prop)
        \<rightarrow>\<^sub>o (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty)"
    by (rule typed_pp_RS_diagonal_builder)
  show "consts_of pp_RS_diagonal_builder = {}"
    by (rule pp_RS_diagonal_builder_constant_free)
qed simp

lemma pp_RS_diagonal_pure_from:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
    and pure_R:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_pure pp_unary_ty R"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_unary_ty (pp_RS_diagonal R)"
proof -
  let ?P = "pp_unary_ty \<rightarrow>\<^sub>o Prop"
  let ?F = "pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
  have closure1:
    "pp_application_closure ?P ?F \<in> T"
    using core pp_T6_application_closure_axiom by blast
  have closure2:
    "pp_application_closure pp_unary_ty pp_unary_ty \<in> T"
    using core pp_T6_application_closure_axiom by blast
  have builder_in:
    "pp_pure (?P \<rightarrow>\<^sub>o ?F) pp_RS_diagonal_builder \<in> T"
    using core pp_RS_diagonal_builder_axiom by blast
  have builder_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure (?P \<rightarrow>\<^sub>o ?F) pp_RS_diagonal_builder"
    using builder_in typed_pp_pure[OF typed_pp_RS_diagonal_builder]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  have target_in: "pp_target_PP \<in> T"
    using core pp_T6_target_axiom by blast
  have target_type: "\<Gamma> \<turnstile> pp_target_PP : Prop"
    by (rule infer_type_sound)
      (simp add: pp_target_PP_def pp_purity_of_pure_def pp_pure_def
        pp_Pure_def pp_unary_ty_def lookup_def)
  have target:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_target_PP"
    using target_in target_type
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  have Pure_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure ?P (pp_Pure pp_unary_ty)"
    using target
    by (simp add: pp_target_PP_def pp_purity_of_pure_def
        pp_unary_ty_def)
  have first_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure ?F
        (App pp_RS_diagonal_builder (pp_Pure pp_unary_ty))"
    using closure1 typed_pp_RS_diagonal_builder
      typed_pp_Pure[of \<Gamma> pp_unary_ty]
      builder_pure Pure_pure
    by (rule pp_axiom_application_closed_from)
  have first_type:
    "\<Gamma> \<turnstile>
      App pp_RS_diagonal_builder (pp_Pure pp_unary_ty) : ?F"
    using typed_pp_RS_diagonal_builder
      typed_pp_Pure[of \<Gamma> pp_unary_ty]
    by (rule has_type.App)
  have instance_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty (pp_RS_diagonal_instance R)"
    using closure2 first_type R_type first_pure pure_R
    by (rule pp_axiom_application_closed_from)
  have diagonal_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty
        (pp_RS_diagonal_instance R)
        (pp_RS_diagonal R)"
    using CEV_pp_RS_diagonal_instance_eq[OF R_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using typed_pp_RS_diagonal_instance[OF R_type]
      typed_pp_RS_diagonal[OF R_type]
      instance_pure diagonal_eq
    by (rule CEV_axiom_from_pure_eq_transport)
qed

subsection \<open>The RS diagonal law\<close>

lemma CEV_axiom_from_EG_typed_RS:
  assumes existential_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    and term_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and inst:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s subst0 M A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Exists \<sigma> A"
proof -
  have body_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    using existential_type by (auto elim: has_type.cases)
  have eg:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (subst0 M A) (Exists \<sigma> A)"
    using body_type term_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.EG)
  have local_eg:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (subst0 M A) (Exists \<sigma> A)"
    using eg
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using inst local_eg by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_RS_diagonal_body_forward:
  assumes L2_in: "pp_strong_L2 \<in> T"
    and R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and y_type: "\<Gamma> \<turnstile> y : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure pp_unary_ty Y)
        (Conj
          (pp_spec_only_fun_prime R)
          (Conj
            (pp_spec_rigid R)
            (App R y))))
      (Imp
        (pp_RS_diagonal_body R (App Y y))
        (Neg (App Y (App Y y))))"
proof -
  let ?x = "App Y y"
  let ?H =
    "Conj
      (pp_pure pp_unary_ty Y)
      (Conj
        (pp_spec_only_fun_prime R)
        (Conj
          (pp_spec_rigid R)
          (App R y)))"
  let ?E = "Neg (App Y ?x)"
  have x_type: "\<Gamma> \<turnstile> ?x : Prop"
    using Y_type y_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Ry_type: "\<Gamma> \<turnstile> App R y : Prop"
    using R_type y_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_pure[OF Y_type]
      typed_pp_spec_only_fun_prime[OF R_type]
      typed_pp_spec_rigid[OF R_type]
      Ry_type
    by (intro has_type.Conj)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
  proof (rule has_type.Neg)
    show "\<Gamma> \<turnstile> App Y ?x : Prop"
      using Y_type x_type unfolding pp_unary_ty_def
      by (rule has_type.App)
  qed

  let ?\<Delta> = "Prop # pp_unary_ty # \<Gamma>"
  let ?X = "Var 1"
  let ?z = "Var 0"
  let ?Rs = "shift (shift R)"
  let ?Ys = "shift (shift Y)"
  let ?ys = "shift (shift y)"
  let ?xs = "shift (shift ?x)"
  let ?K =
    "Conj
      (pp_pure pp_unary_ty ?X)
      (Conj
        (App ?Rs ?z)
        (Conj
          (Eq Prop ?xs (App ?X ?z))
          (Neg (App ?X ?xs))))"
  have X_type: "?\<Delta> \<turnstile> ?X : pp_unary_ty"
    by (rule has_type.Var) (simp add: lookup_def)
  have z_type: "?\<Delta> \<turnstile> ?z : Prop"
    by (rule typed_var0)
  have Rs_type: "?\<Delta> \<turnstile> ?Rs : pp_unary_ty"
    using R_type by (intro typed_shift_ctx)
  have Ys_type: "?\<Delta> \<turnstile> ?Ys : pp_unary_ty"
    using Y_type by (intro typed_shift_ctx)
  have ys_type: "?\<Delta> \<turnstile> ?ys : Prop"
    using y_type by (intro typed_shift_ctx)
  have xs_type: "?\<Delta> \<turnstile> ?xs : Prop"
    using x_type by (intro typed_shift_ctx)
  have Rz_type: "?\<Delta> \<turnstile> App ?Rs ?z : Prop"
    using Rs_type z_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xz_type: "?\<Delta> \<turnstile> App ?X ?z : Prop"
    using X_type z_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xx_type: "?\<Delta> \<turnstile> App ?X ?xs : Prop"
    using X_type xs_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Yx_type: "?\<Delta> \<turnstile> App ?Ys ?xs : Prop"
    using Ys_type xs_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have K_type: "?\<Delta> \<turnstile> ?K : Prop"
    using typed_pp_pure[OF X_type]
      Rz_type xs_type Xz_type Xx_type
    by (intro has_type.Conj has_type.Eq has_type.Neg)
  have H2_type: "?\<Delta> \<turnstile> shift (shift ?H) : Prop"
    using H_type by (intro typed_shift_ctx)
  have E2_type: "?\<Delta> \<turnstile> shift (shift ?E) : Prop"
    using E_type by (intro typed_shift_ctx)
  let ?S = "{?K, shift (shift ?H)}"
  have d_K:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?K"
    using K_type by (intro CEV_axiom_from.Assumption) simp
  have d_H_raw:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s shift (shift ?H)"
    using H2_type by (intro CEV_axiom_from.Assumption) simp
  have d_H:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty ?Ys)
        (Conj
          (pp_spec_only_fun_prime ?Rs)
          (Conj
            (pp_spec_rigid ?Rs)
            (App ?Rs ?ys)))"
    using d_H_raw by simp
  have d_pure_X:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?X"
    using d_K by (rule CEV_axiom_from_conj_left)
  have d_K1:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (App ?Rs ?z)
        (Conj
          (Eq Prop ?xs (App ?X ?z))
          (Neg (App ?X ?xs)))"
    using d_K by (rule CEV_axiom_from_conj_right)
  have d_Rz:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App ?Rs ?z"
    using d_K1 by (rule CEV_axiom_from_conj_left)
  have d_K2:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (Eq Prop ?xs (App ?X ?z))
        (Neg (App ?X ?xs))"
    using d_K1 by (rule CEV_axiom_from_conj_right)
  have d_value:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?xs (App ?X ?z)"
    using d_K2 by (rule CEV_axiom_from_conj_left)
  have d_neg_X:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (App ?X ?xs)"
    using d_K2 by (rule CEV_axiom_from_conj_right)
  have d_pure_Y:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?Ys"
    using d_H by (rule CEV_axiom_from_conj_left)
  have d_H1:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_spec_only_fun_prime ?Rs)
        (Conj
          (pp_spec_rigid ?Rs)
          (App ?Rs ?ys))"
    using d_H by (rule CEV_axiom_from_conj_right)
  have d_only:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_spec_only_fun_prime ?Rs"
    using d_H1 by (rule CEV_axiom_from_conj_left)
  have d_H2:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_spec_rigid ?Rs) (App ?Rs ?ys)"
    using d_H1 by (rule CEV_axiom_from_conj_right)
  have d_rigid:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_spec_rigid ?Rs"
    using d_H2 by (rule CEV_axiom_from_conj_left)
  have d_Ry:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App ?Rs ?ys"
    using d_H2 by (rule CEV_axiom_from_conj_right)
  have collision_ant:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty ?Ys)
        (Conj
          (pp_pure pp_unary_ty ?X)
          (Conj
            (pp_spec_only_fun_prime ?Rs)
            (Conj
              (pp_spec_rigid ?Rs)
              (Conj
                (App ?Rs ?ys)
                (Conj
                  (App ?Rs ?z)
                  (Eq Prop (App ?Ys ?ys) (App ?X ?z)))))))"
  proof -
    have shifted_x:
      "?xs = App ?Ys ?ys"
      by (simp add: shift_def rename_comp comp_def)
    show ?thesis
      using d_pure_Y d_pure_X d_only d_rigid d_Ry d_Rz
        d_value
      unfolding shifted_x
      by (intro CEV_axiom_from_conj_intro)
  qed
  have collision:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (Eq Prop ?ys ?z)
        (Eq pp_unary_ty ?Ys ?X)"
    using collision_ant CEV_axiom_from.Theorem[
      OF CEV_axiom_RS_collision[
        OF L2_in Rs_type Ys_type X_type ys_type z_type]]
    by (rule CEV_axiom_from.MP)
  have d_YX:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?Ys ?X"
    using collision by (rule CEV_axiom_from_conj_right)
  have d_apps:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?Ys ?xs) (App ?X ?xs)"
    using Ys_type X_type xs_type d_YX
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have d_negs:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop
        (Neg (App ?Ys ?xs))
        (Neg (App ?X ?xs))"
    using Yx_type Xx_type d_apps
    by (rule CEV_axiom_from_T5_neg_cong)
  have d_negs_sym:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop
        (Neg (App ?X ?xs))
        (Neg (App ?Ys ?xs))"
    using has_type.Neg[OF Yx_type] has_type.Neg[OF Xx_type] d_negs
    by (rule CEV_axiom_from_eq_sym)
  have d_E:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (App ?Ys ?xs)"
    using has_type.Neg[OF Xx_type] has_type.Neg[OF Yx_type]
      d_neg_X d_negs_sym
    by (rule CEV_axiom_from_eq_prop_elim)
  have d_E_shift:
    "?\<Delta> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      shift (shift ?E)"
    using d_E by (simp add: shift_def rename_comp comp_def)
  have under_K:
    "?\<Delta> ; T ; {?K} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (shift (shift ?H)) (shift (shift ?E))"
  proof (rule CEV_axiom_from_deduction[where S = "{?K}"])
    show "?\<Delta> \<turnstile> shift (shift ?H) : Prop"
      by (rule H2_type)
    show "?\<Delta> ; T ; insert (shift (shift ?H)) {?K}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s shift (shift ?E)"
      using d_E_shift
      by (rule CEV_axiom_from_mono) simp
  qed
  have deepest:
    "?\<Delta> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?K
        (Imp (shift (shift ?H)) (shift (shift ?E)))"
  proof -
    have local:
      "?\<Delta> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?K
          (Imp (shift (shift ?H)) (shift (shift ?E)))"
    proof (rule CEV_axiom_from_deduction[where S = "{}"])
      show "?\<Delta> \<turnstile> ?K : Prop"
        by (rule K_type)
      show "?\<Delta> ; T ; insert ?K {}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Imp (shift (shift ?H)) (shift (shift ?E))"
        using under_K by simp
    qed
    show ?thesis
      using local CEV_axiom_from_empty_iff by blast
  qed

  let ?K1 =
    "Exists Prop
      (Conj
        (pp_pure pp_unary_ty (Var 1))
        (Conj
          (App (shift (shift R)) (Var 0))
          (Conj
            (Eq Prop
              (shift (shift ?x))
              (App (Var 1) (Var 0)))
            (Neg (App (Var 1) (shift (shift ?x)))))))"
  have K1_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?K1 : Prop"
  proof -
    have body_type:
      "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?K : Prop"
      by (rule K_type)
    show ?thesis
      using body_type by (rule has_type.Exists)
  qed
  have inner_eliminated:
    "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?K1
        (Imp (shift ?H) (shift ?E))"
  proof (rule CEV_axiom_proves.Inst)
    show "Prop # pp_unary_ty # \<Gamma> \<turnstile> ?K : Prop"
      by (rule K_type)
    show "pp_unary_ty # \<Gamma> \<turnstile>
      Imp (shift ?H) (shift ?E) : Prop"
      using H_type E_type
      by (intro has_type.Imp typed_shift_ctx)
    show "Prop # pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?K (shift (Imp (shift ?H) (shift ?E)))"
      using deepest by simp
  qed
  have body_to_H_E:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_RS_diagonal_body R ?x) (Imp ?H ?E)"
  proof -
    have raw:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Exists pp_unary_ty ?K1) (Imp ?H ?E)"
    proof (rule CEV_axiom_proves.Inst)
      show "pp_unary_ty # \<Gamma> \<turnstile> ?K1 : Prop"
        by (rule K1_type)
      show "\<Gamma> \<turnstile> Imp ?H ?E : Prop"
        using H_type E_type by (rule has_type.Imp)
      show "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?K1 (shift (Imp ?H ?E))"
        using inner_eliminated by simp
    qed
    show ?thesis
      using raw unfolding pp_RS_diagonal_body_def .
  qed
  have swap:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp (pp_RS_diagonal_body R ?x) (Imp ?H ?E))
        (Imp ?H (Imp (pp_RS_diagonal_body R ?x) ?E))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp (pp_RS_diagonal_body R ?x) (Imp ?H ?E))
        (Imp ?H (Imp (pp_RS_diagonal_body R ?x) ?E)))"
      using typed_pp_RS_diagonal_body[OF R_type x_type]
        H_type E_type
      by (rule prop_tautology_swap_imp)
  qed
  show ?thesis
    using body_to_H_E CEV_axiom_proves.Base[OF swap]
    by (rule CEV_axiom_proves.MP)
qed

lemma CEV_axiom_RS_diagonal_body_backward:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and y_type: "\<Gamma> \<turnstile> y : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure pp_unary_ty Y)
        (Conj
          (App R y)
          (Neg (App Y (App Y y)))))
      (pp_RS_diagonal_body R (App Y y))"
proof -
  let ?x = "App Y y"
  let ?A =
    "Conj
      (pp_pure pp_unary_ty Y)
      (Conj
        (App R y)
        (Neg (App Y ?x)))"
  let ?K0 =
    "Conj
      (pp_pure pp_unary_ty Y)
      (Conj
        (App R y)
        (Conj
          (Eq Prop ?x (App Y y))
          (Neg (App Y ?x))))"
  have x_type: "\<Gamma> \<turnstile> ?x : Prop"
    using Y_type y_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Ry_type: "\<Gamma> \<turnstile> App R y : Prop"
    using R_type y_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Yx_type: "\<Gamma> \<turnstile> App Y ?x : Prop"
    using Y_type x_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using typed_pp_pure[OF Y_type] Ry_type
      has_type.Neg[OF Yx_type]
    by (intro has_type.Conj)
  let ?S = "{?A}"
  have d_A:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    using A_type by (intro CEV_axiom_from.Assumption) simp
  have d_pure:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty Y"
    using d_A by (rule CEV_axiom_from_conj_left)
  have d_tail:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (App R y) (Neg (App Y ?x))"
    using d_A by (rule CEV_axiom_from_conj_right)
  have d_Ry:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App R y"
    using d_tail by (rule CEV_axiom_from_conj_left)
  have d_neg:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App Y ?x)"
    using d_tail by (rule CEV_axiom_from_conj_right)
  have d_ref:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?x (App Y y)"
  proof -
    have ref: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop ?x ?x"
      using x_type
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.Ref)
    show ?thesis
      using ref by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  qed
  have d_K0:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?K0"
    using d_pure d_Ry d_ref d_neg
    by (intro CEV_axiom_from_conj_intro)

  let ?Zbody =
    "Conj
      (pp_pure pp_unary_ty (shift Y))
      (Conj
        (App (shift R) (Var 0))
        (Conj
          (Eq Prop (shift ?x) (App (shift Y) (Var 0)))
          (Neg (App (shift Y) (shift ?x)))))"
  have Zbody_type: "Prop # \<Gamma> \<turnstile> ?Zbody : Prop"
  proof -
    have Ys_type: "Prop # \<Gamma> \<turnstile> shift Y : pp_unary_ty"
      using Y_type by (rule typed_shift_ctx)
    have Rs_type: "Prop # \<Gamma> \<turnstile> shift R : pp_unary_ty"
      using R_type by (rule typed_shift_ctx)
    have xs_type: "Prop # \<Gamma> \<turnstile> shift ?x : Prop"
      using x_type by (rule typed_shift_ctx)
    have z_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    have Rz_type: "Prop # \<Gamma> \<turnstile> App (shift R) (Var 0) : Prop"
      using Rs_type z_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have Yz_type: "Prop # \<Gamma> \<turnstile> App (shift Y) (Var 0) : Prop"
      using Ys_type z_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have Yx_type': "Prop # \<Gamma> \<turnstile> App (shift Y) (shift ?x) : Prop"
      using Ys_type xs_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    show ?thesis
      using typed_pp_pure[OF Ys_type] Rz_type xs_type Yz_type Yx_type'
      by (intro has_type.Conj has_type.Eq has_type.Neg)
  qed
  have inner_type: "\<Gamma> \<turnstile> Exists Prop ?Zbody : Prop"
    using Zbody_type by (rule has_type.Exists)
  have d_inner_instance:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s subst0 y ?Zbody"
    using d_K0
    by (simp add: subst0_def pp_pure_def pp_Pure_def)
  have d_inner:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Exists Prop ?Zbody"
    using inner_type y_type d_inner_instance
    by (rule CEV_axiom_from_EG_typed_RS)

  let ?Outer =
    "Exists Prop
      (Conj
        (pp_pure pp_unary_ty (Var 1))
        (Conj
          (App (shift (shift R)) (Var 0))
          (Conj
            (Eq Prop
              (shift (shift ?x))
              (App (Var 1) (Var 0)))
            (Neg (App (Var 1) (shift (shift ?x)))))))"
  have outer_body_type:
    "pp_unary_ty # \<Gamma> \<turnstile> ?Outer : Prop"
  proof -
    have diagonal_body_type:
      "\<Gamma> \<turnstile> pp_RS_diagonal_body R ?x : Prop"
      using R_type x_type by (rule typed_pp_RS_diagonal_body)
    show ?thesis
      using diagonal_body_type
      unfolding pp_RS_diagonal_body_def
      by (auto elim: has_type.cases)
  qed
  have body_type:
    "\<Gamma> \<turnstile> Exists pp_unary_ty ?Outer : Prop"
    using outer_body_type by (rule has_type.Exists)
  have d_outer_instance:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s subst0 Y ?Outer"
  proof -
    have ren_Y: "rename Suc Y = shift Y"
      by (simp add: shift_def)
    show ?thesis
      using d_inner
      by (simp add: subst0_def pp_pure_def pp_Pure_def ren_Y)
  qed
  have d_body_raw:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Exists pp_unary_ty ?Outer"
    using body_type Y_type d_outer_instance
    by (rule CEV_axiom_from_EG_typed_RS)
  have d_body:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_RS_diagonal_body R ?x"
    using d_body_raw unfolding pp_RS_diagonal_body_def .
  show ?thesis
    using A_type d_body by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_axiom_RS_diagonal_forward:
  assumes L2_in: "pp_strong_L2 \<in> T"
    and R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and y_type: "\<Gamma> \<turnstile> y : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure pp_unary_ty Y)
        (Conj
          (pp_spec_only_fun_prime R)
          (Conj
            (pp_spec_rigid R)
            (App R y))))
      (Imp
        (App (pp_RS_diagonal R) (App Y y))
        (Neg (App Y (App Y y))))"
proof -
  let ?x = "App Y y"
  let ?H =
    "Conj
      (pp_pure pp_unary_ty Y)
      (Conj
        (pp_spec_only_fun_prime R)
        (Conj
          (pp_spec_rigid R)
          (App R y)))"
  let ?P = "App (pp_RS_diagonal R) ?x"
  let ?B = "pp_RS_diagonal_body R ?x"
  let ?E = "Neg (App Y ?x)"
  have x_type: "\<Gamma> \<turnstile> ?x : Prop"
    using Y_type y_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_RS_diagonal[OF R_type] x_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have B_type: "\<Gamma> \<turnstile> ?B : Prop"
    using R_type x_type by (rule typed_pp_RS_diagonal_body)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using CEV_axiom_proves_formula[
      OF CEV_axiom_RS_diagonal_body_forward[
        OF L2_in R_type Y_type y_type]]
    by (auto elim: has_type.cases)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using CEV_axiom_proves_formula[
      OF CEV_axiom_RS_diagonal_body_forward[
        OF L2_in R_type Y_type y_type]]
    by (auto elim: has_type.cases)
  have PB_eq: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop ?P ?B"
    using R_type x_type by (rule CEV_pp_RS_diagonal_apply_eq)
  have P_to_B_base: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?P ?B"
    using PB_eq CEV_eq_prop_implication[OF P_type B_type]
    by (rule CEV_proves.MP)
  have P_to_B:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?P ?B"
    using P_to_B_base by (rule CEV_axiom_proves.Base)
  have body_forward:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?H (Imp ?B ?E)"
    using CEV_axiom_RS_diagonal_body_forward[
      OF L2_in R_type Y_type y_type] .
  have taut:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp ?H (Imp ?B ?E))
        (Imp
          (Imp ?P ?B)
          (Imp ?H (Imp ?P ?E)))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp ?H (Imp ?B ?E))
        (Imp
          (Imp ?P ?B)
          (Imp ?H (Imp ?P ?E))))"
      unfolding prop_tautology_def
      using H_type P_type B_type E_type by auto
  qed
  have step:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp ?P ?B) (Imp ?H (Imp ?P ?E))"
    using body_forward CEV_axiom_proves.Base[OF taut]
    by (rule CEV_axiom_proves.MP)
  show ?thesis
    using P_to_B step by (rule CEV_axiom_proves.MP)
qed

lemma CEV_axiom_RS_diagonal_backward:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and y_type: "\<Gamma> \<turnstile> y : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure pp_unary_ty Y)
        (Conj
          (App R y)
          (Neg (App Y (App Y y)))))
      (App (pp_RS_diagonal R) (App Y y))"
proof -
  let ?x = "App Y y"
  let ?A =
    "Conj
      (pp_pure pp_unary_ty Y)
      (Conj
        (App R y)
        (Neg (App Y ?x)))"
  let ?P = "App (pp_RS_diagonal R) ?x"
  let ?B = "pp_RS_diagonal_body R ?x"
  have x_type: "\<Gamma> \<turnstile> ?x : Prop"
    using Y_type y_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using typed_pp_RS_diagonal[OF R_type] x_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have B_type: "\<Gamma> \<turnstile> ?B : Prop"
    using R_type x_type by (rule typed_pp_RS_diagonal_body)
  have A_type: "\<Gamma> \<turnstile> ?A : Prop"
    using CEV_axiom_proves_formula[
      OF CEV_axiom_RS_diagonal_body_backward[
        OF R_type Y_type y_type]]
    by (auto elim: has_type.cases)
  have PB: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop ?P ?B"
    using R_type x_type by (rule CEV_pp_RS_diagonal_apply_eq)
  have BP: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop ?B ?P"
    using PB CEV_eq_sym[OF P_type B_type]
    by (rule CEV_proves.MP)
  have B_to_P_base: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?B ?P"
    using BP CEV_eq_prop_implication[OF B_type P_type]
    by (rule CEV_proves.MP)
  have B_to_P:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?B ?P"
    using B_to_P_base by (rule CEV_axiom_proves.Base)
  have A_to_B:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?A ?B"
    using CEV_axiom_RS_diagonal_body_backward[
      OF R_type Y_type y_type] .
  show ?thesis
    using A_type B_type P_type A_to_B B_to_P
    by (rule CEV_axiom_imp_trans_plus)
qed

subsection \<open>Contradiction from one rigid instance\<close>

lemma CEV_axiom_RS_instance_contradiction:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and L2_in: "pp_strong_L2 \<in> T"
    and R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
    and y_type: "\<Gamma> \<turnstile> y : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_pure pp_unary_ty R)
        (Conj
          (pp_spec_only_fun_prime R)
          (pp_spec_rigid R)))
      (Imp (App R y) ObjFalse)"
proof -
  let ?B = "pp_RS_diagonal R"
  let ?By = "App ?B y"
  let ?P = "App ?B ?By"
  let ?H =
    "Conj
      (pp_pure pp_unary_ty R)
      (Conj
        (pp_spec_only_fun_prime R)
        (pp_spec_rigid R))"
  have B_type: "\<Gamma> \<turnstile> ?B : pp_unary_ty"
    using R_type by (rule typed_pp_RS_diagonal)
  have By_type: "\<Gamma> \<turnstile> ?By : Prop"
    using B_type y_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using B_type By_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Ry_type: "\<Gamma> \<turnstile> App R y : Prop"
    using R_type y_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_pure[OF R_type]
      typed_pp_spec_only_fun_prime[OF R_type]
      typed_pp_spec_rigid[OF R_type]
    by (intro has_type.Conj)
  let ?S = "{?H, App R y}"
  have d_H:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using H_type by (intro CEV_axiom_from.Assumption) simp
  have d_Ry:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App R y"
    using Ry_type by (intro CEV_axiom_from.Assumption) simp
  have d_pure_R:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty R"
    using d_H by (rule CEV_axiom_from_conj_left)
  have d_H1:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_spec_only_fun_prime R) (pp_spec_rigid R)"
    using d_H by (rule CEV_axiom_from_conj_right)
  have d_only:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_spec_only_fun_prime R"
    using d_H1 by (rule CEV_axiom_from_conj_left)
  have d_rigid:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_spec_rigid R"
    using d_H1 by (rule CEV_axiom_from_conj_right)
  have d_pure_B:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?B"
    using core R_type d_pure_R
    by (rule pp_RS_diagonal_pure_from)
  have forward_ant:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty ?B)
        (Conj
          (pp_spec_only_fun_prime R)
          (Conj
            (pp_spec_rigid R)
            (App R y)))"
    using d_pure_B d_only d_rigid d_Ry
    by (intro CEV_axiom_from_conj_intro)
  have P_to_not_P:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?P (Neg ?P)"
    using forward_ant CEV_axiom_from.Theorem[
      OF CEV_axiom_RS_diagonal_forward[
        OF L2_in R_type B_type y_type]]
    by (rule CEV_axiom_from.MP)
  have self_neg_taut:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp ?P (Neg ?P)) (Neg ?P)"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp (Imp ?P (Neg ?P)) (Neg ?P))"
      unfolding prop_tautology_def
      using P_type by auto
  qed
  have not_P:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?P"
    using P_to_not_P
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[OF self_neg_taut]]
    by (rule CEV_axiom_from.MP)
  have backward_ant:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_pure pp_unary_ty ?B)
        (Conj (App R y) (Neg ?P))"
    using d_pure_B d_Ry not_P
    by (intro CEV_axiom_from_conj_intro)
  have d_P:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using backward_ant CEV_axiom_from.Theorem[
      OF CEV_axiom_RS_diagonal_backward[
        OF R_type B_type y_type]]
    by (rule CEV_axiom_from.MP)
  have false:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_P not_P by (rule CEV_axiom_from_contradiction)
  have under_H:
    "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (App R y) ObjFalse"
  proof (rule CEV_axiom_from_deduction[where S = "{?H}"])
    show "\<Gamma> \<turnstile> App R y : Prop"
      by (rule Ry_type)
    show "\<Gamma> ; T ; insert (App R y) {?H}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
      using false by (rule CEV_axiom_from_mono) simp
  qed
  show ?thesis
    using H_type under_H by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_axiom_RS_specification_contradiction:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and L2_in: "pp_strong_L2 \<in> T"
    and R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_rigid_specification R) ObjFalse"
proof -
  let ?H =
    "Conj
      (pp_pure pp_unary_ty R)
      (Conj
        (pp_spec_only_fun_prime R)
        (pp_spec_rigid R))"
  let ?I = "pp_spec_instantiated R"
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_pure[OF R_type]
      typed_pp_spec_only_fun_prime[OF R_type]
      typed_pp_spec_rigid[OF R_type]
    by (intro has_type.Conj)
  have I_type: "\<Gamma> \<turnstile> ?I : Prop"
    using R_type by (rule typed_pp_spec_instantiated)
  have spec_type: "\<Gamma> \<turnstile> pp_rigid_specification R : Prop"
    using R_type by (rule typed_pp_rigid_specification)
  let ?Rs = "shift R"
  let ?y = "Var 0"
  have Rs_type: "Prop # \<Gamma> \<turnstile> ?Rs : pp_unary_ty"
    using R_type by (rule typed_shift_ctx)
  have y_type: "Prop # \<Gamma> \<turnstile> ?y : Prop"
    by (rule typed_var0)
  have Hs_type: "Prop # \<Gamma> \<turnstile> shift ?H : Prop"
    using H_type by (rule typed_shift_ctx)
  have Rsy_type: "Prop # \<Gamma> \<turnstile> App ?Rs ?y : Prop"
    using Rs_type y_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have instance_rule:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (shift ?H)
        (Imp (App ?Rs ?y) ObjFalse)"
    using CEV_axiom_RS_instance_contradiction[
      OF core L2_in Rs_type y_type]
    by (simp add: shift_def)
  have swap:
    "Prop # \<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp (shift ?H) (Imp (App ?Rs ?y) ObjFalse))
        (Imp (App ?Rs ?y) (Imp (shift ?H) ObjFalse))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology (Prop # \<Gamma>)
      (Imp
        (Imp (shift ?H) (Imp (App ?Rs ?y) ObjFalse))
        (Imp (App ?Rs ?y) (Imp (shift ?H) ObjFalse)))"
      using Hs_type Rsy_type typed_ObjFalse
      by (rule prop_tautology_swap_imp)
  qed
  have bound:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (App ?Rs ?y) (shift (Imp ?H ObjFalse))"
  proof -
    have d:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (App ?Rs ?y) (Imp (shift ?H) ObjFalse)"
      using instance_rule CEV_axiom_proves.Base[OF swap]
      by (rule CEV_axiom_proves.MP)
    show ?thesis
      using d by simp
  qed
  have eliminated:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?I (Imp ?H ObjFalse)"
  proof -
    have raw:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Exists Prop (App (shift R) (Var 0)))
          (Imp ?H ObjFalse)"
    proof (rule CEV_axiom_proves.Inst)
      show "Prop # \<Gamma> \<turnstile> App (shift R) (Var 0) : Prop"
        using Rs_type y_type unfolding pp_unary_ty_def
        by (rule has_type.App)
      show "\<Gamma> \<turnstile> Imp ?H ObjFalse : Prop"
        using H_type typed_ObjFalse by (rule has_type.Imp)
      show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (App (shift R) (Var 0))
          (shift (Imp ?H ObjFalse))"
        by (rule bound)
    qed
    show ?thesis
      using raw unfolding pp_spec_instantiated_def .
  qed
  have finish:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp ?I (Imp ?H ObjFalse))
        (Imp (pp_rigid_specification R) ObjFalse)"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp
        (Imp ?I (Imp ?H ObjFalse))
        (Imp (pp_rigid_specification R) ObjFalse))"
    proof -
      have formula_type:
        "\<Gamma> \<turnstile>
          Imp
            (Imp ?I (Imp ?H ObjFalse))
            (Imp (pp_rigid_specification R) ObjFalse) : Prop"
        using I_type H_type spec_type typed_ObjFalse
        by (intro has_type.Imp)
      have eval:
        "\<forall>v. prop_eval v
          (Imp
            (Imp ?I (Imp ?H ObjFalse))
            (Imp (pp_rigid_specification R) ObjFalse))"
        unfolding pp_rigid_specification_def
        by auto
      show ?thesis
        unfolding prop_tautology_def
        using formula_type eval by blast
    qed
  qed
  show ?thesis
    using eliminated CEV_axiom_proves.Base[OF finish]
    by (rule CEV_axiom_proves.MP)
qed

subsection \<open>The exact T6-RS theorem\<close>

lemma pp_T6_RS_axioms_typed:
  assumes "A \<in> pp_T6_RS_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_purity_schema_typed
    pp_application_closure_schema_typed
    typed_pp_target_PP typed_pp_strong_L2 typed_pp_RS
  unfolding pp_T6_RS_axioms_def pp_T6_core_PP_axioms_def
  by blast

theorem CEV_Goodman_T6_RS:
  "[] ; pp_T6_RS_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof -
  have core:
    "pp_T6_core_PP_axioms \<subseteq> pp_T6_RS_axioms"
    unfolding pp_T6_RS_axioms_def by blast
  have L2_in:
    "pp_strong_L2 \<in> pp_T6_RS_axioms"
    unfolding pp_T6_RS_axioms_def by blast
  let ?R = "Var 0"
  have R_type:
    "[pp_unary_ty] \<turnstile> ?R : pp_unary_ty"
    by (rule typed_var0)
  have bound:
    "[pp_unary_ty] ; pp_T6_RS_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (pp_rigid_specification ?R)
        (shift ObjFalse)"
    using CEV_axiom_RS_specification_contradiction[
      OF core L2_in R_type]
    by simp
  have RS_to_false:
    "[] ; pp_T6_RS_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp pp_RS ObjFalse"
  proof -
    have raw:
      "[] ; pp_T6_RS_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (Exists pp_unary_ty
            (pp_rigid_specification (Var 0)))
          ObjFalse"
    proof (rule CEV_axiom_proves.Inst)
      show "[pp_unary_ty] \<turnstile>
        pp_rigid_specification (Var 0) : Prop"
        using R_type by (rule typed_pp_rigid_specification)
      show "[] \<turnstile> ObjFalse : Prop"
        by (rule typed_ObjFalse)
      show "[pp_unary_ty] ; pp_T6_RS_axioms
        \<turnstile>\<^sub>CEV\<^sup>+
          Imp
            (pp_rigid_specification (Var 0))
            (shift ObjFalse)"
        by (rule bound)
    qed
    show ?thesis
      using raw unfolding pp_RS_def .
  qed
  have RS_in: "pp_RS \<in> pp_T6_RS_axioms"
    unfolding pp_T6_RS_axioms_def by blast
  have d_RS:
    "[] ; pp_T6_RS_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_RS"
    using RS_in typed_pp_RS by (rule CEV_axiom_proves.Axiom)
  show ?thesis
    using d_RS RS_to_false by (rule CEV_axiom_proves.MP)
qed

end
