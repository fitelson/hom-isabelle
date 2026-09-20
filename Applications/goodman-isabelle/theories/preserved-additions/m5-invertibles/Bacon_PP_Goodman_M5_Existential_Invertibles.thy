theory Bacon_PP_Goodman_M5_Existential_Invertibles
  imports
    
    "Goodman_Legacy_M5_Collision.Bacon_PP_Goodman_M5_Collision"
    "Goodman_Legacy_05.Bacon_PP_Goodman_T6_TU"
begin

section \<open>What the M5 collision method says about existential invertibility\<close>

text \<open>
  An explicit two-sided inverse makes its operator injective.  We first prove
  this inside CEV+ and then eliminate the inverse witness existentially.  The
  result identifies the exact limit of the M5 collision calculation: it
  refutes reversibility of the displayed noncontingency operator, but no
  collision can be extracted from reversibility alone.
\<close>

lemma CEV_M5_inverse_witness_injective:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and W_type: "\<Gamma> \<turnstile> W : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_inverse_witness Z W)
      (Imp
        (Eq Prop (App Z p) (App Z q))
        (Eq Prop p q))"
proof -
  let ?WB = "pp_inverse_witness Z W"
  let ?E = "Eq Prop (App Z p) (App Z q)"
  let ?PQ = "Eq Prop p q"
  let ?Base = "insert ?E {?WB}"
  have Zp_type: "\<Gamma> \<turnstile> App Z p : Prop"
    using Z_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Zq_type: "\<Gamma> \<turnstile> App Z q : Prop"
    using Z_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have WZp_type: "\<Gamma> \<turnstile> App W (App Z p) : Prop"
    using W_type Zp_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have WZq_type: "\<Gamma> \<turnstile> App W (App Z q) : Prop"
    using W_type Zq_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have WB_type: "\<Gamma> \<turnstile> ?WB : Prop"
    using Z_type W_type by (rule typed_pp_inverse_witness)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using Zp_type Zq_type by (rule has_type.Eq)
  have d_WB:
      "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?WB"
    using WB_type by (intro CEV_axiom_from.Assumption) simp
  have d_E:
      "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using E_type by (intro CEV_axiom_from.Assumption) simp
  have inverse_pair:
      "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Conj
          (Eq pp_unary_ty
            (pp_compose Z W) pp_identity_operator)
          (Eq pp_unary_ty
            (pp_compose W Z) pp_identity_operator)"
    using d_WB unfolding pp_inverse_witness_def
    by (rule CEV_axiom_from_conj_right)
  have WZ:
      "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq pp_unary_ty
          (pp_compose W Z) pp_identity_operator"
    using inverse_pair by (rule CEV_axiom_from_conj_right)
  have cancel_p:
      "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App W (App Z p)) p"
    using W_type Z_type p_type WZ
    by (rule CEV_axiom_from_T6_inverse_cancel)
  have p_cancel:
      "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop p (App W (App Z p))"
    using WZp_type p_type cancel_p
    by (rule CEV_axiom_from_eq_sym)
  have congruence:
      "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop
          (App W (App Z p))
          (App W (App Z q))"
    using W_type Zp_type Zq_type d_E
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have first:
      "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop p (App W (App Z q))"
    using p_type WZp_type WZq_type p_cancel congruence
    by (rule CEV_axiom_from_eq_trans)
  have cancel_q:
      "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop (App W (App Z q)) q"
    using W_type Z_type q_type WZ
    by (rule CEV_axiom_from_T6_inverse_cancel)
  have result:
      "\<Gamma> ; T ; ?Base \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PQ"
    using p_type WZq_type q_type first cancel_q
    by (rule CEV_axiom_from_eq_trans)
  have under_inverse:
      "\<Gamma> ; T ; {?WB} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?E ?PQ"
    using E_type result by (rule CEV_axiom_from_deduction)
  show ?thesis
    using WB_type under_inverse by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_M5_reversible_injective:
  assumes Z_type: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_reversible Z)
      (Imp
        (Eq Prop (App Z p) (App Z q))
        (Eq Prop p q))"
proof -
  let ?E = "Eq Prop (App Z p) (App Z q)"
  let ?PQ = "Eq Prop p q"
  let ?Target = "Imp ?E ?PQ"
  let ?W = "Var 0"
  let ?Zs = "shift Z"
  let ?WB = "pp_inverse_witness ?Zs ?W"
  have Zs_type:
      "pp_unary_ty # \<Gamma> \<turnstile> ?Zs : pp_unary_ty"
    using Z_type by (rule typed_shift_ctx)
  have W_type:
      "pp_unary_ty # \<Gamma> \<turnstile> ?W : pp_unary_ty"
    by (rule typed_var0)
  have ps_type:
      "pp_unary_ty # \<Gamma> \<turnstile> shift p : Prop"
    using p_type by (rule typed_shift_ctx)
  have qs_type:
      "pp_unary_ty # \<Gamma> \<turnstile> shift q : Prop"
    using q_type by (rule typed_shift_ctx)
  have WB_type:
      "pp_unary_ty # \<Gamma> \<turnstile> ?WB : Prop"
    using Zs_type W_type by (rule typed_pp_inverse_witness)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using has_type.App[OF Z_type[unfolded pp_unary_ty_def] p_type]
      has_type.App[OF Z_type[unfolded pp_unary_ty_def] q_type]
    by (rule has_type.Eq)
  have PQ_type: "\<Gamma> \<turnstile> ?PQ : Prop"
    using p_type q_type by (rule has_type.Eq)
  have Target_type: "\<Gamma> \<turnstile> ?Target : Prop"
    using E_type PQ_type by (rule has_type.Imp)
  have bound:
      "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?WB (shift ?Target)"
  proof -
    have d:
        "pp_unary_ty # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
          Imp ?WB
            (Imp
              (Eq Prop
                (App ?Zs (shift p))
                (App ?Zs (shift q)))
              (Eq Prop (shift p) (shift q)))"
      using CEV_M5_inverse_witness_injective[
        OF Zs_type W_type ps_type qs_type] .
    show ?thesis
      using d by (simp add: shift_def)
  qed
  have eliminated:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Exists pp_unary_ty ?WB) ?Target"
    using WB_type Target_type bound
    by (rule CEV_axiom_proves.Inst)
  show ?thesis
    using eliminated
    by (simp add: pp_reversible_as_inverse_witness)
qed

theorem CEV_Goodman_M5_collision_operator_not_reversible:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and fun_axiom: "pp_fun_prime r \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Neg (pp_reversible pp_M5_collision_operator)"
proof -
  let ?N = "pp_noncontingent r"
  let ?Z = pp_M5_collision_operator
  let ?Rev = "pp_reversible ?Z"
  let ?E = "Eq Prop (App ?Z ?N) (App ?Z ObjTrue)"
  let ?D = "Eq Prop ?N ObjTrue"
  have N_type: "\<Gamma> \<turnstile> ?N : Prop"
    using r_type by (rule typed_pp_noncontingent)
  have Z_type: "\<Gamma> \<turnstile> ?Z : pp_unary_ty"
    by (rule typed_pp_M5_collision_operator)
  have ZN_type: "\<Gamma> \<turnstile> App ?Z ?N : Prop"
    using Z_type N_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have ZT_type: "\<Gamma> \<turnstile> App ?Z ObjTrue : Prop"
    using Z_type typed_ObjTrue unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Rev_type: "\<Gamma> \<turnstile> ?Rev : Prop"
    using Z_type by (rule typed_pp_reversible)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using ZN_type ZT_type by (rule has_type.Eq)
  have D_type: "\<Gamma> \<turnstile> ?D : Prop"
    using N_type typed_ObjTrue by (rule has_type.Eq)
  have collision_result:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Conj (Neg ?D) ?E"
    using CEV_Goodman_M5_collision[
      OF core r_type fun_axiom, unfolded Let_def] .
  have distinct:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg ?D"
  proof -
    have local:
        "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?D"
      using CEV_axiom_from.Theorem[OF collision_result]
      by (rule CEV_axiom_from_conj_left)
    show ?thesis
      using local CEV_axiom_from_empty_iff by blast
  qed
  have collision:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ?E"
  proof -
    have local:
        "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
      using CEV_axiom_from.Theorem[OF collision_result]
      by (rule CEV_axiom_from_conj_right)
    show ?thesis
      using local CEV_axiom_from_empty_iff by blast
  qed
  have injectivity:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?Rev (Imp ?E ?D)"
    using CEV_M5_reversible_injective[
      OF Z_type N_type typed_ObjTrue] .
  have collect_collision:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?E
          (Imp (Imp ?Rev (Imp ?E ?D))
            (Imp ?Rev ?D))"
    by (rule CEVp_M5_propositional)
      (use E_type Rev_type D_type in auto)
  have step:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Imp ?Rev (Imp ?E ?D))
          (Imp ?Rev ?D)"
    using collision collect_collision
    by (rule CEV_axiom_proves.MP)
  have rev_to_equal:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?Rev ?D"
    using injectivity step by (rule CEV_axiom_proves.MP)
  have contradiction:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Neg ?D)
          (Imp (Imp ?Rev ?D) (Neg ?Rev))"
    by (rule CEVp_M5_propositional)
      (use D_type Rev_type in auto)
  have final_step:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Imp ?Rev ?D) (Neg ?Rev)"
    using distinct contradiction by (rule CEV_axiom_proves.MP)
  show ?thesis
    using rev_to_equal final_step by (rule CEV_axiom_proves.MP)
qed

text \<open>
  The first theorem already accepts an inverse supplied only under an
  existential quantifier; no named inverse is needed.  It follows that an
  existential claim of reversibility supplies injectivity, not a collision.
  The displayed M5 calculation works because the operator is given by a term
  whose action can be evaluated at two explicit propositions.  To extend the
  method to a further existentially described class, one must add a condition
  that determines enough of the witness's action to construct unequal inputs.
  Existential reversibility by itself supplies no such condition.
\<close>

end
