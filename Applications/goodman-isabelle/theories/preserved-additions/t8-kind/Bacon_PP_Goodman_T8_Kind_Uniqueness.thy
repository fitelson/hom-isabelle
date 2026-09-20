theory Bacon_PP_Goodman_T8_Kind_Uniqueness
  imports 
    "Goodman_Legacy_T8_Encoding.Bacon_PP_Goodman_T8_Encoding"
begin

section \<open>Goodman T8b: uniqueness of kind under weak L2\<close>

definition pp_T8_representation ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_T8_representation p X q =
    Conj
      (pp_pure pp_unary_ty X)
      (Conj
        (pp_fun_prime q)
        (Eq Prop p (App X q)))"

lemma typed_pp_T8_representation:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> \<turnstile> pp_T8_representation p X q : Prop"
  unfolding pp_T8_representation_def
  using typed_pp_pure[OF X_type] typed_pp_fun_prime[OF q_type]
    p_type has_type.App[OF X_type[unfolded pp_unary_ty_def] q_type]
  by (intro has_type.Conj has_type.Eq)

theorem CEV_Goodman_T8_kind_uniqueness:
  assumes L2_in: "pp_L2 \<in> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and s_type: "\<Gamma> \<turnstile> s : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_T8_representation p X q)
        (pp_T8_representation p Y s))
      (pp_same_kind X Y)"
proof -
  let ?RX = "pp_T8_representation p X q"
  let ?RY = "pp_T8_representation p Y s"
  let ?H = "Conj ?RX ?RY"
  let ?K = "pp_same_kind X Y"
  have RX_type: "\<Gamma> \<turnstile> ?RX : Prop"
    using p_type X_type q_type
    by (rule typed_pp_T8_representation)
  have RY_type: "\<Gamma> \<turnstile> ?RY : Prop"
    using p_type Y_type s_type
    by (rule typed_pp_T8_representation)
  have H_type: "\<Gamma> \<turnstile> ?H : Prop"
    using RX_type RY_type by (rule has_type.Conj)
  let ?S = "{?H}"
  have d_H:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using H_type by (intro CEV_axiom_from.Assumption) simp
  have d_RX:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?RX"
    using d_H by (rule CEV_axiom_from_conj_left)
  have d_RY:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?RY"
    using d_H by (rule CEV_axiom_from_conj_right)
  have pure_X:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty X"
    using d_RX unfolding pp_T8_representation_def
    by (rule CEV_axiom_from_conj_left)
  have tail_X:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_fun_prime q) (Eq Prop p (App X q))"
    using d_RX unfolding pp_T8_representation_def
    by (rule CEV_axiom_from_conj_right)
  have fun_q:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime q"
    using tail_X by (rule CEV_axiom_from_conj_left)
  have eq_X:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p (App X q)"
    using tail_X by (rule CEV_axiom_from_conj_right)
  have pure_Y:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty Y"
    using d_RY unfolding pp_T8_representation_def
    by (rule CEV_axiom_from_conj_left)
  have tail_Y:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_fun_prime s) (Eq Prop p (App Y s))"
    using d_RY unfolding pp_T8_representation_def
    by (rule CEV_axiom_from_conj_right)
  have fun_s:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime s"
    using tail_Y by (rule CEV_axiom_from_conj_left)
  have eq_Y:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p (App Y s)"
    using tail_Y by (rule CEV_axiom_from_conj_right)
  have Xq_type: "\<Gamma> \<turnstile> App X q : Prop"
    using X_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Ys_type: "\<Gamma> \<turnstile> App Y s : Prop"
    using Y_type s_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Xq_p:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App X q) p"
    using p_type Xq_type eq_X by (rule CEV_axiom_from_eq_sym)
  have collision:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App X q) (App Y s)"
    using Xq_type p_type Ys_type Xq_p eq_Y
    by (rule CEV_axiom_from_eq_trans)
  have tail:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_fun_prime q)
        (Conj (pp_fun_prime s)
          (Eq Prop (App X q) (App Y s)))"
    using fun_q CEV_axiom_from_conj_intro[OF fun_s collision]
    by (rule CEV_axiom_from_conj_intro)
  have middle:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_pure pp_unary_ty Y)
        (Conj (pp_fun_prime q)
          (Conj (pp_fun_prime s)
            (Eq Prop (App X q) (App Y s))))"
    using pure_Y tail by (rule CEV_axiom_from_conj_intro)
  have prem:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_pure pp_unary_ty X)
        (Conj (pp_pure pp_unary_ty Y)
          (Conj (pp_fun_prime q)
            (Conj (pp_fun_prime s)
              (Eq Prop (App X q) (App Y s)))))"
    using pure_X middle by (rule CEV_axiom_from_conj_intro)
  have rule:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj (pp_pure pp_unary_ty X)
          (Conj (pp_pure pp_unary_ty Y)
            (Conj (pp_fun_prime q)
              (Conj (pp_fun_prime s)
                (Eq Prop (App X q) (App Y s))))))
        ?K"
    using CEV_axiom_L2_instance[
      OF L2_in X_type Y_type q_type s_type]
    by (rule CEV_axiom_from.Theorem)
  have d_K:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?K"
    using prem rule by (rule CEV_axiom_from.MP)
  show ?thesis
    using H_type d_K by (rule CEV_axiom_from_singleton_imp)
qed

end
