theory Bacon_PP_Goodman_Fun_Prime_Six_Distinct
  imports 
    "Goodman_Legacy_02.Bacon_PP_Goodman_Fun_Prime_Noncontingency"
begin

section \<open>Infrastructure for Goodman T2f\<close>

text \<open>
  At a \<open>fun\<acute>\<close> proposition, distinct pure unary operators have distinct
  outputs.  This is the contraposed, object-language form of the injectivity
  built into \<open>fun\<acute>\<close>.
\<close>

lemma CEV_fun_prime_separates_pure_operators:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and A_type: "\<Gamma> \<turnstile> A : pp_unary_ty"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and pure_A:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty A"
    and pure_B:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty B"
    and neq_AB:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (Eq pp_unary_ty A B)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime p)
      (Neg (Eq Prop (App A p) (App B p)))"
proof -
  let ?F = "pp_fun_prime p"
  let ?E = "Eq Prop (App A p) (App B p)"
  let ?AB = "Eq pp_unary_ty A B"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using p_type by (rule typed_pp_fun_prime)
  have Ap_type: "\<Gamma> \<turnstile> App A p : Prop"
    using A_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Bp_type: "\<Gamma> \<turnstile> App B p : Prop"
    using B_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using Ap_type Bp_type by (rule has_type.Eq)
  have d_F:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_E:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using E_type by (intro CEV_axiom_from.Assumption) simp
  have d_pure_A:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty A"
    using pure_A by (rule CEV_axiom_from.Theorem)
  have d_pure_B:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty B"
    using pure_B by (rule CEV_axiom_from.Theorem)
  have d_AB:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?AB"
    using p_type A_type B_type d_F d_pure_A d_pure_B d_E
    by (rule CEV_axiom_from_fun_prime)
  have d_not_AB:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?AB"
    using neq_AB by (rule CEV_axiom_from.Theorem)
  have d_false:
    "\<Gamma> ; T ; insert ?E {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_AB d_not_AB by (rule CEV_axiom_from_contradiction)
  have E_imp_false:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?E ObjFalse"
    using E_type d_false by (rule CEV_axiom_from_deduction)
  have imp_to_neg:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?E ObjFalse) (Neg ?E)"
    using CEV_proves_imp_false_to_neg[OF E_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_not_E:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?E"
    using E_imp_false imp_to_neg by (rule CEV_axiom_from.MP)
  show ?thesis
    using F_type d_not_E by (rule CEV_axiom_from_singleton_imp)
qed

end
