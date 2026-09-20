theory Bacon_PP_Goodman_Fun_Prime_Attainment
  imports 
    "Goodman_Legacy_02.Bacon_PP_Goodman_Fun_Prime_Nontriviality"
begin

section \<open>Goodman T2c: every pure proposition is attainable\<close>

text \<open>
  For a proposition \<open>p\<close>, let \<open>N\<^sub>p\<close> be the unary operator
  \<open>\<lambda>q. \<not>(q = p)\<close>.  If \<open>r\<close> satisfies \<open>fun\<acute>\<close> and it were necessary
  that \<open>r \<noteq> p\<close>, then \<open>N\<^sub>p\<close> and the constant-truth operator would
  agree at \<open>r\<close>.  When \<open>p\<close> is pure, both operators are pure, so
  \<open>fun\<acute>(r)\<close> identifies them.  Evaluating them at \<open>p\<close> then yields both
  \<open>p = p\<close> and its negation.

  The proof below uses only the section-4 core package.  In particular, no
  Recombination, QSS, Persistence, fundamentality, or classification axiom is
  used.
\<close>

definition pp_inequality_builder :: oterm where
  "pp_inequality_builder =
    Lam Prop (Lam Prop (Neg (Eq Prop (Var 0) (Var 1))))"

definition pp_inequality_lambda :: "oterm \<Rightarrow> oterm" where
  "pp_inequality_lambda p =
    Lam Prop (Neg (Eq Prop (Var 0) (shift p)))"

definition pp_inequality_operator :: "oterm \<Rightarrow> oterm" where
  "pp_inequality_operator p = App pp_inequality_builder p"

lemma typed_pp_inequality_builder:
  "\<Gamma> \<turnstile> pp_inequality_builder :
    Prop \<rightarrow>\<^sub>o pp_unary_ty"
  unfolding pp_inequality_builder_def pp_unary_ty_def
  by (intro has_type.Lam has_type.Neg has_type.Eq has_type.Var)
    (simp_all add: lookup_def)

lemma typed_pp_inequality_lambda:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile> pp_inequality_lambda p : pp_unary_ty"
  unfolding pp_inequality_lambda_def pp_unary_ty_def
proof (rule has_type.Lam)
  have q_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have p_shift: "Prop # \<Gamma> \<turnstile> shift p : Prop"
    using p_type by (rule typed_shift_ctx)
  show "Prop # \<Gamma> \<turnstile>
    Neg (Eq Prop (Var 0) (shift p)) : Prop"
    using q_type p_shift by (intro has_type.Neg has_type.Eq)
qed

lemma typed_pp_inequality_operator:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile> pp_inequality_operator p : pp_unary_ty"
  unfolding pp_inequality_operator_def
  using typed_pp_inequality_builder p_type by (rule has_type.App)

lemma pp_inequality_operator_first_beta:
  "compatible_step beta_contract
    (App (pp_inequality_operator p) q)
    (App (pp_inequality_lambda p) q)"
proof (rule compatible_step.App_left, rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam Prop (Lam Prop (Neg (Eq Prop (Var 0) (Var 1)))))
        p)
      (subst0 p
        (Lam Prop (Neg (Eq Prop (Var 0) (Var 1)))))"
    by (rule beta_contract.beta)
  show "beta_contract
    (pp_inequality_operator p)
    (pp_inequality_lambda p)"
    using step
    by (simp add: pp_inequality_operator_def pp_inequality_builder_def
      pp_inequality_lambda_def subst0_def shift_def)
qed

lemma pp_inequality_operator_second_beta:
  "compatible_step beta_contract
    (App (pp_inequality_lambda p) q)
    (Neg (Eq Prop q p))"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam Prop (Neg (Eq Prop (Var 0) (shift p))))
        q)
      (subst0 q (Neg (Eq Prop (Var 0) (shift p))))"
    by (rule beta_contract.beta)
  show "beta_contract
    (App (pp_inequality_lambda p) q)
    (Neg (Eq Prop q p))"
    using step
    by (simp add: pp_inequality_lambda_def subst0_def)
qed

lemma CEV_pp_inequality_operator_apply_eq:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop
      (App (pp_inequality_operator p) q)
      (Neg (Eq Prop q p))"
proof -
  let ?N = "pp_inequality_operator p"
  let ?L = "pp_inequality_lambda p"
  let ?R = "Neg (Eq Prop q p)"
  have N_type: "\<Gamma> \<turnstile> ?N : pp_unary_ty"
    using p_type by (rule typed_pp_inequality_operator)
  have L_type: "\<Gamma> \<turnstile> ?L : pp_unary_ty"
    using p_type by (rule typed_pp_inequality_lambda)
  have Nq_type: "\<Gamma> \<turnstile> App ?N q : Prop"
    using N_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Lq_type: "\<Gamma> \<turnstile> App ?L q : Prop"
    using L_type q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using q_type p_type by (intro has_type.Neg has_type.Eq)
  have first_iff:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App ?N q \<longleftrightarrow>\<^sub>o App ?L q)"
    using Nq_type Lq_type pp_inequality_operator_first_beta
    by (rule CEV_beta_step)
  have first_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (App ?N q) (App ?L q)"
    using Nq_type Lq_type first_iff by (rule CEV_zeroary_equivalence)
  have second_iff:
    "\<Gamma> \<turnstile>\<^sub>CEV (App ?L q \<longleftrightarrow>\<^sub>o ?R)"
    using Lq_type R_type pp_inequality_operator_second_beta
    by (rule CEV_beta_step)
  have second_eq:
    "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (App ?L q) ?R"
    using Lq_type R_type second_iff by (rule CEV_zeroary_equivalence)
  show ?thesis
    using Nq_type Lq_type R_type first_eq second_eq
    by (rule CEV_eq_trans_from)
qed

subsection \<open>Purity of the inequality operator\<close>

lemma pp_inequality_builder_purity_axiom:
  "pp_pure
      (Prop \<rightarrow>\<^sub>o pp_unary_ty)
      pp_inequality_builder
    \<in> pp_T2_min_axioms"
  unfolding pp_T2_min_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
proof (intro UnI1 CollectI exI conjI)
  show "[] \<turnstile> pp_inequality_builder :
    Prop \<rightarrow>\<^sub>o pp_unary_ty"
    by (rule typed_pp_inequality_builder)
  show "consts_of pp_inequality_builder = {}"
    by (simp add: pp_inequality_builder_def)
qed simp

lemma pp_inequality_builder_pure_in_core_extension:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure
      (Prop \<rightarrow>\<^sub>o pp_unary_ty)
      pp_inequality_builder"
proof -
  have core_proof:
    "\<Gamma> ; pp_T2_min_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure
        (Prop \<rightarrow>\<^sub>o pp_unary_ty)
        pp_inequality_builder"
    using pp_inequality_builder_purity_axiom
      typed_pp_pure[OF typed_pp_inequality_builder]
    by (rule CEV_axiom_proves.Axiom)
  show ?thesis
    using core_proof core by (rule CEV_axiom_proves_mono)
qed

lemma pp_inequality_operator_pure_from:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and pure_p:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop p"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_unary_ty (pp_inequality_operator p)"
proof -
  have closure:
    "pp_application_closure Prop pp_unary_ty \<in> T"
    using core unfolding pp_T2_min_axioms_def
      pp_application_closure_schema_def by blast
  have pure_builder:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure
        (Prop \<rightarrow>\<^sub>o pp_unary_ty)
        pp_inequality_builder"
    using pp_inequality_builder_pure_in_core_extension[OF core]
    by (rule CEV_axiom_from.Theorem)
  show ?thesis
    unfolding pp_inequality_operator_def
    using closure typed_pp_inequality_builder p_type
      pure_builder pure_p
    by (rule pp_axiom_application_closed_from)
qed

subsection \<open>The attainable-purity theorem\<close>

theorem CEV_Goodman_T2c_parameter:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Imp
        (pp_pure Prop p)
        (\<diamond>\<^sub>o (Eq Prop r p)))"
proof -
  let ?F = "pp_fun_prime r"
  let ?P = "pp_pure Prop p"
  let ?E = "Eq Prop r p"
  let ?N = "\<box>\<^sub>o (Neg ?E)"
  let ?I = "pp_inequality_operator p"
  let ?K = "pp_constant_operator ObjTrue"
  let ?S = "insert ?N (insert ?P {?F})"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using p_type by (rule typed_pp_pure)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using r_type p_type by (rule has_type.Eq)
  have N_type: "\<Gamma> \<turnstile> ?N : Prop"
    using E_type by (intro typed_ObjBox has_type.Neg)
  have I_type: "\<Gamma> \<turnstile> ?I : pp_unary_ty"
    using p_type by (rule typed_pp_inequality_operator)
  have K_type: "\<Gamma> \<turnstile> ?K : pp_unary_ty"
    using typed_ObjTrue by (rule typed_pp_constant_operator)
  have d_fun:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_pure_p:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have d_N:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?N"
    using N_type by (intro CEV_axiom_from.Assumption) simp
  have pure_I:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?I"
    using core p_type d_pure_p
    by (rule pp_inequality_operator_pure_from)
  have pure_K:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?K"
    using pp_constant_ObjTrue_pure_in_core_extension[OF core]
    by (rule CEV_axiom_from.Theorem)

  have Ir_type: "\<Gamma> \<turnstile> App ?I r : Prop"
    using I_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Kr_type: "\<Gamma> \<turnstile> App ?K r : Prop"
    using K_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have not_E_type: "\<Gamma> \<turnstile> Neg ?E : Prop"
    using E_type by (rule has_type.Neg)
  have beta_Ir:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I r) (Neg ?E)"
    using CEV_pp_inequality_operator_apply_eq[OF p_type r_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have N_eq_true:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ?E) ObjTrue"
    using d_N unfolding ObjBox_def .
  have Ir_eq_true:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I r) ObjTrue"
    using Ir_type not_E_type typed_ObjTrue beta_Ir N_eq_true
    by (rule CEV_axiom_from_eq_trans)
  have beta_Kr:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?K r) ObjTrue"
    using CEV_pp_constant_operator_apply_eq[OF typed_ObjTrue r_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have true_eq_Kr:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ObjTrue (App ?K r)"
    using Kr_type typed_ObjTrue beta_Kr
    by (rule CEV_axiom_from_eq_sym)
  have same_at_r:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I r) (App ?K r)"
    using Ir_type typed_ObjTrue Kr_type Ir_eq_true true_eq_Kr
    by (rule CEV_axiom_from_eq_trans)
  have I_eq_K:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty ?I ?K"
    using r_type I_type K_type d_fun pure_I pure_K same_at_r
    by (rule CEV_axiom_from_fun_prime)

  have Ip_type: "\<Gamma> \<turnstile> App ?I p : Prop"
    using I_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Kp_type: "\<Gamma> \<turnstile> App ?K p : Prop"
    using K_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have app_eq:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I p) (App ?K p)"
    using I_type K_type p_type I_eq_K
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have ref_type: "\<Gamma> \<turnstile> Eq Prop p p : Prop"
    using p_type p_type by (rule has_type.Eq)
  have neg_ref_type: "\<Gamma> \<turnstile> Neg (Eq Prop p p) : Prop"
    using ref_type by (rule has_type.Neg)
  have beta_Ip:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?I p) (Neg (Eq Prop p p))"
    using CEV_pp_inequality_operator_apply_eq[OF p_type p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have neg_ref_eq_Ip:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg (Eq Prop p p)) (App ?I p)"
    using Ip_type neg_ref_type beta_Ip
    by (rule CEV_axiom_from_eq_sym)
  have neg_ref_eq_Kp:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg (Eq Prop p p)) (App ?K p)"
    using neg_ref_type Ip_type Kp_type neg_ref_eq_Ip app_eq
    by (rule CEV_axiom_from_eq_trans)
  have beta_Kp:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App ?K p) ObjTrue"
    using CEV_pp_constant_operator_apply_eq[OF typed_ObjTrue p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have neg_ref_eq_true:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg (Eq Prop p p)) ObjTrue"
    using neg_ref_type Kp_type typed_ObjTrue neg_ref_eq_Kp beta_Kp
    by (rule CEV_axiom_from_eq_trans)
  have true_eq_neg_ref:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ObjTrue (Neg (Eq Prop p p))"
    using neg_ref_type typed_ObjTrue neg_ref_eq_true
    by (rule CEV_axiom_from_eq_sym)
  have d_true:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjTrue"
    using CEV_axiom_proves_ObjTrue by (rule CEV_axiom_from.Theorem)
  have d_neg_ref:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop p p)"
    using typed_ObjTrue neg_ref_type d_true true_eq_neg_ref
    by (rule CEV_axiom_from_eq_prop_elim)
  have d_ref:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p p"
    using p_type
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base
        CEV_proves.CE CE_proves.C C_proves.H H_proves.Ref)
  have d_false:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_ref d_neg_ref by (rule CEV_axiom_from_contradiction)

  have N_imp_false:
    "\<Gamma> ; T ; insert ?P {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?N ObjFalse"
    using N_type d_false by (rule CEV_axiom_from_deduction)
  have imp_to_not_N:
    "\<Gamma> ; T ; insert ?P {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?N ObjFalse) (Neg ?N)"
    using CEV_proves_imp_false_to_neg[OF N_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_diamond:
    "\<Gamma> ; T ; insert ?P {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<diamond>\<^sub>o ?E"
    unfolding ObjDiamond_def
    using N_imp_false imp_to_not_N by (rule CEV_axiom_from.MP)
  have pure_imp_diamond:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?P (\<diamond>\<^sub>o ?E)"
    using P_type d_diamond by (rule CEV_axiom_from_deduction)
  show ?thesis
    using F_type pure_imp_diamond
    by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_Goodman_T2c:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Forall Prop
        (Imp
          (pp_pure Prop (Var 0))
          (\<diamond>\<^sub>o
            (Eq Prop (shift r) (Var 0)))))"
proof (rule CEV_axiom_proves.Gen)
  show "\<Gamma> \<turnstile> pp_fun_prime r : Prop"
    using r_type by (rule typed_pp_fun_prime)
  show "Prop # \<Gamma> \<turnstile>
    Imp
      (pp_pure Prop (Var 0))
      (\<diamond>\<^sub>o (Eq Prop (shift r) (Var 0))) : Prop"
    using typed_var0[where \<sigma> = Prop and \<Gamma> = \<Gamma>]
      typed_shift_ctx[OF r_type, where \<sigma> = Prop]
    by (intro has_type.Imp typed_pp_pure typed_ObjDiamond has_type.Eq)
  show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (shift (pp_fun_prime r))
      (Imp
        (pp_pure Prop (Var 0))
        (\<diamond>\<^sub>o (Eq Prop (shift r) (Var 0))))"
    using CEV_Goodman_T2c_parameter[
      OF core
        typed_shift_ctx[OF r_type, where \<sigma> = Prop]
        typed_var0[where \<sigma> = Prop and \<Gamma> = \<Gamma>]]
    by simp
qed

end
