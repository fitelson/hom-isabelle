theory Bacon_PP_Goodman_Heredity_Rigidity
  imports 
    "Goodman_Legacy_03.Bacon_PP_Goodman_Heredity_Modal"
begin

section \<open>Purity of identity propositions and rigidity from Exhaustion\<close>

subsection \<open>A closed, constant-free identity builder\<close>

definition pp_eq_builder :: "otype \<Rightarrow> oterm" where
  "pp_eq_builder \<sigma> =
    Lam \<sigma> (Lam \<sigma> (Eq \<sigma> (Var 1) (Var 0)))"

lemma typed_pp_eq_builder:
  "\<Gamma> \<turnstile> pp_eq_builder \<sigma> :
    \<sigma> \<rightarrow>\<^sub>o (\<sigma> \<rightarrow>\<^sub>o Prop)"
  unfolding pp_eq_builder_def
  by (intro has_type.Lam has_type.Eq has_type.Var) (simp_all add: lookup_def)

lemma consts_of_pp_eq_builder:
  "consts_of (pp_eq_builder \<sigma>) = {}"
  by (simp add: pp_eq_builder_def)

lemma pp_eq_builder_purity_axiom:
  "pp_pure (\<sigma> \<rightarrow>\<^sub>o (\<sigma> \<rightarrow>\<^sub>o Prop))
      (pp_eq_builder \<sigma>) \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> pp_eq_builder \<sigma> :
      \<sigma> \<rightarrow>\<^sub>o (\<sigma> \<rightarrow>\<^sub>o Prop)"
    by (rule typed_pp_eq_builder)
  show "consts_of (pp_eq_builder \<sigma>) = {}"
    by (rule consts_of_pp_eq_builder)
  show "pp_pure (\<sigma> \<rightarrow>\<^sub>o (\<sigma> \<rightarrow>\<^sub>o Prop)) (pp_eq_builder \<sigma>) =
      pp_pure (\<sigma> \<rightarrow>\<^sub>o (\<sigma> \<rightarrow>\<^sub>o Prop)) (pp_eq_builder \<sigma>)"
    by simp
qed

subsection \<open>The two beta steps\<close>

lemma pp_eq_builder_first_beta:
  "compatible_step beta_contract
    (App (pp_eq_builder \<sigma>) X)
    (Lam \<sigma> (Eq \<sigma> (shift X) (Var 0)))"
proof -
  have step:
    "beta_contract
      (App (Lam \<sigma> (Lam \<sigma> (Eq \<sigma> (Var 1) (Var 0)))) X)
      (subst0 X (Lam \<sigma> (Eq \<sigma> (Var 1) (Var 0))))"
    by (rule beta_contract.beta)
  show ?thesis
    using step
    by (intro compatible_step.root)
      (simp add: pp_eq_builder_def subst0_def shift_def)
qed

lemma pp_eq_builder_second_beta:
  "compatible_step beta_contract
    (App (Lam \<sigma> (Eq \<sigma> (shift X) (Var 0))) Y)
    (Eq \<sigma> X Y)"
proof -
  have step:
    "beta_contract
      (App (Lam \<sigma> (Eq \<sigma> (shift X) (Var 0))) Y)
      (subst0 Y (Eq \<sigma> (shift X) (Var 0)))"
    by (rule beta_contract.beta)
  show ?thesis
    using step
    by (intro compatible_step.root)
      (simp add: subst0_def shift_def subst0_shift[of Y X, unfolded subst0_def shift_def])
qed

lemma CEV_pp_eq_builder_apply_eq:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma>"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop (App (App (pp_eq_builder \<sigma>) X) Y) (Eq \<sigma> X Y)"
proof -
  let ?L = "Lam \<sigma> (Eq \<sigma> (shift X) (Var 0))"
  have X_shift: "\<sigma> # \<Gamma> \<turnstile> shift X : \<sigma>"
    using X_type by (rule typed_shift_ctx)
  have v_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by (rule typed_var0)
  have L_type: "\<Gamma> \<turnstile> ?L : \<sigma> \<rightarrow>\<^sub>o Prop"
    using X_shift v_type by (intro has_type.Lam has_type.Eq)
  have left_type:
    "\<Gamma> \<turnstile> App (App (pp_eq_builder \<sigma>) X) Y : Prop"
    using has_type.App[OF typed_pp_eq_builder X_type] Y_type
    by (rule has_type.App)
  have mid_type: "\<Gamma> \<turnstile> App ?L Y : Prop"
    using L_type Y_type by (rule has_type.App)
  have right_type: "\<Gamma> \<turnstile> Eq \<sigma> X Y : Prop"
    using X_type Y_type by (rule has_type.Eq)
  have first:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App (App (pp_eq_builder \<sigma>) X) Y \<longleftrightarrow>\<^sub>o App ?L Y)"
    using left_type mid_type
      compatible_step.App_left[OF pp_eq_builder_first_beta]
    by (rule CEV_beta_step)
  have second:
    "\<Gamma> \<turnstile>\<^sub>CEV (App ?L Y \<longleftrightarrow>\<^sub>o Eq \<sigma> X Y)"
    using mid_type right_type pp_eq_builder_second_beta
    by (rule CEV_beta_step)
  have both:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App (App (pp_eq_builder \<sigma>) X) Y \<longleftrightarrow>\<^sub>o Eq \<sigma> X Y)"
    using left_type mid_type right_type first second
    by (rule CEV_biconditional_trans)
  show ?thesis
    using left_type right_type both by (rule CEV_zeroary_equivalence)
qed

subsection \<open>Identity propositions between pure terms are pure\<close>

lemma CEV_axiom_from_pure_eq_proposition:
  assumes closure1:
      "pp_application_closure \<sigma> (\<sigma> \<rightarrow>\<^sub>o Prop) \<in> T"
    and closure2: "pp_application_closure \<sigma> Prop \<in> T"
    and builder:
      "pp_pure (\<sigma> \<rightarrow>\<^sub>o (\<sigma> \<rightarrow>\<^sub>o Prop))
        (pp_eq_builder \<sigma>) \<in> T"
    and X_type: "\<Gamma> \<turnstile> X : \<sigma>"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma>"
    and pure_X: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<sigma> X"
    and pure_Y: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<sigma> Y"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure Prop (Eq \<sigma> X Y)"
proof -
  have B_type:
    "\<Gamma> \<turnstile> pp_eq_builder \<sigma> :
      \<sigma> \<rightarrow>\<^sub>o (\<sigma> \<rightarrow>\<^sub>o Prop)"
    by (rule typed_pp_eq_builder)
  have pure_builder:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure (\<sigma> \<rightarrow>\<^sub>o (\<sigma> \<rightarrow>\<^sub>o Prop)) (pp_eq_builder \<sigma>)"
    using builder typed_pp_pure[OF B_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  have pure_BX:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (App (pp_eq_builder \<sigma>) X)"
    using closure1 B_type X_type pure_builder pure_X
    by (rule pp_axiom_application_closed_from)
  have BX_type:
    "\<Gamma> \<turnstile> App (pp_eq_builder \<sigma>) X : \<sigma> \<rightarrow>\<^sub>o Prop"
    using B_type X_type by (rule has_type.App)
  have pure_BXY:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop (App (App (pp_eq_builder \<sigma>) X) Y)"
    using closure2 BX_type Y_type pure_BX pure_Y
    by (rule pp_axiom_application_closed_from)
  have BXY_type:
    "\<Gamma> \<turnstile> App (App (pp_eq_builder \<sigma>) X) Y : Prop"
    using BX_type Y_type by (rule has_type.App)
  have eq_type: "\<Gamma> \<turnstile> Eq \<sigma> X Y : Prop"
    using X_type Y_type by (rule has_type.Eq)
  have d_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App (App (pp_eq_builder \<sigma>) X) Y) (Eq \<sigma> X Y)"
    using CEV_pp_eq_builder_apply_eq[OF X_type Y_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using BXY_type eq_type pure_BXY d_eq
    by (rule CEV_axiom_from_pure_eq_transport)
qed

subsection \<open>Exhaustion gives rigidity for pure propositions\<close>

lemma CEV_axiom_from_pure_neg:
  assumes closure: "pp_application_closure Prop Prop \<in> T"
    and negpure: "pp_pure pp_unary_ty pp_negation_operator \<in> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and pure_p: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop p"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop (Neg p)"
proof -
  let ?N = pp_negation_operator
  have N_type: "\<Gamma> \<turnstile> ?N : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  have Np_type: "\<Gamma> \<turnstile> App ?N p : Prop"
    using N_type p_type unfolding pp_unary_ty_def by (rule has_type.App)
  have neg_p_type: "\<Gamma> \<turnstile> Neg p : Prop"
    using p_type by (rule has_type.Neg)
  have d_pure_N:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty ?N"
    using negpure typed_pp_pure[OF N_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Axiom)
  have d_pure_Np:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop (App ?N p)"
    using closure N_type p_type d_pure_N pure_p
    unfolding pp_unary_ty_def
    by (rule pp_axiom_application_closed_from)
  have Np_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?N p) (Neg p)"
    using CEV_pp_negation_apply_eq[OF p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using Np_type neg_p_type d_pure_Np Np_eq
    by (rule CEV_axiom_from_pure_eq_transport)
qed

lemma CEV_axiom_from_pure_diamond_elim:
  assumes exhaustion: "pp_zeroary_exhaustion \<in> T"
    and closure: "pp_application_closure Prop Prop \<in> T"
    and negpure: "pp_pure pp_unary_ty pp_negation_operator \<in> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and pure_p: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop p"
    and dia_p: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o p"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s p"
proof -
  have neg_p_type: "\<Gamma> \<turnstile> Neg p : Prop"
    using p_type by (rule has_type.Neg)
  have pure_neg:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure Prop (Neg p)"
    using closure negpure p_type pure_p by (rule CEV_axiom_from_pure_neg)
  have rule_neg:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_pure Prop (Neg p))
        (Imp (Neg p) (\<box>\<^sub>o (Neg p)))"
    using pp_axiom_zeroary_exhaustion_imp[OF exhaustion neg_p_type]
    by (rule CEV_axiom_from.Theorem)
  have neg_imp_box:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Neg p) (\<box>\<^sub>o (Neg p))"
    using pure_neg rule_neg by (rule CEV_axiom_from.MP)
  have box_type: "\<Gamma> \<turnstile> \<box>\<^sub>o (Neg p) : Prop"
    using neg_p_type by (rule typed_ObjBox)
  have taut:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp (Neg p) (\<box>\<^sub>o (Neg p)))
        (Imp (Neg (\<box>\<^sub>o (Neg p))) p)"
  proof (rule CEV_prop_tautology)
    have type:
      "\<Gamma> \<turnstile>
        Imp (Imp (Neg p) (\<box>\<^sub>o (Neg p)))
          (Imp (Neg (\<box>\<^sub>o (Neg p))) p) : Prop"
      using p_type box_type by auto
    moreover have
      "\<forall>v. prop_eval v
        (Imp (Imp (Neg p) (\<box>\<^sub>o (Neg p)))
          (Imp (Neg (\<box>\<^sub>o (Neg p))) p))"
      apply (simp only: prop_eval.simps) by blast
    ultimately show
      "prop_tautology \<Gamma>
        (Imp (Imp (Neg p) (\<box>\<^sub>o (Neg p)))
          (Imp (Neg (\<box>\<^sub>o (Neg p))) p))"
      unfolding prop_tautology_def by blast
  qed
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Neg (\<box>\<^sub>o (Neg p))) p"
    using neg_imp_box
      CEV_axiom_from.Theorem[OF CEV_axiom_proves.Base[OF taut]]
    by (rule CEV_axiom_from.MP)
  show ?thesis
    using dia_p step unfolding ObjDiamond_def by (rule CEV_axiom_from.MP)
qed

end
