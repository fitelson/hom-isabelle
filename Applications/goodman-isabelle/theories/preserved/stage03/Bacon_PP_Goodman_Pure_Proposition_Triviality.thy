theory Bacon_PP_Goodman_Pure_Proposition_Triviality
  imports 
    "Goodman_Legacy_02.Bacon_PP_Goodman_Fun_Prime_Noncontingency"
begin

section \<open>Goodman T1: triviality of pure propositions\<close>

definition pp_T1_axioms :: "oterm set" where
  "pp_T1_axioms =
    pp_purity_schema \<union>
    pp_application_closure_schema \<union>
    {pp_zeroary_exhaustion}"

definition pp_proposition_extreme :: "oterm \<Rightarrow> oterm" where
  "pp_proposition_extreme p =
    Disj
      (Eq Prop p ObjTrue)
      (Eq Prop p ObjFalse)"

definition pp_T1_pure_propositions_extreme :: oterm where
  "pp_T1_pure_propositions_extreme =
    Forall Prop
      (Imp
        (pp_pure Prop (Var 0))
        (pp_proposition_extreme (Var 0)))"

lemma typed_pp_proposition_extreme:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile> pp_proposition_extreme p : Prop"
  unfolding pp_proposition_extreme_def
  using p_type typed_ObjTrue typed_ObjFalse
  by (intro has_type.Disj has_type.Eq)

lemma typed_pp_T1_pure_propositions_extreme:
  "\<Gamma> \<turnstile> pp_T1_pure_propositions_extreme : Prop"
  unfolding pp_T1_pure_propositions_extreme_def
proof (intro has_type.Forall has_type.Imp)
  show "Prop # \<Gamma> \<turnstile> pp_pure Prop (Var 0) : Prop"
    by (intro typed_pp_pure has_type.Var) (simp add: lookup_def)
  show "Prop # \<Gamma> \<turnstile> pp_proposition_extreme (Var 0) : Prop"
    by (intro typed_pp_proposition_extreme has_type.Var)
      (simp add: lookup_def)
qed

lemma pp_T1_purity_axiom:
  assumes "[] \<turnstile> M : \<sigma>"
    and "pp_logical_vocabulary M"
  shows "pp_pure \<sigma> M \<in> pp_T1_axioms"
  unfolding pp_T1_axioms_def pp_purity_schema_def
  using assms by blast

lemma pp_T1_application_closure_axiom:
  "pp_application_closure \<sigma> \<tau> \<in> pp_T1_axioms"
  unfolding pp_T1_axioms_def pp_application_closure_schema_def
  by blast

lemma pp_T1_zeroary_exhaustion_axiom:
  "pp_zeroary_exhaustion \<in> pp_T1_axioms"
  unfolding pp_T1_axioms_def by blast

lemma pp_T1_negation_purity_axiom:
  "pp_pure pp_unary_ty pp_negation_operator \<in> pp_T1_axioms"
  unfolding pp_T1_axioms_def
  using pp_negation_operator_purity_axiom by blast

lemma pp_axiom_zeroary_exhaustion_imp:
  assumes exhaustion: "pp_zeroary_exhaustion \<in> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_pure Prop p)
      (Imp p (\<box>\<^sub>o p))"
proof -
  have exhaustion_type:
    "\<Gamma> \<turnstile> pp_zeroary_exhaustion : Prop"
    by (rule infer_type_sound)
      (simp add: pp_zeroary_exhaustion_def pp_pure_def pp_Pure_def
        ObjBox_def ObjTrue_def lookup_def)
  have d_exhaustion:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_zeroary_exhaustion"
    using exhaustion exhaustion_type by (rule CEV_axiom_proves.Axiom)
  have body_type:
    "Prop # \<Gamma> \<turnstile>
      Imp
        (pp_pure Prop (Var 0))
        (Imp (Var 0) (\<box>\<^sub>o (Var 0))) : Prop"
    by (intro has_type.Imp typed_pp_pure typed_ObjBox has_type.Var)
      (simp_all add: lookup_def)
  have inst:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      subst0 p
        (Imp
          (pp_pure Prop (Var 0))
          (Imp (Var 0) (\<box>\<^sub>o (Var 0))))"
    using body_type p_type
      d_exhaustion[unfolded pp_zeroary_exhaustion_def]
    by (rule CEV_axiom_UI)
  show ?thesis
    using inst
    by (simp add: subst0_def pp_pure_def pp_Pure_def
      ObjBox_def ObjTrue_def)
qed

lemma CEV_axiom_from_pure_eq_transport:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma>"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma>"
    and pure_X:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<sigma> X"
    and XY:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> X Y"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<sigma> Y"
proof -
  have PX_type: "\<Gamma> \<turnstile> pp_pure \<sigma> X : Prop"
    using X_type by (rule typed_pp_pure)
  have PY_type: "\<Gamma> \<turnstile> pp_pure \<sigma> Y : Prop"
    using Y_type by (rule typed_pp_pure)
  have pure_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (pp_pure \<sigma> X) (pp_pure \<sigma> Y)"
    unfolding pp_pure_def
    using typed_pp_Pure X_type Y_type XY
    by (rule CEV_axiom_from_eq_app_right)
  show ?thesis
    using PX_type PY_type pure_X pure_eq
    by (rule CEV_axiom_from_eq_prop_elim)
qed

lemma CEV_Goodman_T1_parameter:
  assumes T1: "pp_T1_axioms \<subseteq> T"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_pure Prop p)
      (pp_proposition_extreme p)"
proof -
  let ?P = "pp_pure Prop p"
  let ?NP = "pp_pure Prop (Neg p)"
  let ?N = pp_negation_operator
  let ?Np = "App ?N p"
  let ?ET = "Eq Prop p ObjTrue"
  let ?EF = "Eq Prop p ObjFalse"
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using p_type by (rule typed_pp_pure)
  have neg_p_type: "\<Gamma> \<turnstile> Neg p : Prop"
    using p_type by (rule has_type.Neg)
  have N_type: "\<Gamma> \<turnstile> ?N : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  have Np_type: "\<Gamma> \<turnstile> ?Np : Prop"
    using N_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have d_P:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?P"
    using P_type by (intro CEV_axiom_from.Assumption) simp
  have d_pure_N:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty ?N"
  proof (rule CEV_axiom_from.Theorem)
    have axiom: "pp_pure pp_unary_ty ?N \<in> T"
      using pp_T1_negation_purity_axiom T1 by blast
    show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty ?N"
      using axiom typed_pp_pure[OF N_type]
      by (rule CEV_axiom_proves.Axiom)
  qed
  have closure: "pp_application_closure Prop Prop \<in> T"
    using pp_T1_application_closure_axiom T1 by blast
  have d_pure_Np:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure Prop ?Np"
    using closure N_type p_type d_pure_N d_P
    unfolding pp_unary_ty_def
    by (rule pp_axiom_application_closed_from)
  have Np_eq_neg:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?Np (Neg p)"
    using CEV_pp_negation_apply_eq[OF p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have d_NP:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?NP"
    using Np_type neg_p_type d_pure_Np Np_eq_neg
    by (rule CEV_axiom_from_pure_eq_transport)
  have exhaustion: "pp_zeroary_exhaustion \<in> T"
    using pp_T1_zeroary_exhaustion_axiom T1 by blast
  have p_rule:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?P (Imp p (\<box>\<^sub>o p))"
    using pp_axiom_zeroary_exhaustion_imp[OF exhaustion p_type]
    by (rule CEV_axiom_from.Theorem)
  have p_imp_box:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp p (\<box>\<^sub>o p)"
    using d_P p_rule by (rule CEV_axiom_from.MP)
  have neg_rule:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?NP (Imp (Neg p) (\<box>\<^sub>o (Neg p)))"
    using pp_axiom_zeroary_exhaustion_imp[OF exhaustion neg_p_type]
    by (rule CEV_axiom_from.Theorem)
  have neg_imp_box:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Neg p) (\<box>\<^sub>o (Neg p))"
    using d_NP neg_rule by (rule CEV_axiom_from.MP)
  have cases_taut:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp p (\<box>\<^sub>o p))
        (Imp (Imp (Neg p) (\<box>\<^sub>o (Neg p)))
          (Disj (\<box>\<^sub>o p) (\<box>\<^sub>o (Neg p))))"
  proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
    have type:
      "\<Gamma> \<turnstile>
        Imp (Imp p (\<box>\<^sub>o p))
          (Imp (Imp (Neg p) (\<box>\<^sub>o (Neg p)))
            (Disj (\<box>\<^sub>o p) (\<box>\<^sub>o (Neg p)))) : Prop"
      using p_type
      by (intro has_type.Imp has_type.Disj has_type.Neg typed_ObjBox)
    moreover have
      "\<forall>v. prop_eval v
        (Imp (Imp p (\<box>\<^sub>o p))
          (Imp (Imp (Neg p) (\<box>\<^sub>o (Neg p)))
            (Disj (\<box>\<^sub>o p) (\<box>\<^sub>o (Neg p)))))"
      apply (simp only: prop_eval.simps)
      by blast
    ultimately show
      "prop_tautology \<Gamma>
        (Imp (Imp p (\<box>\<^sub>o p))
          (Imp (Imp (Neg p) (\<box>\<^sub>o (Neg p)))
            (Disj (\<box>\<^sub>o p) (\<box>\<^sub>o (Neg p)))))"
      unfolding prop_tautology_def by blast
  qed
  have d_cases_taut:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp p (\<box>\<^sub>o p))
        (Imp (Imp (Neg p) (\<box>\<^sub>o (Neg p)))
          (Disj (\<box>\<^sub>o p) (\<box>\<^sub>o (Neg p))))"
    using cases_taut
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have step:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp (Neg p) (\<box>\<^sub>o (Neg p)))
        (Disj (\<box>\<^sub>o p) (\<box>\<^sub>o (Neg p)))"
    using p_imp_box d_cases_taut by (rule CEV_axiom_from.MP)
  have d_modal_cases:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Disj (\<box>\<^sub>o p) (\<box>\<^sub>o (Neg p))"
    using neg_imp_box step by (rule CEV_axiom_from.MP)
  have box_neg_to_false:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (\<box>\<^sub>o (Neg p)) ?EF"
    using CEV_axiom_box_neg_implies_eq_ObjFalse[OF p_type]
    by (rule CEV_axiom_from.Theorem)
  have finish_taut:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Disj (\<box>\<^sub>o p) (\<box>\<^sub>o (Neg p)))
        (Imp
          (Imp (\<box>\<^sub>o (Neg p)) ?EF)
          (Disj ?ET ?EF))"
  proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
    have box_p_type: "\<Gamma> \<turnstile> \<box>\<^sub>o p : Prop"
      using p_type by (rule typed_ObjBox)
    have box_neg_type: "\<Gamma> \<turnstile> \<box>\<^sub>o (Neg p) : Prop"
      using p_type by (intro typed_ObjBox has_type.Neg)
    have ET_type: "\<Gamma> \<turnstile> ?ET : Prop"
      using p_type typed_ObjTrue by (rule has_type.Eq)
    have EF_type: "\<Gamma> \<turnstile> ?EF : Prop"
      using p_type typed_ObjFalse by (rule has_type.Eq)
    have formula_type:
      "\<Gamma> \<turnstile>
        Imp
          (Disj (\<box>\<^sub>o p) (\<box>\<^sub>o (Neg p)))
          (Imp
            (Imp (\<box>\<^sub>o (Neg p)) ?EF)
            (Disj ?ET ?EF)) : Prop"
      using box_p_type box_neg_type ET_type EF_type
      by (intro has_type.Imp has_type.Disj)
    moreover have
      "\<forall>v. prop_eval v
        (Imp
          (Disj (\<box>\<^sub>o p) (\<box>\<^sub>o (Neg p)))
          (Imp
            (Imp (\<box>\<^sub>o (Neg p)) ?EF)
            (Disj ?ET ?EF)))"
      unfolding ObjBox_def
      apply (simp only: prop_eval.simps)
      by blast
    ultimately show "prop_tautology \<Gamma>
      (Imp
        (Disj (\<box>\<^sub>o p) (\<box>\<^sub>o (Neg p)))
        (Imp
          (Imp (\<box>\<^sub>o (Neg p)) ?EF)
          (Disj ?ET ?EF)))"
      unfolding prop_tautology_def by blast
  qed
  have d_finish:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Disj (\<box>\<^sub>o p) (\<box>\<^sub>o (Neg p)))
        (Imp
          (Imp (\<box>\<^sub>o (Neg p)) ?EF)
          (Disj ?ET ?EF))"
    using finish_taut
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have step2:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Imp (\<box>\<^sub>o (Neg p)) ?EF)
        (Disj ?ET ?EF)"
    using d_modal_cases d_finish by (rule CEV_axiom_from.MP)
  have d_extreme:
    "\<Gamma> ; T ; {?P} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_proposition_extreme p"
    unfolding pp_proposition_extreme_def
    using box_neg_to_false step2 by (rule CEV_axiom_from.MP)
  show ?thesis
    using P_type d_extreme by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_Goodman_T1_pure_propositions_extreme:
  assumes T1: "pp_T1_axioms \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_T1_pure_propositions_extreme"
proof -
  have body:
    "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (pp_pure Prop (Var 0))
        (pp_proposition_extreme (Var 0))"
    using CEV_Goodman_T1_parameter[
      OF T1, where \<Gamma> = "[Prop]" and p = "Var 0"]
    by (simp add: lookup_def)
  let ?Q =
    "Imp
      (pp_pure Prop (Var 0))
      (pp_proposition_extreme (Var 0))"
  have Q_type: "[Prop] \<turnstile> ?Q : Prop"
    using typed_pp_T1_pure_propositions_extreme[where \<Gamma> = "[]"]
    unfolding pp_T1_pure_propositions_extreme_def
    by (auto elim: has_type.cases)
  have guarded:
    "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ObjTrue ?Q"
    using typed_ObjTrue body by (rule CEV_axiom_imp_of_right)
  have generalized_imp:
    "[] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ObjTrue (Forall Prop ?Q)"
  proof (rule CEV_axiom_proves.Gen)
    show "[] \<turnstile> ObjTrue : Prop"
      by (rule typed_ObjTrue)
    show "[Prop] \<turnstile> ?Q : Prop"
      by (rule Q_type)
    show "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ObjTrue) ?Q"
      using guarded by (simp add: ObjTrue_def shift_def)
  qed
  have d_true: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjTrue"
    using CEV_proves_ObjTrue by (rule CEV_axiom_proves.Base)
  have generalized:
    "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall Prop ?Q"
    using d_true generalized_imp by (rule CEV_axiom_proves.MP)
  show ?thesis
    using generalized
    unfolding pp_T1_pure_propositions_extreme_def .
qed

end
