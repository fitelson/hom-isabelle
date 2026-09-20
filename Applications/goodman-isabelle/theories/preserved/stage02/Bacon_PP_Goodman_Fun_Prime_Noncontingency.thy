theory Bacon_PP_Goodman_Fun_Prime_Noncontingency
  imports 
    "Goodman_Legacy_02.Bacon_PP_Goodman_Fun_Prime_Possibly_Pure"
begin

section \<open>Goodman T2e: noncontingency is false but possible\<close>

text \<open>
  We render noncontingency in its standard modal form: a proposition is
  necessarily true or necessarily false.  In the identity theory of modality,
  the first disjunct is definitionally identity with truth; below we derive
  that the second disjunct entails identity with falsity.
\<close>

definition pp_noncontingent :: "oterm \<Rightarrow> oterm" where
  "pp_noncontingent p =
    Disj
      (\<box>\<^sub>o p)
      (\<box>\<^sub>o (Neg p))"

definition pp_T2e_false_but_possible :: "oterm \<Rightarrow> oterm" where
  "pp_T2e_false_but_possible p =
    Conj
      (Neg (pp_noncontingent p))
      (\<diamond>\<^sub>o (pp_noncontingent p))"

lemma typed_pp_noncontingent:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile> pp_noncontingent p : Prop"
  unfolding pp_noncontingent_def
  using p_type
  by (intro has_type.Disj typed_ObjBox has_type.Neg)

lemma typed_pp_T2e_false_but_possible:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile> pp_T2e_false_but_possible p : Prop"
  unfolding pp_T2e_false_but_possible_def
  using typed_pp_noncontingent[OF p_type]
  by (intro has_type.Conj has_type.Neg typed_ObjDiamond)

lemma CEV_axiom_identity_implies_noncontingent:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Eq Prop r ObjTrue)
      (pp_noncontingent r)"
proof -
  have true_eq_type:
    "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have false_eq_type:
    "\<Gamma> \<turnstile> \<box>\<^sub>o (Neg r) : Prop"
    using r_type by (intro typed_ObjBox has_type.Neg)
  have taut:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Eq Prop r ObjTrue)
        (Disj
          (\<box>\<^sub>o r)
          (\<box>\<^sub>o (Neg r)))"
    using true_eq_type false_eq_type
    unfolding ObjBox_def
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_disj_left_intro)
  show ?thesis
    unfolding pp_noncontingent_def
    using taut by (rule CEV_axiom_proves.Base)
qed

lemma CEV_double_negation_eq:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop p (Neg (Neg p))"
proof -
  have nn_type: "\<Gamma> \<turnstile> Neg (Neg p) : Prop"
    using p_type by (intro has_type.Neg)
  have iff:
    "\<Gamma> \<turnstile>\<^sub>CEV (p \<longleftrightarrow>\<^sub>o Neg (Neg p))"
  proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
    have iff_type:
      "\<Gamma> \<turnstile> (p \<longleftrightarrow>\<^sub>o Neg (Neg p)) : Prop"
      using p_type nn_type by (intro has_type.Conj has_type.Imp)
    show "prop_tautology \<Gamma> (p \<longleftrightarrow>\<^sub>o Neg (Neg p))"
      unfolding prop_tautology_def
      using iff_type by auto
  qed
  show ?thesis
    using p_type nn_type iff by (rule CEV_zeroary_equivalence)
qed

lemma CEV_axiom_box_neg_implies_eq_ObjFalse:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (\<box>\<^sub>o (Neg p))
      (Eq Prop p ObjFalse)"
proof -
  let ?N = pp_negation_operator
  let ?BN = "\<box>\<^sub>o (Neg p)"
  let ?NN = "Neg (Neg p)"
  let ?AN = "App ?N (Neg p)"
  let ?AT = "App ?N ObjTrue"
  have N_type: "\<Gamma> \<turnstile> ?N : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  have neg_p_type: "\<Gamma> \<turnstile> Neg p : Prop"
    using p_type by (rule has_type.Neg)
  have NN_type: "\<Gamma> \<turnstile> ?NN : Prop"
    using p_type by (intro has_type.Neg)
  have AN_type: "\<Gamma> \<turnstile> ?AN : Prop"
    using N_type neg_p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have AT_type: "\<Gamma> \<turnstile> ?AT : Prop"
    using N_type typed_ObjTrue unfolding pp_unary_ty_def
    by (rule has_type.App)
  have BN_type: "\<Gamma> \<turnstile> ?BN : Prop"
    using neg_p_type by (rule typed_ObjBox)
  have d_BN:
    "\<Gamma> ; T ; {?BN} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg p) ObjTrue"
    using BN_type
    unfolding ObjBox_def
    by (intro CEV_axiom_from.Assumption) simp
  have d_apps:
    "\<Gamma> ; T ; {?BN} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?AN ?AT"
    using N_type neg_p_type typed_ObjTrue d_BN
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have AN_eq_NN:
    "\<Gamma> ; T ; {?BN} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?AN ?NN"
    using CEV_pp_negation_apply_eq[OF neg_p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have NN_eq_AN:
    "\<Gamma> ; T ; {?BN} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?NN ?AN"
    using AN_type NN_type AN_eq_NN
    by (rule CEV_axiom_from_eq_sym)
  have NN_eq_AT:
    "\<Gamma> ; T ; {?BN} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?NN ?AT"
    using NN_type AN_type AT_type NN_eq_AN d_apps
    by (rule CEV_axiom_from_eq_trans)
  have AT_eq_false:
    "\<Gamma> ; T ; {?BN} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?AT ObjFalse"
    using CEV_pp_negation_apply_eq[OF typed_ObjTrue]
    unfolding ObjFalse_def
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have NN_eq_false:
    "\<Gamma> ; T ; {?BN} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?NN ObjFalse"
    using NN_type AT_type typed_ObjFalse NN_eq_AT AT_eq_false
    by (rule CEV_axiom_from_eq_trans)
  have p_eq_NN:
    "\<Gamma> ; T ; {?BN} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop p ?NN"
    using CEV_double_negation_eq[OF p_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have p_eq_false:
    "\<Gamma> ; T ; {?BN} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop p ObjFalse"
    using p_type NN_type typed_ObjFalse p_eq_NN NN_eq_false
    by (rule CEV_axiom_from_eq_trans)
  show ?thesis
    using BN_type p_eq_false by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_Goodman_T2e_false:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg (pp_noncontingent r))"
proof -
  let ?F = "pp_fun_prime r"
  let ?ET = "\<box>\<^sub>o r"
  let ?EN = "\<box>\<^sub>o (Neg r)"
  let ?EF = "Eq Prop r ObjFalse"
  let ?NT = "Neg ?ET"
  let ?NF = "Neg ?EF"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have ET_type: "\<Gamma> \<turnstile> ?ET : Prop"
    using r_type by (rule typed_ObjBox)
  have EN_type: "\<Gamma> \<turnstile> ?EN : Prop"
    using r_type by (intro typed_ObjBox has_type.Neg)
  have EF_type: "\<Gamma> \<turnstile> ?EF : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have d_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_NT:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?NT"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_fun_prime_neq_ObjTrue[OF core r_type]]
    unfolding ObjBox_def
    by (rule CEV_axiom_from.MP)
  have d_NF:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?NF"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_fun_prime_neq_ObjFalse[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have d_EN_EF:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?EN ?EF"
    using CEV_axiom_box_neg_implies_eq_ObjFalse[OF r_type]
    by (rule CEV_axiom_from.Theorem)
  have taut:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp ?NT (Imp ?NF
        (Imp (Imp ?EN ?EF)
          (Neg (Disj ?ET ?EN))))"
  proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
    have type:
      "\<Gamma> \<turnstile>
        Imp ?NT (Imp ?NF
          (Imp (Imp ?EN ?EF)
            (Neg (Disj ?ET ?EN)))) : Prop"
      using ET_type EN_type EF_type
      by (intro has_type.Imp has_type.Neg has_type.Disj)
    moreover have
      "\<forall>v. prop_eval v
        (Imp ?NT (Imp ?NF
          (Imp (Imp ?EN ?EF)
            (Neg (Disj ?ET ?EN)))))"
      apply (simp only: prop_eval.simps)
      by blast
    ultimately show
      "prop_tautology \<Gamma>
        (Imp ?NT (Imp ?NF
          (Imp (Imp ?EN ?EF)
            (Neg (Disj ?ET ?EN)))))"
      unfolding prop_tautology_def by blast
  qed
  have d_taut:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?NT (Imp ?NF
        (Imp (Imp ?EN ?EF)
          (Neg (Disj ?ET ?EN))))"
    using taut
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have step:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?NF
        (Imp (Imp ?EN ?EF)
          (Neg (Disj ?ET ?EN)))"
    using d_NT d_taut by (rule CEV_axiom_from.MP)
  have step2:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Imp ?EN ?EF)
        (Neg (Disj ?ET ?EN))"
    using d_NF step by (rule CEV_axiom_from.MP)
  have d_not_noncontingent:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (pp_noncontingent r)"
    unfolding pp_noncontingent_def
    using d_EN_EF step2 by (rule CEV_axiom_from.MP)
  show ?thesis
    using F_type d_not_noncontingent
    by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_Goodman_T2e_possible:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (\<diamond>\<^sub>o (pp_noncontingent r))"
proof -
  let ?F = "pp_fun_prime r"
  let ?E = "Eq Prop r ObjTrue"
  let ?PT = "pp_pure Prop ObjTrue"
  let ?NC = "pp_noncontingent r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have PT_type: "\<Gamma> \<turnstile> ?PT : Prop"
    using typed_ObjTrue by (rule typed_pp_pure)
  have NC_type: "\<Gamma> \<turnstile> ?NC : Prop"
    using r_type by (rule typed_pp_noncontingent)
  have d_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have t2c:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F (Imp ?PT (\<diamond>\<^sub>o ?E))"
    using CEV_Goodman_T2c_parameter[OF core r_type typed_ObjTrue]
    by (rule CEV_axiom_from.Theorem)
  have pure_imp_diamond:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?PT (\<diamond>\<^sub>o ?E)"
    using d_F t2c by (rule CEV_axiom_from.MP)
  have d_PT:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PT"
  proof (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Axiom)
    show "pp_pure Prop ObjTrue \<in> T"
    proof -
      have in_schema:
          "pp_pure Prop ObjTrue \<in> pp_purity_schema"
        unfolding pp_purity_schema_def pp_logical_vocabulary_def
      proof (intro CollectI exI conjI)
        show "[] \<turnstile> ObjTrue : Prop"
          by (rule typed_ObjTrue)
        show "consts_of ObjTrue = {}"
          by (simp add: ObjTrue_def)
        show "pp_pure Prop ObjTrue = pp_pure Prop ObjTrue"
          by simp
      qed
      show ?thesis
        using core in_schema unfolding pp_T2_min_axioms_def by blast
    qed
    show "\<Gamma> \<turnstile> pp_pure Prop ObjTrue : Prop"
      using typed_ObjTrue by (rule typed_pp_pure)
  qed
  have d_diamond_E:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<diamond>\<^sub>o ?E"
    using d_PT pure_imp_diamond by (rule CEV_axiom_from.MP)
  have E_imp_NC:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?E ?NC"
    using r_type by (rule CEV_axiom_identity_implies_noncontingent)
  have diamond_mono:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (\<diamond>\<^sub>o ?E) (\<diamond>\<^sub>o ?NC)"
    using CEV_axiom_diamond_mono[OF E_type NC_type E_imp_NC]
    by (rule CEV_axiom_from.Theorem)
  have d_diamond_NC:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<diamond>\<^sub>o ?NC"
    using d_diamond_E diamond_mono by (rule CEV_axiom_from.MP)
  show ?thesis
    using F_type d_diamond_NC
    by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_Goodman_T2e:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (pp_T2e_false_but_possible r)"
proof -
  let ?F = "pp_fun_prime r"
  let ?N = "pp_noncontingent r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have not_N_type: "\<Gamma> \<turnstile> Neg ?N : Prop"
    using typed_pp_noncontingent[OF r_type] by (rule has_type.Neg)
  have diamond_N_type: "\<Gamma> \<turnstile> \<diamond>\<^sub>o ?N : Prop"
    using typed_pp_noncontingent[OF r_type]
    by (rule typed_ObjDiamond)
  have d_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have d_not_N:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?N"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T2e_false[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have d_diamond_N:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o ?N"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T2e_possible[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have d_both:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T2e_false_but_possible r"
    unfolding pp_T2e_false_but_possible_def
    using d_not_N d_diamond_N
    by (rule CEV_axiom_from_conj_intro)
  show ?thesis
    using F_type d_both by (rule CEV_axiom_from_singleton_imp)
qed

end
