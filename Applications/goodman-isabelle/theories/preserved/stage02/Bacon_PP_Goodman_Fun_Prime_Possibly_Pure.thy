theory Bacon_PP_Goodman_Fun_Prime_Possibly_Pure
  imports 
    "Goodman_Legacy_02.Bacon_PP_Goodman_Fun_Prime_Attainment"
begin

section \<open>Possibility is monotone in every CEV axiom extension\<close>

text \<open>
  We first make explicit a normal-modal consequence that is needed below.
  The premise is a theorem of the axiom extension, not a result depending on
  temporary assumptions.  It may therefore be necessitated legitimately.
\<close>

lemma CEV_axiom_diamond_mono:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and imp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (\<diamond>\<^sub>o A) (\<diamond>\<^sub>o B)"
proof -
  have neg_A_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by (rule has_type.Neg)
  have neg_B_type: "\<Gamma> \<turnstile> Neg B : Prop"
    using B_type by (rule has_type.Neg)
  have contra_taut:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp A B) (Imp (Neg B) (Neg A))"
  proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
    have type:
      "\<Gamma> \<turnstile>
        Imp (Imp A B) (Imp (Neg B) (Neg A)) : Prop"
      using A_type B_type by auto
    moreover have
      "\<forall>v. prop_eval v
        (Imp (Imp A B) (Imp (Neg B) (Neg A)))"
      apply (simp only: prop_eval.simps)
      by blast
    ultimately show
      "prop_tautology \<Gamma>
        (Imp (Imp A B) (Imp (Neg B) (Neg A)))"
      unfolding prop_tautology_def by blast
  qed
  have contra:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Neg B) (Neg A)"
    using imp CEV_axiom_proves.Base[OF contra_taut]
    by (rule CEV_axiom_proves.MP)
  have box_contra:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      \<box>\<^sub>o (Imp (Neg B) (Neg A))"
    using contra by (rule CEV_axiom_necessitation)
  have K:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      modal_K (Neg B) (Neg A)"
    using CEV_modal_K[OF neg_B_type neg_A_type]
    by (rule CEV_axiom_proves.Base)
  have box_imp:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o (Neg B)) (\<box>\<^sub>o (Neg A))"
    using box_contra K
    unfolding modal_K_def
    by (rule CEV_axiom_proves.MP)
  have box_neg_A_type:
    "\<Gamma> \<turnstile> \<box>\<^sub>o (Neg A) : Prop"
    using neg_A_type by (rule typed_ObjBox)
  have box_neg_B_type:
    "\<Gamma> \<turnstile> \<box>\<^sub>o (Neg B) : Prop"
    using neg_B_type by (rule typed_ObjBox)
  have outer_contra_taut:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp (\<box>\<^sub>o (Neg B)) (\<box>\<^sub>o (Neg A)))
        (Imp
          (Neg (\<box>\<^sub>o (Neg A)))
          (Neg (\<box>\<^sub>o (Neg B))))"
  proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
    have type:
      "\<Gamma> \<turnstile>
        Imp
          (Imp (\<box>\<^sub>o (Neg B)) (\<box>\<^sub>o (Neg A)))
          (Imp
            (Neg (\<box>\<^sub>o (Neg A)))
            (Neg (\<box>\<^sub>o (Neg B)))) : Prop"
      using box_neg_A_type box_neg_B_type by auto
    moreover have
      "\<forall>v. prop_eval v
        (Imp
          (Imp (\<box>\<^sub>o (Neg B)) (\<box>\<^sub>o (Neg A)))
          (Imp
            (Neg (\<box>\<^sub>o (Neg A)))
            (Neg (\<box>\<^sub>o (Neg B)))))"
      apply (simp only: prop_eval.simps)
      by blast
    ultimately show
      "prop_tautology \<Gamma>
        (Imp
          (Imp (\<box>\<^sub>o (Neg B)) (\<box>\<^sub>o (Neg A)))
          (Imp
            (Neg (\<box>\<^sub>o (Neg A)))
            (Neg (\<box>\<^sub>o (Neg B)))))"
      unfolding prop_tautology_def by blast
  qed
  have diamond_imp:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (Neg (\<box>\<^sub>o (Neg A)))
        (Neg (\<box>\<^sub>o (Neg B)))"
    using box_imp CEV_axiom_proves.Base[OF outer_contra_taut]
    by (rule CEV_axiom_proves.MP)
  then show ?thesis
    unfolding ObjDiamond_def .
qed

section \<open>Goodman T2d: a fun-prime proposition is possibly pure\<close>

text \<open>
  Goodman obtains this result from T2c and Persistence.  Persistence is in
  fact unnecessary.  Instantiate T2c at the logical truth proposition.  Its
  purity is an axiom of the purity schema, hence a theorem and therefore
  necessitable.  Identity transport yields
  \<open>(r = \<top>) \<longrightarrow> Pure(r)\<close>, and possibility monotonicity finishes the
  argument.
\<close>

lemma pp_ObjTrue_purity_axiom:
  "pp_pure Prop ObjTrue \<in> pp_T6_core_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
proof (intro UnI1 CollectI exI conjI)
  show "[] \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  show "consts_of ObjTrue = {}"
    by (simp add: ObjTrue_def)
qed simp

lemma pp_ObjTrue_pure_in_core_extension:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure Prop ObjTrue"
proof -
  have core_proof:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure Prop ObjTrue"
    using pp_ObjTrue_purity_axiom
      typed_pp_pure[OF typed_ObjTrue]
    by (rule CEV_axiom_proves.Axiom)
  show ?thesis
    using core_proof core by (rule CEV_axiom_proves_mono)
qed

lemma CEV_axiom_ObjTrue_identity_implies_pure:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Eq Prop r ObjTrue)
      (pp_pure Prop r)"
proof -
  let ?E = "Eq Prop r ObjTrue"
  let ?PT = "pp_pure Prop ObjTrue"
  let ?PR = "pp_pure Prop r"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have PT_type: "\<Gamma> \<turnstile> ?PT : Prop"
    using typed_ObjTrue by (rule typed_pp_pure)
  have PR_type: "\<Gamma> \<turnstile> ?PR : Prop"
    using r_type by (rule typed_pp_pure)
  have d_E:
    "\<Gamma> ; T ; {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using E_type by (intro CEV_axiom_from.Assumption) simp
  have true_eq_r:
    "\<Gamma> ; T ; {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ObjTrue r"
    using r_type typed_ObjTrue d_E
    by (rule CEV_axiom_from_eq_sym)
  have pure_eq:
    "\<Gamma> ; T ; {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ?PT ?PR"
    unfolding pp_pure_def
    using typed_pp_Pure typed_ObjTrue r_type true_eq_r
    by (rule CEV_axiom_from_eq_app_right)
  have d_PT:
    "\<Gamma> ; T ; {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PT"
    using pp_ObjTrue_pure_in_core_extension[OF core]
    by (rule CEV_axiom_from.Theorem)
  have d_PR:
    "\<Gamma> ; T ; {?E} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PR"
    using PT_type PR_type d_PT pure_eq
    by (rule CEV_axiom_from_eq_prop_elim)
  show ?thesis
    using E_type d_PR by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_Goodman_T2d:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (\<diamond>\<^sub>o (pp_pure Prop r))"
proof -
  let ?F = "pp_fun_prime r"
  let ?E = "Eq Prop r ObjTrue"
  let ?PT = "pp_pure Prop ObjTrue"
  let ?PR = "pp_pure Prop r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have PT_type: "\<Gamma> \<turnstile> ?PT : Prop"
    using typed_ObjTrue by (rule typed_pp_pure)
  have PR_type: "\<Gamma> \<turnstile> ?PR : Prop"
    using r_type by (rule typed_pp_pure)
  have d_F:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have t2c:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?F (Imp ?PT (\<diamond>\<^sub>o ?E))"
    using CEV_Goodman_T2c_parameter[
      OF pp_T2_min_axioms_into_T6_extension[OF core]
        r_type typed_ObjTrue]
    by (rule CEV_axiom_from.Theorem)
  have pure_imp_diamond:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?PT (\<diamond>\<^sub>o ?E)"
    using d_F t2c by (rule CEV_axiom_from.MP)
  have d_PT:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PT"
    using pp_ObjTrue_pure_in_core_extension[OF core]
    by (rule CEV_axiom_from.Theorem)
  have d_diamond_E:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<diamond>\<^sub>o ?E"
    using d_PT pure_imp_diamond by (rule CEV_axiom_from.MP)
  have identity_imp_pure:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?E ?PR"
    using core r_type
    by (rule CEV_axiom_ObjTrue_identity_implies_pure)
  have diamond_mono:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (\<diamond>\<^sub>o ?E) (\<diamond>\<^sub>o ?PR)"
    using CEV_axiom_diamond_mono[
      OF E_type PR_type identity_imp_pure]
    by (rule CEV_axiom_from.Theorem)
  have d_diamond_PR:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<diamond>\<^sub>o ?PR"
    using d_diamond_E diamond_mono by (rule CEV_axiom_from.MP)
  show ?thesis
    using F_type d_diamond_PR
    by (rule CEV_axiom_from_singleton_imp)
qed

end
