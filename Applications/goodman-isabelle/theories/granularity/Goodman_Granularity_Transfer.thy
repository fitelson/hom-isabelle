theory Goodman_Granularity_Transfer
  imports Goodman_Legacy_Granularity_QLN.Bacon_PP_Goodman_Granularity_QLN
    Goodman_Integration_Individual.Goodman_T45_Transfer
begin

section \<open>Only logical purity, application closure and unary QLN are needed\<close>

definition gi_granularity_source where
  "gi_granularity_source = pp_T2_min_axioms \<union> {pp_unary_recombination, pp_unary_exhaustion}"

definition gb_granularity_axioms where
  "gb_granularity_axioms G = gb_T2_min_axioms G \<union> {gb_unary_recombination G, gb_unary_exhaustion G}"

definition gi_granularity_conditional where
  "gi_granularity_conditional Z r = Imp (Conj (pp_pure pp_unary_ty Z) (pp_fun Prop r))
    (Conj (Imp (pp_QLN_granularity_at Z r) (pp_QLN_truth_uniform_at Z))
      (Imp (pp_QLN_truth_uniform_at Z) (pp_QLN_granularity_at Z r)))"

lemma gi_granularity_logical_builder_pure:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
    and closed: "[] \<turnstile> B : \<sigma>" and logical: "pp_logical_vocabulary B"
    and typed: "\<Gamma> \<turnstile> B : \<sigma>"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<sigma> B"
proof -
  have member: "pp_pure \<sigma> B \<in> T"
    using core closed logical unfolding pp_T2_min_axioms_def pp_purity_schema_def by blast
  show ?thesis by (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Axiom[OF member typed_pp_pure[OF typed]])
qed

lemma gi_granularity_pure_agreement:
  assumes core: "pp_T2_min_axioms \<subseteq> T" and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and pure_z: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Z"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty (pp_agreement_operator Z)"
proof -
  have logical: "pp_logical_vocabulary pp_agreement_operator_builder"
    by (simp add: pp_logical_vocabulary_def pp_agreement_operator_builder_def)
  have pure_builder: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure (Arr pp_unary_ty pp_unary_ty) pp_agreement_operator_builder"
    by (rule gi_granularity_logical_builder_pure[OF core typed_pp_agreement_operator_builder logical typed_pp_agreement_operator_builder])
  have closure: "pp_application_closure pp_unary_ty pp_unary_ty \<in> T"
    using core unfolding pp_T2_min_axioms_def pp_application_closure_schema_def by blast
  show ?thesis unfolding pp_agreement_operator_def
    by (rule pp_axiom_application_closed_from[OF closure typed_pp_agreement_operator_builder zt pure_builder pure_z])
qed

lemma gi_granularity_pure_disagreement:
  assumes core: "pp_T2_min_axioms \<subseteq> T" and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty"
    and pure_z: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Z"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty (pp_disagreement_operator Z)"
proof -
  have logical: "pp_logical_vocabulary pp_disagreement_operator_builder"
    by (simp add: pp_logical_vocabulary_def pp_disagreement_operator_builder_def)
  have pure_builder: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure (Arr pp_unary_ty pp_unary_ty) pp_disagreement_operator_builder"
    by (rule gi_granularity_logical_builder_pure[OF core typed_pp_disagreement_operator_builder logical typed_pp_disagreement_operator_builder])
  have closure: "pp_application_closure pp_unary_ty pp_unary_ty \<in> T"
    using core unfolding pp_T2_min_axioms_def pp_application_closure_schema_def by blast
  show ?thesis unfolding pp_disagreement_operator_def
    by (rule pp_axiom_application_closed_from[OF closure typed_pp_disagreement_operator_builder zt pure_builder pure_z])
qed

theorem gi_granularity_conditional_source:
  assumes zt: "\<Gamma> \<turnstile> Z : pp_unary_ty" and rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; gi_granularity_source \<turnstile>\<^sub>CEV\<^sup>+ gi_granularity_conditional Z r"
proof -
  let ?A = "Conj (pp_pure pp_unary_ty Z) (pp_fun Prop r)"
  have at: "\<Gamma> \<turnstile> ?A : Prop" by (intro has_type.Conj typed_pp_pure[OF zt] typed_pp_fun[OF rt])
  have assumed: "\<Gamma> ; gi_granularity_source ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    by (rule CEV_axiom_from.Assumption; use at in auto)
  have pure_z: "\<Gamma> ; gi_granularity_source ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty Z"
    by (rule CEV_axiom_from_conj_left[OF assumed])
  have fun_r: "\<Gamma> ; gi_granularity_source ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun Prop r"
    by (rule CEV_axiom_from_conj_right[OF assumed])
  have core: "pp_T2_min_axioms \<subseteq> gi_granularity_source" by (auto simp: gi_granularity_source_def)
  have recombination: "pp_unary_recombination \<in> gi_granularity_source" by (simp add: gi_granularity_source_def)
  have exhaustion: "pp_unary_exhaustion \<in> gi_granularity_source" by (simp add: gi_granularity_source_def)
  have equivalence: "\<Gamma> ; gi_granularity_source ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    (pp_QLN_granularity_at Z r \<longleftrightarrow>\<^sub>o pp_QLN_truth_uniform_at Z)"
    by (rule CEV_axiom_from_QLN_granularity_iff_truth_uniform[OF recombination exhaustion zt rt
      gi_granularity_pure_agreement[OF core zt pure_z] gi_granularity_pure_disagreement[OF core zt pure_z] fun_r])
  show ?thesis unfolding gi_granularity_conditional_def
    by (rule CEV_axiom_from_singleton_imp[OF at equivalence])
qed

lemma gi_granularity_source_closed:
  "A \<in> gi_granularity_source \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding gi_granularity_source_def
  by (auto intro: gi_T2_min_axioms_closed typed_pp_unary_recombination typed_pp_unary_exhaustion)

lemma gb_granularity_axioms_language:
  "sg_rich G \<Longrightarrow> A \<in> gb_granularity_axioms G \<Longrightarrow> book_theory_formula gb_signature G A"
  unfolding gb_granularity_axioms_def
  by (auto intro: gb_T2_min_axioms_language gb_unary_recombination_language gb_unary_exhaustion_language)

lemma gi_granularity_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and member: "A \<in> gi_granularity_source"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_granularity_axioms G) (gi_to_book G [] k A)"
proof -
  have core: "goodman_book_proves (\<lambda>_. UNIV) G (gb_granularity_axioms G) (gi_to_book G [] k B)"
    if "B \<in> pp_T2_min_axioms" for B
    by (rule goodman_book_mono[OF gi_T2_min_axiom_from_native[OF rich names that]];
      auto simp: gb_granularity_axioms_def)
  have recombination: "goodman_book_proves (\<lambda>_. UNIV) G (gb_granularity_axioms G)
    (gi_to_book G [] k pp_unary_recombination)"
    by (rule gi_unary_recombination_from_native[OF rich names]; simp add: gb_granularity_axioms_def)
  have exhaustion: "goodman_book_proves (\<lambda>_. UNIV) G (gb_granularity_axioms G)
    (gi_to_book G [] k pp_unary_exhaustion)"
    by (rule gi_unary_exhaustion_from_native[OF rich names]; simp add: gb_granularity_axioms_def)
  show ?thesis using member core recombination exhaustion unfolding gi_granularity_source_def by blast
qed

lemma gi_granularity_admitted:
  assumes names: "gi_goodman_names k" and za: "gi_constants_admitted k gb_signature Z"
    and ra: "gi_constants_admitted k gb_signature r"
  shows "gi_constants_admitted k gb_signature (gi_granularity_conditional Z r)"
  using names za ra
  by (simp add: gi_granularity_conditional_def pp_QLN_granularity_at_def pp_QLN_truth_uniform_at_def
    pp_agreement_operator_def pp_disagreement_operator_def pp_agreement_operator_builder_def pp_disagreement_operator_builder_def
    pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def gi_goodman_names_def gb_signature_def
    ObjBox_def ObjTrue_def shift_def gi_constants_rename)

theorem gi_granularity_iff_truth_uniform:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty" and rt: "\<Gamma> \<turnstile> r : Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and za: "gi_constants_admitted k gb_signature Z" and ra: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_granularity_axioms G)
    (gi_to_book G ns k (gi_granularity_conditional Z r))"
proof -
  have source: "\<Gamma> ; gi_granularity_source \<turnstile>\<^sub>CEV\<^sup>+ gi_granularity_conditional Z r"
    by (rule gi_granularity_conditional_source[OF zt rt])
  have admitted: "gi_constants_admitted k gb_signature (gi_granularity_conditional Z r)"
    by (rule gi_granularity_admitted[OF names za ra])
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_granularity_axioms G)
    (gi_to_book G ns k (gi_granularity_conditional Z r))"
    by (rule gi_native_package_preservation[OF rich source gi_granularity_source_closed
      gi_granularity_axiom_from_native[OF rich names] chart distinct])
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich source chart admitted universal
    gb_granularity_axioms_language[OF rich]])
qed

text \<open>
  The local guard Pure(Z) ∧ Fun(r) is DISCHARGED by the ordinary local
  deduction rule, not inserted into the axiom stock. Neither PP nor
  Persistence nor zeroary Exhaustion is needed. The conclusion compares
  □(Zr↔r)∨□¬(Zr↔r) with the universal truth-uniformity disjunction.
  It does not prove either disjunct; material biconditional is not identity.
  The separate HOL cardinal results retain all their cardinal premises.
\<close>

end
