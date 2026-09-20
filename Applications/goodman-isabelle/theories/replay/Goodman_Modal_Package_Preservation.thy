theory Goodman_Modal_Package_Preservation
  imports Goodman_QLN_Translation
begin

section \<open>Replace translated axioms by provably equivalent native axioms\<close>

lemma gi_axiom_from_native_equivalent:
  assumes rich: "sg_rich G" and typed: "[] \<turnstile> A : Prop"
    and bl: "book_theory_formula gb_signature G B"
    and equivalent: "goodman_book_proves (\<lambda>_. UNIV) G U (book_iff G (gi_to_book G [] k A) B)"
    and member: "B \<in> U"
  shows "goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k A)"
proof -
  have al: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G [] k A)"
    by (rule gi_to_book_language[OF rich typed _ gi_constants_universal]; simp)
  have bl': "book_theory_formula (\<lambda>_. UNIV) G B" by (rule gi_gb_universal_language[OF bl])
  have b: "goodman_book_proves (\<lambda>_. UNIV) G U B"
    by (rule goodman_book_proves.Axiom[OF member bl'])
  show ?thesis using gi_goodman_equivalent_proofs[OF rich al bl' equivalent] b by blast
qed

lemma gi_zeroary_recombination_from_native:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow> gb_zeroary_recombination G \<in> U \<Longrightarrow>
    goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k pp_zeroary_recombination)"
  by (rule gi_axiom_from_native_equivalent;
    (assumption | rule typed_pp_zeroary_recombination | rule gb_zeroary_recombination_language
      | rule gi_zeroary_recombination_equivalence); assumption)

lemma gi_zeroary_exhaustion_from_native:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow> gb_zeroary_exhaustion G \<in> U \<Longrightarrow>
    goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k pp_zeroary_exhaustion)"
  by (rule gi_axiom_from_native_equivalent;
    (assumption | rule typed_pp_zeroary_exhaustion | rule gb_zeroary_exhaustion_language
      | rule gi_zeroary_exhaustion_equivalence); assumption)

lemma gi_unary_recombination_from_native:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow> gb_unary_recombination G \<in> U \<Longrightarrow>
    goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k pp_unary_recombination)"
  by (rule gi_axiom_from_native_equivalent;
    (assumption | rule typed_pp_unary_recombination | rule gb_unary_recombination_language
      | rule gi_unary_recombination_equivalence); assumption)

lemma gi_unary_exhaustion_from_native:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow> gb_unary_exhaustion G \<in> U \<Longrightarrow>
    goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k pp_unary_exhaustion)"
  by (rule gi_axiom_from_native_equivalent;
    (assumption | rule typed_pp_unary_exhaustion | rule gb_unary_exhaustion_language
      | rule gi_unary_exhaustion_equivalence); assumption)

lemma gi_persistence_from_native:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow> gb_persistence G \<sigma> \<in> U \<Longrightarrow>
    goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k (pp_persistence \<sigma>))"
  by (rule gi_axiom_from_native_equivalent;
    (assumption | rule typed_pp_persistence | rule gb_persistence_language
      | rule gi_persistence_equivalence); assumption)

lemma gi_background_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and stock: "gb_background_axioms G \<subseteq> U" and member: "A \<in> pp_background_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k A)"
proof -
  have im: "gi_to_book G [] k A \<in> gb_background_axioms G"
    using gi_background_inclusion[OF rich names] member by blast
  have member': "gi_to_book G [] k A \<in> U" using stock im by blast
  have language: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G [] k A)"
    by (rule gi_gb_universal_language, rule gb_background_axioms_language[OF rich im])
  show ?thesis by (rule goodman_book_proves.Axiom[OF member' language])
qed

lemma gi_PP_axiom_from_native:
  "gi_goodman_names k \<Longrightarrow> gb_target_PP \<in> U \<Longrightarrow>
    goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k pp_target_PP)"
  by (simp only: gi_PP_translation;
    rule goodman_book_proves.Axiom; (assumption | rule gi_gb_universal_language[OF gb_target_PP_language]))

theorem gi_native_package_preservation:
  assumes rich: "sg_rich G" and derivation: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sup>+ A"
    and closed: "\<And>B. B \<in> S \<Longrightarrow> [] \<turnstile> B : Prop"
    and support: "\<And>B. B \<in> S \<Longrightarrow> goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k B)"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  shows "goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G ns k A)"
  by (rule goodman_book_cut[OF gi_CEV_axiom_preservation[OF rich derivation closed chart distinct]];
    use support in blast)

section \<open>The Recombination, repaired, QLN, and persistence packages\<close>

lemma gi_recombination_package_support:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and stock: "gb_recombination_PP_axioms G \<subseteq> U"
    and member: "A \<in> pp_recombination_PP_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k A)"
proof -
  have background: "gb_background_axioms G \<subseteq> U"
    and pp: "gb_target_PP \<in> U" and zero: "gb_zeroary_recombination G \<in> U"
    and unary: "gb_unary_recombination G \<in> U"
    using stock unfolding gb_recombination_PP_axioms_def gb_recombination_background_def by auto
  show ?thesis using member unfolding pp_recombination_PP_axioms_def pp_recombination_background_axioms_def
    by (auto intro: gi_background_axiom_from_native[OF rich names background]
      gi_PP_axiom_from_native[OF names pp] gi_zeroary_recombination_from_native[OF rich names zero]
      gi_unary_recombination_from_native[OF rich names unary])
qed

lemma gi_QLN_package_support:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and stock: "gb_zeroary_unary_QLN_PP_axioms G \<subseteq> U"
    and member: "A \<in> pp_full_QLN_PP_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k A)"
proof -
  have rec: "gb_recombination_PP_axioms G \<subseteq> U"
    and zero: "gb_zeroary_exhaustion G \<in> U" and unary: "gb_unary_exhaustion G \<in> U"
    using stock unfolding gb_zeroary_unary_QLN_PP_axioms_def gb_exhaustion_axioms_def by auto
  have old: "pp_full_QLN_PP_axioms = pp_recombination_PP_axioms \<union> pp_exhaustion_axioms"
    unfolding pp_full_QLN_PP_axioms_def pp_full_QLN_background_axioms_def pp_recombination_PP_axioms_def by auto
  show ?thesis using member unfolding old pp_exhaustion_axioms_def
    by (auto intro: gi_recombination_package_support[OF rich names rec]
      gi_zeroary_exhaustion_from_native[OF rich names zero] gi_unary_exhaustion_from_native[OF rich names unary])
qed

theorem gi_recombination_PP_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_recombination_PP_axioms G) (gi_to_book G ns k A)"
  by (rule gi_native_package_preservation[OF rich derivation pp_recombination_PP_axioms_typed
    gi_recombination_package_support[OF rich names subset_refl] chart distinct])

theorem gi_QLN_PP_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; pp_full_QLN_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_zeroary_unary_QLN_PP_axioms G) (gi_to_book G ns k A)"
  by (rule gi_native_package_preservation[OF rich derivation pp_full_QLN_PP_axioms_typed
    gi_QLN_package_support[OF rich names subset_refl] chart distinct])

lemma gi_repaired_package_support:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and member: "A \<in> insert pp_zeroary_exhaustion pp_recombination_PP_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_recombination_PP_zeroary_exhaustion G) (gi_to_book G [] k A)"
  using member unfolding gb_recombination_PP_zeroary_exhaustion_def
  by (auto intro: gi_zeroary_exhaustion_from_native[OF rich names]
    gi_recombination_package_support[OF rich names])

theorem gi_repaired_PP_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; insert pp_zeroary_exhaustion pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_recombination_PP_zeroary_exhaustion G) (gi_to_book G ns k A)"
proof (rule gi_native_package_preservation[OF rich derivation _ gi_repaired_package_support[OF rich names] chart distinct])
  fix B assume "B \<in> insert pp_zeroary_exhaustion pp_recombination_PP_axioms"
  then show "[] \<turnstile> B : Prop" by (auto intro: typed_pp_zeroary_exhaustion pp_recombination_PP_axioms_typed)
qed

lemma gi_persistent_QLN_package_support:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and member: "A \<in> pp_full_QLN_PP_persistence_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G
    (gb_zeroary_unary_QLN_PP_axioms G \<union> gb_persistence_schema G) (gi_to_book G [] k A)"
  using member unfolding pp_full_QLN_PP_persistence_axioms_def pp_persistence_schema_def gb_persistence_schema_def
  by (auto intro: gi_persistence_from_native[OF rich names] gi_QLN_package_support[OF rich names])

theorem gi_persistent_QLN_PP_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; pp_full_QLN_PP_persistence_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  shows "goodman_book_proves (\<lambda>_. UNIV) G
    (gb_zeroary_unary_QLN_PP_axioms G \<union> gb_persistence_schema G) (gi_to_book G ns k A)"
proof (rule gi_native_package_preservation[OF rich derivation _ gi_persistent_QLN_package_support[OF rich names] chart distinct])
  fix B assume "B \<in> pp_full_QLN_PP_persistence_axioms"
  then show "[] \<turnstile> B : Prop"
    unfolding pp_full_QLN_PP_persistence_axioms_def pp_persistence_schema_def
    by (auto intro: pp_full_QLN_PP_axioms_typed typed_pp_persistence)
qed

text \<open>
  These four statements preserve whole CEV+ proofs into the independently
  written native packages, in the universal target signature. They are
  not converses, consistency proofs, or identifications of denotational
  stocks. Logical purity remains a one-way syntactic inclusion. Full QLN
  here means exactly the zeroary/unary pair of directions, not all arities.
\<close>

section \<open>The conditional consistency direction\<close>

theorem gi_native_consistency_implies_CEV_axiom_consistency:
  assumes rich: "sg_rich G" and consistent: "goodman_book_consistent (\<lambda>_. UNIV) G U"
    and preservation: "\<And>A. [] ; S \<turnstile>\<^sub>CEV\<^sup>+ A \<Longrightarrow>
      goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k A)"
  shows "CEV_axiom_consistent [] S"
proof (unfold CEV_axiom_consistent_def, intro notI)
  assume refutation: "[] ; S \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  have translated: "goodman_book_proves (\<lambda>_. UNIV) G U (gi_to_book G [] k ObjFalse)"
    by (rule preservation[OF refutation])
  have implication: "goodman_book_proves (\<lambda>_. UNIV) G U
    (book_imp (gi_to_book G [] k ObjFalse) (book_bottom G))"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H, rule gi_H_translated_false_elim[OF rich])
  have bottom: "goodman_book_proves (\<lambda>_. UNIV) G U (book_bottom G)"
    by (rule goodman_book_proves.MP[OF translated implication book_bottom_language[OF rich]])
  show False using consistent bottom unfolding goodman_book_consistent_def by blast
qed

corollary gi_recombination_PP_consistency_transfer:
  assumes rich: "sg_rich G"
    and consistent: "goodman_book_consistent (\<lambda>_. UNIV) G (gb_recombination_PP_axioms G)"
  shows "CEV_axiom_consistent [] pp_recombination_PP_axioms"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis by (rule gi_native_consistency_implies_CEV_axiom_consistency[OF rich consistent, where k=k],
    rule gi_recombination_PP_preservation[OF rich names]; (assumption | simp))
qed

corollary gi_QLN_PP_consistency_transfer:
  assumes rich: "sg_rich G"
    and consistent: "goodman_book_consistent (\<lambda>_. UNIV) G (gb_zeroary_unary_QLN_PP_axioms G)"
  shows "CEV_axiom_consistent [] pp_full_QLN_PP_axioms"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis by (rule gi_native_consistency_implies_CEV_axiom_consistency[OF rich consistent, where k=k],
    rule gi_QLN_PP_preservation[OF rich names]; (assumption | simp))
qed

corollary gi_repaired_PP_consistency_transfer:
  assumes rich: "sg_rich G"
    and consistent: "goodman_book_consistent (\<lambda>_. UNIV) G (gb_recombination_PP_zeroary_exhaustion G)"
  shows "CEV_axiom_consistent [] (insert pp_zeroary_exhaustion pp_recombination_PP_axioms)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis by (rule gi_native_consistency_implies_CEV_axiom_consistency[OF rich consistent, where k=k],
    rule gi_repaired_PP_preservation[OF rich names]; (assumption | simp))
qed

corollary gi_persistent_QLN_PP_consistency_transfer:
  assumes rich: "sg_rich G"
    and consistent: "goodman_book_consistent (\<lambda>_. UNIV) G
      (gb_zeroary_unary_QLN_PP_axioms G \<union> gb_persistence_schema G)"
  shows "CEV_axiom_consistent [] pp_full_QLN_PP_persistence_axioms"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis by (rule gi_native_consistency_implies_CEV_axiom_consistency[OF rich consistent, where k=k],
    rule gi_persistent_QLN_PP_preservation[OF rich names]; (assumption | simp))
qed

text \<open>
  Consistency here is CEV_axiom_consistent, the axiom extension that
  permits vector Equivalence above the added stock. It is not merely
  CEV_consistent, the weaker local/MP consequence relation. Native
  consistency remains an explicit unproved hypothesis in every corollary.
\<close>

end
