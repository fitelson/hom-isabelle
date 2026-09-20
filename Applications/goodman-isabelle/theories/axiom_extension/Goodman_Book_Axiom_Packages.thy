theory Goodman_Book_Axiom_Packages
  imports Goodman_Book_QLN Goodman_Book_Extension_Closure
begin

section \<open>The candidate Goodman axiom packages\<close>

text \<open>
  Logical purity ranges over ALL closed terms of the minimal book
  language with empty nonlogical signature. It is not restricted to
  an enumerated list of operators. On Bacon's exact carriers, equality
  with the old constructor stock is proved in the downstream theory
  Goodman_Exact_Stock_Correspondence, not assumed in these schemas.
  Full-F application closure and absence of nonpropositional fundamentals
  remain separate schemas. Only PP at the unary propositional type is
  included in the target package; Purity of Fun is not added.
\<close>

definition gb_closed_logical where
  "gb_closed_logical G \<sigma> M \<longleftrightarrow>
    book_in_language book_minimal_logical_type UNIV (\<lambda>_. {}) G M \<sigma> \<and> named_fv M = {}"

definition gb_purity_schema where
  "gb_purity_schema G = {A. \<exists>\<sigma> M. gb_closed_logical G \<sigma> M \<and> A = gb_pure \<sigma> M}"
definition gb_application_schema where
  "gb_application_schema G = {A. \<exists>\<sigma> \<tau>. A = gb_application_closure G \<sigma> \<tau>}"
definition gb_no_other_fundamentals_schema where
  "gb_no_other_fundamentals_schema G = {A. \<exists>\<sigma>. \<sigma> \<noteq> Prop \<and> A = gb_no_fundamentals G \<sigma>}"
definition gb_persistence_schema where
  "gb_persistence_schema G = {A. \<exists>\<sigma>. A = gb_persistence G \<sigma>}"

definition gb_background_axioms where
  "gb_background_axioms G = gb_purity_schema G \<union> gb_application_schema G \<union>
    {gb_unique_fundamental G Prop} \<union> gb_no_other_fundamentals_schema G"
definition gb_recombination_background where
  "gb_recombination_background G = gb_background_axioms G \<union>
    {gb_zeroary_recombination G, gb_unary_recombination G}"
definition gb_exhaustion_axioms where
  "gb_exhaustion_axioms G = {gb_zeroary_exhaustion G, gb_unary_exhaustion G}"
definition gb_recombination_PP_axioms where
  "gb_recombination_PP_axioms G = insert gb_target_PP (gb_recombination_background G)"
definition gb_zeroary_unary_QLN_PP_axioms where
  "gb_zeroary_unary_QLN_PP_axioms G = gb_recombination_PP_axioms G \<union> gb_exhaustion_axioms G"
definition gb_recombination_PP_zeroary_exhaustion where
  "gb_recombination_PP_zeroary_exhaustion G =
    insert (gb_zeroary_exhaustion G) (gb_recombination_PP_axioms G)"

lemma gb_closed_logical_in_signature:
  assumes logical: "gb_closed_logical G \<sigma> M"
  shows "book_in_language book_minimal_logical_type UNIV gb_signature G M \<sigma>"
proof -
  have empty: "book_in_language book_minimal_logical_type UNIV (\<lambda>_. {}) G M \<sigma>"
    using logical unfolding gb_closed_logical_def by blast
  show ?thesis by (rule book_language_signature_mono[OF empty]; simp)
qed

lemma gb_purity_schema_language:
  assumes member: "A \<in> gb_purity_schema G"
  shows "book_theory_formula gb_signature G A"
  using member unfolding gb_purity_schema_def
  by (auto intro: gb_pure_language gb_closed_logical_in_signature)

lemma gb_purity_schema_closed:
  "A \<in> gb_purity_schema G \<Longrightarrow> named_fv A = {}"
  by (auto simp: gb_purity_schema_def gb_closed_logical_def)

lemma gb_background_axioms_language:
  assumes rich: "sg_rich G" and member: "A \<in> gb_background_axioms G"
  shows "book_theory_formula gb_signature G A"
  using member unfolding gb_background_axioms_def gb_application_schema_def gb_no_other_fundamentals_schema_def
  by (auto intro: gb_purity_schema_language gb_application_closure_language[OF rich]
    gb_unique_fundamental_language[OF rich] gb_no_fundamentals_language[OF rich])

lemma gb_background_axioms_closed:
  "A \<in> gb_background_axioms G \<Longrightarrow> named_fv A = {}"
  unfolding gb_background_axioms_def gb_application_schema_def gb_no_other_fundamentals_schema_def
  by (auto simp: gb_purity_schema_closed gb_basic_axioms_closed)

lemma gb_recombination_PP_language:
  assumes rich: "sg_rich G" and member: "A \<in> gb_recombination_PP_axioms G"
  shows "book_theory_formula gb_signature G A"
  using member unfolding gb_recombination_PP_axioms_def gb_recombination_background_def
  by (auto intro: gb_target_PP_language gb_background_axioms_language[OF rich]
    gb_zeroary_recombination_language[OF rich] gb_unary_recombination_language[OF rich])

lemma gb_recombination_PP_closed:
  "A \<in> gb_recombination_PP_axioms G \<Longrightarrow> named_fv A = {}"
  unfolding gb_recombination_PP_axioms_def gb_recombination_background_def
  by (auto simp: gb_background_axioms_closed gb_basic_axioms_closed gb_QLN_axioms_closed)

lemma gb_QLN_PP_language:
  assumes rich: "sg_rich G" and member: "A \<in> gb_zeroary_unary_QLN_PP_axioms G"
  shows "book_theory_formula gb_signature G A"
  using member unfolding gb_zeroary_unary_QLN_PP_axioms_def gb_exhaustion_axioms_def
  by (auto intro: gb_recombination_PP_language[OF rich]
    gb_zeroary_exhaustion_language[OF rich] gb_unary_exhaustion_language[OF rich])

lemma gb_QLN_PP_closed:
  "A \<in> gb_zeroary_unary_QLN_PP_axioms G \<Longrightarrow> named_fv A = {}"
  unfolding gb_zeroary_unary_QLN_PP_axioms_def gb_exhaustion_axioms_def
  by (auto simp: gb_recombination_PP_closed gb_QLN_axioms_closed)

lemma gb_repaired_PP_language:
  "sg_rich G \<Longrightarrow> A \<in> gb_recombination_PP_zeroary_exhaustion G \<Longrightarrow>
    book_theory_formula gb_signature G A"
  unfolding gb_recombination_PP_zeroary_exhaustion_def
  by (auto intro: gb_recombination_PP_language gb_zeroary_exhaustion_language)

lemma gb_repaired_PP_closed:
  "A \<in> gb_recombination_PP_zeroary_exhaustion G \<Longrightarrow> named_fv A = {}"
  unfolding gb_recombination_PP_zeroary_exhaustion_def
  by (auto simp: gb_recombination_PP_closed gb_QLN_axioms_closed)

lemma gb_persistence_schema_language:
  "sg_rich G \<Longrightarrow> A \<in> gb_persistence_schema G \<Longrightarrow> book_theory_formula gb_signature G A"
  unfolding gb_persistence_schema_def by (auto intro: gb_persistence_language)
lemma gb_persistence_schema_closed:
  "A \<in> gb_persistence_schema G \<Longrightarrow> named_fv A = {}"
  unfolding gb_persistence_schema_def by (auto simp: gb_basic_axioms_closed)

theorem gb_package_inclusions:
  "gb_recombination_PP_axioms G \<subseteq> gb_recombination_PP_zeroary_exhaustion G"
  "gb_recombination_PP_zeroary_exhaustion G \<subseteq> gb_zeroary_unary_QLN_PP_axioms G"
  unfolding gb_recombination_PP_zeroary_exhaustion_def gb_zeroary_unary_QLN_PP_axioms_def gb_exhaustion_axioms_def
  by auto

lemma gb_target_PP_member: "gb_target_PP \<in> gb_recombination_PP_axioms G"
  by (simp add: gb_recombination_PP_axioms_def)

theorem gb_target_PP_necessitated:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_recombination_PP_axioms G) (book_box G gb_target_PP)"
  by (rule goodman_book_added_axiom_necessitation[
    OF rich gb_target_PP_member gb_target_PP_language])

theorem gb_QLN_consistency_implies_recombination_consistency:
  assumes strong: "goodman_book_consistent gb_signature G (gb_zeroary_unary_QLN_PP_axioms G)"
  shows "goodman_book_consistent gb_signature G (gb_recombination_PP_axioms G)"
proof -
  have inclusion: "gb_recombination_PP_axioms G \<subseteq> gb_zeroary_unary_QLN_PP_axioms G"
    using gb_package_inclusions by blast
  show ?thesis using strong goodman_book_mono[OF _ inclusion]
    unfolding goodman_book_consistent_def by blast
qed

end
