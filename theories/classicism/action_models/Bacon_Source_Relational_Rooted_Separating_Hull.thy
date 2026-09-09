theory Bacon_Source_Relational_Rooted_Separating_Hull
  imports Bacon_Source_Relational_Classical_Separating_Hull Bacon_Source_Relational_Reachable_Intensional
begin

section \<open>Rooted preparation preserving every retained outgoing profile\<close>

context paper_R_classicism_hull
begin

abbreviation rooted_objects where
  "rooted_objects \<equiv> paper_reachable_objects generated_arrows paper_arrow_source paper_arrow_target Root"
abbreviation rooted_arrows where
  "rooted_arrows \<equiv> paper_reachable_arrows generated_arrows paper_arrow_source paper_arrow_target Root"

theorem paper_R_classicism_rooted_hull_subcategory:
  "paper_R_bbk_subcategory signature stock rooted_objects rooted_arrows"
  by (rule paper_R_bbk_reachable_subcategory[OF paper_R_classicism_hull_subcategory])

theorem paper_R_classicism_rooted_hull_category:
  "paper_rooted_category rooted_objects rooted_arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
  by (rule paper_R_bbk_reachable_rooted_category[OF paper_R_classicism_hull_subcategory paper_R_classicism_hull_root])

lemma paper_R_classicism_rooted_hull_root:
  "Root \<in> rooted_objects"
  by (rule paper_rooted_category.root_object[OF paper_R_classicism_rooted_hull_category])

lemma paper_R_classicism_rooted_objects_subset:
  "rooted_objects \<subseteq> generated_objects"
  by (rule paper_R_bbk_reachable_objects_subset[OF paper_R_classicism_hull_subcategory])

lemma paper_R_classicism_rooted_arrows_subset:
  "rooted_arrows \<subseteq> generated_arrows"
  by (rule subsetI; rule paper_reachable_arrows_original; assumption)

lemma paper_R_classicism_rooted_hull_domains:
  assumes object: "M \<in> rooted_objects"
  shows "(\<Union>\<sigma>. paper_bbk_domain M \<sigma>) \<subseteq> U"
  by (rule paper_R_classicism_hull_domains[OF subsetD[OF paper_R_classicism_rooted_objects_subset object]])

theorem paper_R_classicism_rooted_hull_canonical:
  "paper_R_bbk_canonical_subcategory signature stock rooted_objects rooted_arrows"
  unfolding paper_R_bbk_canonical_subcategory_def
proof (rule conjI[OF paper_R_classicism_rooted_hull_subcategory], intro ballI)
  fix M
  assume object: "M \<in> rooted_objects"
  have generated: "M \<in> generated_objects" by (rule subsetD[OF paper_R_classicism_rooted_objects_subset object])
  have original: "M \<in> full_objects" by (rule subsetD[OF paper_R_classicism_hull_objects_subset generated])
  show "paper_R_bbk_data_canonical signature stock M" by (rule paper_R_bounded_theory_models_canonical[OF original])
qed

theorem paper_R_classicism_rooted_hull_intensional:
  "paper_R_intensional_on signature stock rooted_objects rooted_arrows"
  by (rule paper_R_bbk_reachable_intensional[OF paper_R_classicism_hull_subcategory paper_R_classicism_hull_intensional])

lemma paper_R_classicism_rooted_outgoing_iff:
  assumes object: "M \<in> rooted_objects"
  shows "(r \<in> rooted_arrows \<and> paper_arrow_source r = M) \<longleftrightarrow>
    (r \<in> generated_arrows \<and> paper_arrow_source r = M)"
  by (rule paper_R_bbk_reachable_outgoing_iff[OF paper_R_classicism_hull_subcategory object])

lemma paper_R_classicism_rooted_truth_profile:
  assumes object: "M \<in> rooted_objects"
  shows "paper_bbk_truth_profile_on rooted_arrows M p = paper_bbk_truth_profile_on generated_arrows M p"
  by (rule paper_R_truth_profile_outgoing_cong; rule paper_R_classicism_rooted_outgoing_iff[OF object])

lemma paper_R_classicism_rooted_application_profile:
  assumes object: "M \<in> rooted_objects"
  shows "paper_R_app_profile_on signature stock rooted_arrows M \<sigma> \<tau> d =
    paper_R_app_profile_on signature stock generated_arrows M \<sigma> \<tau> d"
  by (rule paper_R_app_profile_outgoing_cong; rule paper_R_classicism_rooted_outgoing_iff[OF object])

lemma paper_R_classicism_rooted_intension:
  assumes object: "M \<in> rooted_objects"
  shows "paper_R_intension_on signature stock rooted_arrows M \<sigma>s d =
    paper_R_intension_on signature stock generated_arrows M \<sigma>s d"
  by (rule paper_R_intension_outgoing_cong; rule paper_R_classicism_rooted_outgoing_iff[OF object])

end

text \<open>
  The root record and all retained interpretation/valuation data are
  unchanged. Every outgoing arrow from a reachable object is retained,
  so the displayed three profiles are exactly equal. Root arrows need
  not be unique. No equality of the two common theories, inherited
  intensionality under an arbitrary deletion, or action-model premise
  is asserted. Source: Proposition 3.22, pp.57 and 72.
\<close>

end
