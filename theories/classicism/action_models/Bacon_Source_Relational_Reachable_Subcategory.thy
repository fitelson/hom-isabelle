theory Bacon_Source_Relational_Reachable_Subcategory
  imports Bacon_Source_Relational_Subcategory Bacon_Source_Reachable_Category
begin

section \<open>Reachability preserves the selected R model category\<close>

text \<open>
  Starting at M₀, retain exactly the objects reached by an original
  selected arrow, and all original selected arrows between retained
  objects. Source: the root convention on p.55 and Proposition 3.22,
  pp.57 and 72. No additional BBK homomorphism is inserted.

  Representation: the existing generic reachable sets retain the original
  records, interpretations, valuations, and maps. Their R validity is
  inherited. This restriction neither normalizes objects nor equates
  the common theories of the original and restricted collections.
\<close>

theorem paper_R_bbk_reachable_subcategory:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
  shows "paper_R_bbk_subcategory \<Sigma> G
    (paper_reachable_objects Arrows paper_arrow_source paper_arrow_target M0)
    (paper_reachable_arrows Arrows paper_arrow_source paper_arrow_target M0)"
proof -
  let ?Obj = "paper_reachable_objects Arrows paper_arrow_source paper_arrow_target M0"
  let ?Arrows = "paper_reachable_arrows Arrows paper_arrow_source paper_arrow_target M0"
  interpret Original: paper_category Obj Arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_R_bbk_subcategory_category[OF category])
  interpret Reach: paper_category ?Obj ?Arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule Original.paper_reachable_category)
  show ?thesis unfolding paper_R_bbk_subcategory_def
  proof (intro conjI)
    show "\<forall>M\<in>?Obj. paper_R_bbk_data_valid \<Sigma> G M"
    proof (intro ballI)
      fix M
      assume reachable: "M \<in> ?Obj"
      have member: "M \<in> Obj" by (rule Original.paper_reachable_object_original[OF reachable])
      show "paper_R_bbk_data_valid \<Sigma> G M" by (rule paper_R_bbk_subcategory_models[OF category member])
    qed
  next
    show "?Arrows \<subseteq> paper_R_bbk_arrows \<Sigma> G ?Obj"
    proof
      fix f
      assume reachable: "f \<in> ?Arrows"
      have original: "f \<in> Arrows" by (rule paper_reachable_arrows_original[OF reachable])
      have full_arrow: "f \<in> paper_R_bbk_arrows \<Sigma> G Obj"
        by (rule paper_R_bbk_subcategory_arrow[OF category original])
      have typed: "f \<in> paper_typed_arrows Obj paper_bbk_domain" by (rule paper_R_bbk_arrows_typed[OF full_arrow])
      have source: "paper_arrow_source f \<in> ?Obj" and target: "paper_arrow_target f \<in> ?Obj"
        using reachable by (auto simp only: paper_reachable_arrows_member)
      have restricted_typed: "f \<in> paper_typed_arrows ?Obj paper_bbk_domain"
        using typed source target unfolding paper_typed_arrows_def by blast
      show "f \<in> paper_R_bbk_arrows \<Sigma> G ?Obj"
        by (rule paper_R_bbk_arrowsI[OF restricted_typed paper_R_bbk_arrows_morphism[OF full_arrow]])
    qed
  next
    show "\<forall>M\<in>?Obj. paper_typed_identity paper_bbk_domain M \<in> ?Arrows"
      by (intro ballI, rule Reach.identity_arrow, assumption)
  next
    show "\<forall>f\<in>?Arrows. \<forall>g\<in>?Arrows. paper_arrow_target f = paper_arrow_source g \<longrightarrow>
      paper_typed_compose paper_bbk_domain g f \<in> ?Arrows"
      by (intro ballI impI, rule Reach.compose_arrow; assumption)
  qed
qed

theorem paper_R_bbk_reachable_rooted_category:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows" and root: "M0 \<in> Obj"
  shows "paper_rooted_category
    (paper_reachable_objects Arrows paper_arrow_source paper_arrow_target M0)
    (paper_reachable_arrows Arrows paper_arrow_source paper_arrow_target M0)
    paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain)
    (paper_typed_identity paper_bbk_domain) M0"
proof -
  interpret Original: paper_category Obj Arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_R_bbk_subcategory_category[OF category])
  show ?thesis by (rule Original.paper_reachable_rooted_category[OF root])
qed

lemma paper_R_bbk_reachable_objects_subset:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
  shows "paper_reachable_objects Arrows paper_arrow_source paper_arrow_target M0 \<subseteq> Obj"
proof -
  interpret Original: paper_category Obj Arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_R_bbk_subcategory_category[OF category])
  show ?thesis by (rule subsetI, rule Original.paper_reachable_object_original, assumption)
qed

lemma paper_R_bbk_reachable_outgoing_iff:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and reachable: "M \<in> paper_reachable_objects Arrows paper_arrow_source paper_arrow_target M0"
  shows "(h \<in> paper_reachable_arrows Arrows paper_arrow_source paper_arrow_target M0 \<and> paper_arrow_source h = M)
    \<longleftrightarrow> (h \<in> Arrows \<and> paper_arrow_source h = M)"
proof -
  interpret Original: paper_category Obj Arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_R_bbk_subcategory_category[OF category])
  have equal: "paper_outgoing (paper_reachable_arrows Arrows paper_arrow_source paper_arrow_target M0)
      paper_arrow_source M = paper_outgoing Arrows paper_arrow_source M"
    by (rule Original.paper_reachable_outgoing_equal[OF reachable])
  have membership: "(h \<in> paper_outgoing (paper_reachable_arrows Arrows paper_arrow_source paper_arrow_target M0)
      paper_arrow_source M) = (h \<in> paper_outgoing Arrows paper_arrow_source M)"
    by (simp only: equal)
  show ?thesis using membership by (simp only: paper_outgoing_member)
qed

end
