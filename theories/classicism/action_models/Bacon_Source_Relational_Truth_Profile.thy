theory Bacon_Source_Relational_Truth_Profile
  imports Bacon_Source_Relational_Category_Interface
    Bacon_Source_BBK_Selected_Truth_Profile Bacon_Source_Image_Action
begin

section \<open>Truth profiles of selected R categories\<close>

text \<open>
  val𝒞M(p)={h:M→N in 𝒞 | VN(hₜ(p))}. For f:M→N,
  val𝒞N(fₜ(p))=fᴾ(val𝒞M(p)). Source: Definition 3.10, p.50,
  and Example 3.15, p.54. The selected arrows here have independent
  R-model endpoints, not F-model endpoints.

  Representation: paper_bbk_truth_profile_on is reused as a raw set
  expression over record fields. Despite its historical filename, its
  naturality theorem assumes only a generic category with the displayed
  normalized composition and a typed p. It uses no F validator, term
  grammar, denotation clause, or truth-preservation condition on arrows.
  Status: R profile naturality and the image subaction, not separation
  or identification of propositions with their profiles.
\<close>

theorem paper_R_bbk_selected_truth_profile_naturality:
  assumes category: "paper_R_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
    and arrow: "f \<in> Arrows"
    and member: "p \<in> paper_bbk_domain (paper_arrow_source f) Prop"
  shows "paper_bbk_truth_profile_on Arrows (paper_arrow_target f) (paper_arrow_map f Prop p) =
    paper_powerset_transport Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) f
      (paper_bbk_truth_profile_on Arrows (paper_arrow_source f) p)"
  by (rule paper_bbk_truth_profile_on_naturality[
    OF paper_R_bbk_canonical_subcategory_category[OF category] arrow member])

theorem paper_R_bbk_truth_profile_action_map:
  assumes category: "paper_R_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
  shows "paper_action_map Obj Arrows paper_arrow_source paper_arrow_target
    (\<lambda>M. paper_bbk_domain M Prop) (\<lambda>h. paper_arrow_map h Prop)
    (paper_powerset_fiber Arrows paper_arrow_source)
    (paper_powerset_transport Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain))
    (paper_bbk_truth_profile_on Arrows)"
proof (rule paper_action_mapI)
  fix M p
  assume object: "M \<in> Obj" and member: "p \<in> paper_bbk_domain M Prop"
  show "paper_bbk_truth_profile_on Arrows M p \<in> paper_powerset_fiber Arrows paper_arrow_source M"
    by (rule paper_bbk_truth_profile_on_fiber)
next
  fix h p
  assume arrow: "h \<in> Arrows" and member: "p \<in> paper_bbk_domain (paper_arrow_source h) Prop"
  show "paper_bbk_truth_profile_on Arrows (paper_arrow_target h) (paper_arrow_map h Prop p) =
    paper_powerset_transport Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain)
      h (paper_bbk_truth_profile_on Arrows (paper_arrow_source h) p)"
    by (rule paper_R_bbk_selected_truth_profile_naturality[OF category arrow member])
qed

theorem paper_R_bbk_truth_profile_subaction:
  assumes category: "paper_R_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
  shows "paper_subaction Obj Arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)
    (paper_action_image (paper_bbk_truth_profile_on Arrows) (\<lambda>M. paper_bbk_domain M Prop))
    (paper_powerset_transport Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain))
    (paper_powerset_fiber Arrows paper_arrow_source)
    (paper_powerset_transport Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain))"
proof -
  interpret Category: paper_category Obj Arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_R_bbk_canonical_subcategory_category[OF category])
  show ?thesis
    by (rule paper_action_image_subaction[
      OF paper_R_bbk_canonical_subcategory_type_action[where \<sigma>=Prop, OF category]
        Category.paper_powerset_action paper_R_bbk_truth_profile_action_map[OF category]])
qed

end
