theory Bacon_Source_BBK_Profile_Subactions
  imports Bacon_Source_BBK_Application_Profile_Action Bacon_Source_Image_Action
begin

section \<open>The images of truth profiles form a powerset subaction\<close>

text \<open>
  Each truth profile lies in Mᴾ and commutes with transport. Its image
  therefore forms a subaction of the powerset action. Source: the paragraph
  preceding Definition 3.17, p.55, following Example 3.15.
  No injectivity is assumed: the original propositions are not thereby
  identified with their profiles.
\<close>

theorem paper_bbk_truth_profile_action_map:
  assumes category: "paper_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
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
    by (rule paper_bbk_selected_truth_profile_naturality[OF category arrow member])
qed

theorem paper_bbk_truth_profile_subaction:
  assumes category: "paper_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
  shows "paper_subaction Obj Arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)
    (paper_action_image (paper_bbk_truth_profile_on Arrows) (\<lambda>M. paper_bbk_domain M Prop))
    (paper_powerset_transport Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain))
    (paper_powerset_fiber Arrows paper_arrow_source)
    (paper_powerset_transport Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain))"
proof -
  interpret Category: paper_category Obj Arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_bbk_canonical_subcategory_category[OF category])
  show ?thesis
    by (rule paper_action_image_subaction[
      OF paper_bbk_canonical_subcategory_type_action[where \<sigma>=Prop, OF category]
        Category.paper_powerset_action paper_bbk_truth_profile_action_map[OF category]])
qed

section \<open>The images of applicative profiles form an exponential subaction\<close>

text \<open>
  app𝒞M sends Mσ→τ into the exponential fiber (−σ⇒−τ)M
  and commutes with each arrow. Its image is a subaction of that
  exponential action (p.55, following Example 3.16). The source and
  target action carriers differ: old values versus pair-functions.
  We claim a subaction of the profile images, not an isomorphism of
  the original function-domain action without quasi-functionality.
\<close>

theorem paper_bbk_app_profile_action_map:
  assumes category: "paper_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
  shows "paper_action_map Obj Arrows paper_arrow_source paper_arrow_target
    (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>)) (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>))
    (paper_exponential_fiber Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain)
      (\<lambda>M. paper_bbk_domain M \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)
      (\<lambda>M. paper_bbk_domain M \<tau>) (\<lambda>h. paper_arrow_map h \<tau>))
    (paper_exponential_transport Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (\<lambda>M. paper_bbk_domain M \<sigma>))
    (\<lambda>M. paper_bbk_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau>)"
proof (rule paper_action_mapI)
  fix M d
  assume object: "M \<in> Obj" and member: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
  show "paper_bbk_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d \<in>
    paper_exponential_fiber Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain)
      (\<lambda>M. paper_bbk_domain M \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)
      (\<lambda>M. paper_bbk_domain M \<tau>) (\<lambda>h. paper_arrow_map h \<tau>) M"
    by (rule paper_bbk_app_profile_on_exponential[OF category member])
next
  fix h d
  assume arrow: "h \<in> Arrows" and member: "d \<in> paper_bbk_domain (paper_arrow_source h) (Arr \<sigma> \<tau>)"
  show "paper_bbk_app_profile_on \<Sigma> G Arrows (paper_arrow_target h) \<sigma> \<tau>
      (paper_arrow_map h (Arr \<sigma> \<tau>) d) =
    paper_exponential_transport Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain)
      (\<lambda>M. paper_bbk_domain M \<sigma>) h
      (paper_bbk_app_profile_on \<Sigma> G Arrows (paper_arrow_source h) \<sigma> \<tau> d)"
    by (rule paper_bbk_app_profile_on_naturality[OF category arrow member])
qed

theorem paper_bbk_app_profile_subaction:
  assumes category: "paper_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
  shows "paper_subaction Obj Arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)
    (paper_action_image (\<lambda>M. paper_bbk_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau>)
      (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>)))
    (paper_exponential_transport Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (\<lambda>M. paper_bbk_domain M \<sigma>))
    (paper_exponential_fiber Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain)
      (\<lambda>M. paper_bbk_domain M \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)
      (\<lambda>M. paper_bbk_domain M \<tau>) (\<lambda>h. paper_arrow_map h \<tau>))
    (paper_exponential_transport Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (\<lambda>M. paper_bbk_domain M \<sigma>))"
  by (rule paper_action_image_subaction[
    OF paper_bbk_canonical_subcategory_type_action[where \<sigma>="Arr \<sigma> \<tau>", OF category]
      paper_bbk_profile_exponential_action[where \<sigma>=\<sigma> and \<tau>=\<tau>, OF category]
      paper_bbk_app_profile_action_map[OF category]])

end
