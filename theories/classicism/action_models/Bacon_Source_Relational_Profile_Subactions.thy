theory Bacon_Source_Relational_Profile_Subactions
  imports Bacon_Source_Relational_Application_Profile_Action Bacon_Source_Image_Action
begin

section \<open>The images of applicative profiles form an exponential subaction\<close>

text \<open>
  For σ→τ∈R, app𝒞M sends Mσ→τ into the exponential fiber (−σ⇒−τ)M
  and commutes with each arrow. Its image is a subaction of that
  exponential action (p.55, following Example 3.16). The source and
  target action carriers differ: old values versus pair-functions.
  We claim a subaction of the profile images, not an isomorphism of
  the original function-domain action without quasi-functionality.
  Both endpoints are independent R actions. No F model validator or F
  application/profile theorem is used; no injectivity is assumed.
\<close>

theorem paper_R_app_profile_action_map:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and rt: "paper_R_type (Arr \<sigma> \<tau>)"
  shows "paper_action_map Obj Arrows paper_arrow_source paper_arrow_target
    (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>)) (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>))
    (paper_exponential_fiber Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain)
      (\<lambda>M. paper_bbk_domain M \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)
      (\<lambda>M. paper_bbk_domain M \<tau>) (\<lambda>h. paper_arrow_map h \<tau>))
    (paper_exponential_transport Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (\<lambda>M. paper_bbk_domain M \<sigma>))
    (\<lambda>M. paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau>)"
proof (rule paper_action_mapI)
  fix M d
  assume object: "M \<in> Obj" and member: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
  show "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d \<in>
    paper_exponential_fiber Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain)
      (\<lambda>M. paper_bbk_domain M \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)
      (\<lambda>M. paper_bbk_domain M \<tau>) (\<lambda>h. paper_arrow_map h \<tau>) M"
    by (rule paper_R_app_profile_on_exponential[OF category rt member])
next
  fix h d
  assume arrow: "h \<in> Arrows" and member: "d \<in> paper_bbk_domain (paper_arrow_source h) (Arr \<sigma> \<tau>)"
  show "paper_R_app_profile_on \<Sigma> G Arrows (paper_arrow_target h) \<sigma> \<tau>
      (paper_arrow_map h (Arr \<sigma> \<tau>) d) =
    paper_exponential_transport Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain)
      (\<lambda>M. paper_bbk_domain M \<sigma>) h
      (paper_R_app_profile_on \<Sigma> G Arrows (paper_arrow_source h) \<sigma> \<tau> d)"
    by (rule paper_R_app_profile_on_naturality[OF category rt arrow member])
qed

theorem paper_R_app_profile_subaction:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and rt: "paper_R_type (Arr \<sigma> \<tau>)"
  shows "paper_subaction Obj Arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)
    (paper_action_image (\<lambda>M. paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau>)
      (\<lambda>M. paper_bbk_domain M (Arr \<sigma> \<tau>)))
    (paper_exponential_transport Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (\<lambda>M. paper_bbk_domain M \<sigma>))
    (paper_exponential_fiber Arrows paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain)
      (\<lambda>M. paper_bbk_domain M \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)
      (\<lambda>M. paper_bbk_domain M \<tau>) (\<lambda>h. paper_arrow_map h \<tau>))
    (paper_exponential_transport Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (\<lambda>M. paper_bbk_domain M \<sigma>))"
  by (rule paper_action_image_subaction[
    OF paper_R_bbk_selected_type_action[where \<sigma>="Arr \<sigma> \<tau>", OF category]
      paper_R_profile_exponential_action[where \<sigma>=\<sigma> and \<tau>=\<tau>, OF category rt]
      paper_R_app_profile_action_map[OF category rt]])

end
