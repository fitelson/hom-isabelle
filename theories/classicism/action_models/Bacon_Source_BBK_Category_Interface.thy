theory Bacon_Source_BBK_Category_Interface
  imports Bacon_Source_BBK_Normalized_Category Bacon_Source_BBK_Subcategory
    Bacon_Source_BBK_Selected_Truth_Profile
begin

section \<open>Small BBK categories with canonical objects and selected arrows\<close>

text \<open>
  A represented BBK category has validated canonical model objects and
  a chosen identity-containing, composition-closed collection of normalized
  homomorphisms. Source: Bacon–Dorr §3.3, pp.49–50.

  Canonical records prevent irrelevant total-function extensions from
  distinguishing objects; normalized typed maps do the same for arrows.
  Neither operation identifies genuine denotations or changes truth.
  The selected collection need not contain every available homomorphism.
  This is a set-sized presentation, not the class of all BBK models.
\<close>

definition paper_bbk_canonical_subcategory ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data set \<Rightarrow>
    ('c,'v) paper_bbk_arrow set \<Rightarrow> bool" where
  "paper_bbk_canonical_subcategory \<Sigma> G Obj Arrows \<longleftrightarrow>
    paper_bbk_subcategory \<Sigma> G Obj Arrows \<and>
    (\<forall>M\<in>Obj. paper_bbk_data_canonical \<Sigma> G M)"

lemma paper_bbk_canonical_subcategory_raw:
  "paper_bbk_canonical_subcategory \<Sigma> G Obj Arrows \<Longrightarrow>
    paper_bbk_subcategory \<Sigma> G Obj Arrows"
  unfolding paper_bbk_canonical_subcategory_def by (rule conjunct1)

theorem paper_bbk_canonical_subcategory_category:
  assumes category: "paper_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
  shows "paper_category Obj Arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)"
  by (rule paper_bbk_subcategory_category[OF paper_bbk_canonical_subcategory_raw[OF category]])

theorem paper_bbk_canonical_subcategory_type_action:
  assumes category: "paper_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
  shows "paper_action Obj Arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)
    (\<lambda>M. paper_bbk_domain M \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)"
  by (rule paper_bbk_selected_type_action[OF paper_bbk_canonical_subcategory_raw[OF category]])

section \<open>Actual canonical categories obtained from supplied model sets\<close>

theorem paper_bbk_normalized_full_subcategory:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_bbk_data_valid \<Sigma> G M"
  shows "paper_bbk_canonical_subcategory \<Sigma> G
    (image (paper_bbk_normalize \<Sigma> G) Obj)
    (paper_bbk_arrows \<Sigma> G (image (paper_bbk_normalize \<Sigma> G) Obj))"
proof -
  let ?Obj = "image (paper_bbk_normalize \<Sigma> G) Obj"
  have valid: "paper_bbk_data_valid \<Sigma> G N" if "N \<in> ?Obj" for N
    by (rule conjunct1[OF paper_bbk_normalized_objects_valid[OF models that]])
  have canonical: "paper_bbk_data_canonical \<Sigma> G N" if "N \<in> ?Obj" for N
    by (rule conjunct2[OF paper_bbk_normalized_objects_valid[OF models that]])
  have subcategory: "paper_bbk_subcategory \<Sigma> G ?Obj (paper_bbk_arrows \<Sigma> G ?Obj)"
    by (rule paper_bbk_full_subcategory[OF valid])
  show ?thesis unfolding paper_bbk_canonical_subcategory_def
    by (rule conjI[OF subcategory], intro ballI, rule canonical, assumption)
qed

section \<open>Definition 3.10 truth profiles respect Example 3.15 transport\<close>

theorem paper_bbk_selected_truth_profile_naturality:
  assumes category: "paper_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
    and arrow: "f \<in> Arrows"
    and member: "p \<in> paper_bbk_domain (paper_arrow_source f) Prop"
  shows "paper_bbk_truth_profile_on Arrows (paper_arrow_target f) (paper_arrow_map f Prop p) =
    paper_powerset_transport Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) f
      (paper_bbk_truth_profile_on Arrows (paper_arrow_source f) p)"
  by (rule paper_bbk_truth_profile_on_naturality[
    OF paper_bbk_canonical_subcategory_category[OF category] arrow member])

text \<open>
  Thus the general selected-arrow profile has a genuine BBK-category use,
  rather than only an algebraic interpretation over an arbitrary category.
  Quasi-Fregeanness remains the additional injectivity condition of
  Definition 3.11; no existence or separation theorem is inferred here.
\<close>

end
