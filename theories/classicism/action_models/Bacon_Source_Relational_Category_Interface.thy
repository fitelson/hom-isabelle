theory Bacon_Source_Relational_Category_Interface
  imports Bacon_Source_Relational_Subcategory Bacon_Source_Relational_Normalization_Validity
begin

section \<open>Canonical R objects with chosen homomorphisms\<close>

text \<open>
  A small R BBK category consists of model objects and a chosen family
  of arrows containing identities and closed under composition.
  Source: Bacon–Dorr §3.3, pp.49–50, with the R grammar of p.5.

  Representation: objects satisfy the independent R validator and are
  fixed by R-input normalization. Their arrow maps are normalized on
  their source domains. Neither normalization changes genuine R values.
  No F canonical-model assumption is used. This is a common-carrier
  small presentation, not the proper class of all source models.
\<close>

definition paper_R_bbk_canonical_subcategory ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data set \<Rightarrow>
    ('c,'v) paper_R_bbk_arrow set \<Rightarrow> bool" where
  "paper_R_bbk_canonical_subcategory \<Sigma> G Obj Arrows \<longleftrightarrow>
    paper_R_bbk_subcategory \<Sigma> G Obj Arrows \<and>
    (\<forall>M\<in>Obj. paper_R_bbk_data_canonical \<Sigma> G M)"

lemma paper_R_bbk_canonical_subcategory_raw:
  "paper_R_bbk_canonical_subcategory \<Sigma> G Obj Arrows \<Longrightarrow>
    paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
  unfolding paper_R_bbk_canonical_subcategory_def by (rule conjunct1)

lemma paper_R_bbk_canonical_subcategory_object:
  assumes category: "paper_R_bbk_canonical_subcategory \<Sigma> G Obj Arrows" and member: "M \<in> Obj"
  shows "paper_R_bbk_data_valid \<Sigma> G M \<and> paper_R_bbk_data_canonical \<Sigma> G M"
  using category member
  unfolding paper_R_bbk_canonical_subcategory_def paper_R_bbk_subcategory_def by blast

theorem paper_R_bbk_canonical_subcategory_category:
  assumes category: "paper_R_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
  shows "paper_category Obj Arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)"
  by (rule paper_R_bbk_subcategory_category[OF paper_R_bbk_canonical_subcategory_raw[OF category]])

theorem paper_R_bbk_canonical_subcategory_type_action:
  assumes category: "paper_R_bbk_canonical_subcategory \<Sigma> G Obj Arrows"
  shows "paper_action Obj Arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)
    (\<lambda>M. paper_bbk_domain M \<sigma>) (\<lambda>h. paper_arrow_map h \<sigma>)"
  by (rule paper_R_bbk_selected_type_action[OF paper_R_bbk_canonical_subcategory_raw[OF category]])

section \<open>The full-hom special case on normalized supplied objects\<close>

lemma paper_R_bbk_normalized_objects_valid:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_R_bbk_data_valid \<Sigma> G M"
    and member: "N \<in> image (paper_R_bbk_normalize \<Sigma> G) Obj"
  shows "paper_R_bbk_data_valid \<Sigma> G N \<and> paper_R_bbk_data_canonical \<Sigma> G N"
proof -
  obtain M where original: "M \<in> Obj" and shape: "N = paper_R_bbk_normalize \<Sigma> G M"
    using member by blast
  have valid: "paper_R_bbk_data_valid \<Sigma> G (paper_R_bbk_normalize \<Sigma> G M)"
    by (rule paper_R_bbk_normalize_valid[OF models[OF original]])
  show ?thesis by (simp only: shape; rule conjI[OF valid paper_R_bbk_normalize_canonical])
qed

theorem paper_R_bbk_normalized_full_subcategory:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_R_bbk_data_valid \<Sigma> G M"
  shows "paper_R_bbk_canonical_subcategory \<Sigma> G
    (image (paper_R_bbk_normalize \<Sigma> G) Obj)
    (paper_R_bbk_arrows \<Sigma> G (image (paper_R_bbk_normalize \<Sigma> G) Obj))"
proof -
  let ?Obj = "image (paper_R_bbk_normalize \<Sigma> G) Obj"
  have valid: "paper_R_bbk_data_valid \<Sigma> G N" if "N \<in> ?Obj" for N
    by (rule conjunct1[OF paper_R_bbk_normalized_objects_valid[OF models that]])
  have canonical: "paper_R_bbk_data_canonical \<Sigma> G N" if "N \<in> ?Obj" for N
    by (rule conjunct2[OF paper_R_bbk_normalized_objects_valid[OF models that]])
  have selected: "paper_R_bbk_subcategory \<Sigma> G ?Obj (paper_R_bbk_arrows \<Sigma> G ?Obj)"
    by (rule paper_R_bbk_full_subcategory[OF valid])
  show ?thesis unfolding paper_R_bbk_canonical_subcategory_def
    by (rule conjI[OF selected], intro ballI, rule canonical, assumption)
qed

text \<open>
  The last construction uses every R homomorphism between its new objects.
  It does not transport a pre-existing selected arrow family through object
  normalization. Nor does it prove quasi-Fregeanness, intensionality,
  representation of every R model on this carrier, or Classicism validity.
\<close>

end
