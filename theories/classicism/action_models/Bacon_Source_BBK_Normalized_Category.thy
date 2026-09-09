theory Bacon_Source_BBK_Normalized_Category
  imports Bacon_Source_BBK_Normalization_Validity Bacon_Source_BBK_Category
begin

section \<open>Canonical records identify exactly the meaningful model data\<close>

text \<open>
  A canonical record is fixed by normalization. Two canonical records
  with the same domains and the same source-defined interpretation and
  valuation are literally equal. Source role: faithful object identity
  for the model categories of Bacon–Dorr §3.3, pp.49–50.
  This removes irrelevant total-function extensions, not any semantic
  distinctions between propositions or higher-type objects.
\<close>

definition paper_bbk_data_canonical ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data \<Rightarrow> bool" where
  "paper_bbk_data_canonical \<Sigma> G M \<longleftrightarrow> paper_bbk_normalize \<Sigma> G M = M"

lemma paper_bbk_normalize_canonical:
  "paper_bbk_data_canonical \<Sigma> G (paper_bbk_normalize \<Sigma> G M)"
  by (simp only: paper_bbk_data_canonical_def paper_bbk_normalize_idempotent)

theorem paper_bbk_canonical_data_ext:
  assumes first: "paper_bbk_data_canonical \<Sigma> G M"
    and second: "paper_bbk_data_canonical \<Sigma> G N"
    and domains: "paper_bbk_domain M = paper_bbk_domain N"
    and denotations: "\<And>g A. paper_bbk_input \<Sigma> G (paper_bbk_domain M) g A \<Longrightarrow>
      paper_bbk_denote M g A = paper_bbk_denote N g A"
    and valuations: "\<And>a. a \<in> paper_bbk_domain M Prop \<Longrightarrow>
      paper_bbk_valuation M a = paper_bbk_valuation N a"
  shows "M = N"
proof -
  have normalized: "paper_bbk_normalize \<Sigma> G M = paper_bbk_normalize \<Sigma> G N"
    by (rule paper_bbk_normalize_cong[OF domains denotations valuations])
  show ?thesis using normalized first second unfolding paper_bbk_data_canonical_def by simp
qed

section \<open>A category of canonical BBK model records\<close>

theorem paper_bbk_normalized_objects_valid:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_bbk_data_valid \<Sigma> G M"
    and member: "N \<in> image (paper_bbk_normalize \<Sigma> G) Obj"
  shows "paper_bbk_data_valid \<Sigma> G N \<and> paper_bbk_data_canonical \<Sigma> G N"
proof -
  obtain M where original: "M \<in> Obj" and shape: "N = paper_bbk_normalize \<Sigma> G M"
    using member by blast
  have valid: "paper_bbk_data_valid \<Sigma> G (paper_bbk_normalize \<Sigma> G M)"
    by (rule paper_bbk_normalize_valid[OF models[OF original]])
  show ?thesis by (simp only: shape; rule conjI[OF valid paper_bbk_normalize_canonical])
qed

theorem paper_bbk_normalized_category:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_bbk_data_valid \<Sigma> G M"
  shows "paper_category (image (paper_bbk_normalize \<Sigma> G) Obj)
    (paper_bbk_arrows \<Sigma> G (image (paper_bbk_normalize \<Sigma> G) Obj))
    paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)"
proof (rule paper_bbk_record_category)
  fix N
  assume member: "N \<in> image (paper_bbk_normalize \<Sigma> G) Obj"
  show "paper_bbk_data_valid \<Sigma> G N"
    by (rule conjunct1[OF paper_bbk_normalized_objects_valid[OF models member]])
qed

text \<open>
  This is an actual small category built from every supplied set of valid
  model records on the common carrier. Normalization preserves all BBK
  clauses and all meaningful truth values; the objects have canonical
  field extensions, and arrows have canonical map extensions.
  It does not assert that the proper class of all models fits this carrier,
  nor that the resulting category is intensional or validates Classicism.
\<close>

end
