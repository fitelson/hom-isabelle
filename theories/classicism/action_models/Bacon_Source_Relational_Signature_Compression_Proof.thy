theory Bacon_Source_Relational_Signature_Compression_Proof
  imports Bacon_Source_Relational_Signature_Compression_Section
    Bacon_Source_Relational_Classicism_Typed_Constant_Map
begin

section \<open>Reflection for the single formula whose names are retained\<close>

theorem paper_R_compression_C_reflects:
  assumes support: "paper_R_constant_names A \<subseteq> K"
    and derivation: "paper_R_classicism_proves (paper_R_compressed_signature \<Sigma> K) G
      (paper_R_constant_map (paper_R_compress_name K) A)"
  shows "paper_R_classicism_proves \<Sigma> G A"
proof -
  have reflected: "paper_R_classicism_proves \<Sigma> G
      (paper_R_typed_constant_map (paper_R_compression_section \<Sigma> K)
        (paper_R_constant_map (paper_R_compress_name K) A))"
    by (rule paper_R_classicism_typed_constant_map[OF derivation]; rule paper_R_compression_section_maps; assumption)
  show ?thesis using reflected by (simp only: paper_R_compression_formula_roundtrip[OF support])
qed

theorem paper_R_compression_C_forward:
  assumes derivation: "paper_R_classicism_proves \<Sigma> G A"
  shows "paper_R_classicism_proves (paper_R_compressed_signature \<Sigma> K) G
    (paper_R_constant_map (paper_R_compress_name K) A)"
proof -
  have mapped: "paper_R_classicism_proves (paper_R_compressed_signature \<Sigma> K) G
      (paper_R_typed_constant_map (\<lambda>_. paper_R_compress_name K) A)"
    by (rule paper_R_classicism_typed_constant_map[OF derivation]; rule paper_R_compressed_signature_maps; assumption)
  show ?thesis using mapped by (simp only: paper_R_typed_constant_map_uniform)
qed

corollary paper_R_compression_C_iff:
  assumes support: "paper_R_constant_names A \<subseteq> K"
  shows "paper_R_classicism_proves (paper_R_compressed_signature \<Sigma> K) G
    (paper_R_constant_map (paper_R_compress_name K) A) \<longleftrightarrow> paper_R_classicism_proves \<Sigma> G A"
  using paper_R_compression_C_reflects[OF support] paper_R_compression_C_forward by blast

corollary paper_R_compression_non_theorem:
  assumes missing: "\<not> paper_R_classicism_proves \<Sigma> G A" and support: "paper_R_constant_names A \<subseteq> K"
  shows "\<not> paper_R_classicism_proves (paper_R_compressed_signature \<Sigma> K) G
    (paper_R_constant_map (paper_R_compress_name K) A)"
  using paper_R_compression_C_reflects[OF support] missing by blast

theorem paper_R_finite_formula_compression:
  assumes language: "paper_R_in_language \<Sigma> G A Prop" and missing: "\<not> paper_R_classicism_proves \<Sigma> G A"
  shows "finite (\<Union>\<sigma>. paper_R_compressed_signature \<Sigma> (paper_R_constant_names A) \<sigma>) \<and>
    paper_R_in_language (paper_R_compressed_signature \<Sigma> (paper_R_constant_names A)) G
      (paper_R_constant_map (paper_R_compress_name (paper_R_constant_names A)) A) Prop \<and>
    \<not> paper_R_classicism_proves (paper_R_compressed_signature \<Sigma> (paper_R_constant_names A)) G
      (paper_R_constant_map (paper_R_compress_name (paper_R_constant_names A)) A)"
  by (rule conjI[OF paper_R_compressed_signature_finite[OF paper_R_constant_names_finite]],
    rule conjI[OF paper_R_compression_language[OF language] paper_R_compression_non_theorem[OF missing subset_refl]])

text \<open>
  Proof reflection uses the declared-name section, followed by the exact
  roundtrip on A. This is not reflection for an arbitrary formula under
  a noninjective constant map. No richness, model, countability of the
  ambient name carrier, or compression of an infinite premise theory is
  assumed. The finite-size conclusion concerns the selected formula's
  compressed signature and leaves its native C non-theoremhood intact.
\<close>

end
