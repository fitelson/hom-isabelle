theory Bacon_Source_Relational_Signature_Compression_Section
  imports Bacon_Source_Relational_Signature_Compression_Syntax
begin

section \<open>A type-indexed section on declared compressed names\<close>

fun paper_R_compression_section :: "'c ssignature \<Rightarrow> 'c set \<Rightarrow> otype \<Rightarrow> 'c + unit \<Rightarrow> 'c" where
  "paper_R_compression_section \<Sigma> K \<sigma> (Inl c) = c"
| "paper_R_compression_section \<Sigma> K \<sigma> (Inr u) = (SOME c. c \<in> \<Sigma> \<sigma> - K)"

lemma paper_R_compression_dummy_choice:
  assumes inhabited: "\<Sigma> \<sigma> - K \<noteq> {}"
  shows "(SOME c. c \<in> \<Sigma> \<sigma> - K) \<in> \<Sigma> \<sigma> - K"
  by (rule someI_ex; use inhabited in blast)

theorem paper_R_compression_section_spec:
  assumes declared: "d \<in> paper_R_compressed_signature \<Sigma> K \<sigma>"
  shows "paper_R_compression_section \<Sigma> K \<sigma> d \<in> \<Sigma> \<sigma> \<and>
    paper_R_compress_name K (paper_R_compression_section \<Sigma> K \<sigma> d) = d"
proof (cases d)
  case (Inl c)
  have original: "c \<in> \<Sigma> \<sigma>" and retained: "c \<in> K"
    using declared by (simp_all add: Inl paper_R_compressed_signature_retained_iff)
  show ?thesis by (simp add: Inl original retained paper_R_compress_name_def)
next
  case (Inr u)
  have inhabited: "\<Sigma> \<sigma> - K \<noteq> {}"
    using declared by (cases u) (simp add: Inr paper_R_compressed_signature_dummy_iff)
  have chosen: "(SOME c. c \<in> \<Sigma> \<sigma> - K) \<in> \<Sigma> \<sigma> - K"
    by (rule paper_R_compression_dummy_choice[where \<Sigma>=\<Sigma> and \<sigma>=\<sigma> and K=K, OF inhabited])
  show ?thesis using chosen by (cases u) (auto simp: Inr paper_R_compress_name_def)
qed

corollary paper_R_compression_section_maps:
  assumes declared: "d \<in> paper_R_compressed_signature \<Sigma> K \<sigma>"
  shows "paper_R_compression_section \<Sigma> K \<sigma> d \<in> \<Sigma> \<sigma>"
  by (rule conjunct1[OF paper_R_compression_section_spec[OF declared]])

corollary paper_R_compression_section_retract:
  assumes declared: "d \<in> paper_R_compressed_signature \<Sigma> K \<sigma>"
  shows "paper_R_compress_name K (paper_R_compression_section \<Sigma> K \<sigma> d) = d"
  by (rule conjunct2[OF paper_R_compression_section_spec[OF declared]])

lemma paper_R_compression_section_retained:
  assumes retained: "c \<in> K"
  shows "paper_R_compression_section \<Sigma> K \<sigma> (paper_R_compress_name K c) = c"
  by (simp only: paper_R_compress_name_retained[OF retained] paper_R_compression_section.simps)

theorem paper_R_compression_formula_roundtrip:
  assumes support: "paper_R_constant_names A \<subseteq> K"
  shows "paper_R_typed_constant_map (paper_R_compression_section \<Sigma> K)
    (paper_R_constant_map (paper_R_compress_name K) A) = A"
  using support by (induction A) (auto simp: paper_R_compress_name_def)

corollary paper_R_compression_at_formula_names:
  "paper_R_typed_constant_map (paper_R_compression_section \<Sigma> (paper_R_constant_names A))
    (paper_R_constant_map (paper_R_compress_name (paper_R_constant_names A)) A) = A"
  by (rule paper_R_compression_formula_roundtrip[OF subset_refl])

lemma paper_R_compression_section_language:
  assumes language: "paper_R_in_language (paper_R_compressed_signature \<Sigma> K) G B \<tau>"
  shows "paper_R_in_language \<Sigma> G (paper_R_typed_constant_map (paper_R_compression_section \<Sigma> K) B) \<tau>"
  by (rule paper_R_typed_constant_map_language[OF language]; rule paper_R_compression_section_maps; assumption)

text \<open>
  The dummy's preimage is chosen separately at each occurrence type.
  No one original constant need be declared at every dummy-bearing
  type. Choice is constrained only when that type declares the dummy;
  the corresponding difference Σσ−K is then proved nonempty.

  The formula roundtrip needs only coverage of that formula's names,
  not finiteness, language membership, or global injectivity. Finiteness
  is used separately for the compressed signature's size. No proof or
  semantic transport result is assumed in these syntax equations.
\<close>

end
