theory Bacon_Source_Relational_Signature_Compression_Syntax
  imports Bacon_Source_Relational_Typed_Constant_Map "HOL-Library.Countable_Set"
begin

section \<open>The finitely many bare constant names of a formula\<close>

abbreviation paper_R_constant_names :: "('c,'l) named_term \<Rightarrow> 'c set" where
  "paper_R_constant_names A \<equiv> named_term.set1_named_term A"

lemma paper_R_constant_names_finite:
  "finite (paper_R_constant_names A)"
  by (induction A) simp_all

lemma paper_R_constant_names_signature_iff:
  "named_in_signature (\<lambda>_. K) A \<longleftrightarrow> paper_R_constant_names A \<subseteq> K"
  by (induction A) auto

section \<open>Retain K and collapse all other names to one dummy\<close>

definition paper_R_compress_name :: "'c set \<Rightarrow> 'c \<Rightarrow> 'c + unit" where
  "paper_R_compress_name K c = (if c \<in> K then Inl c else Inr ())"

definition paper_R_compressed_signature :: "'c ssignature \<Rightarrow> 'c set \<Rightarrow> ('c + unit) ssignature" where
  "paper_R_compressed_signature \<Sigma> K \<sigma> = paper_R_compress_name K ` \<Sigma> \<sigma>"

lemma paper_R_compress_name_retained:
  "c \<in> K \<Longrightarrow> paper_R_compress_name K c = Inl c"
  by (simp add: paper_R_compress_name_def)

lemma paper_R_compress_name_discarded:
  "c \<notin> K \<Longrightarrow> paper_R_compress_name K c = Inr ()"
  by (simp add: paper_R_compress_name_def)

lemma paper_R_compressed_signature_maps:
  "c \<in> \<Sigma> \<sigma> \<Longrightarrow> paper_R_compress_name K c \<in> paper_R_compressed_signature \<Sigma> K \<sigma>"
  unfolding paper_R_compressed_signature_def by (rule imageI)

lemma paper_R_compressed_signature_exact:
  "paper_R_compressed_signature \<Sigma> K \<sigma> = Inl ` (\<Sigma> \<sigma> \<inter> K) \<union>
    (if \<Sigma> \<sigma> - K = {} then {} else {Inr ()})"
  by (auto simp: paper_R_compressed_signature_def paper_R_compress_name_def split: if_splits)

lemma paper_R_compressed_signature_retained_iff:
  "Inl c \<in> paper_R_compressed_signature \<Sigma> K \<sigma> \<longleftrightarrow> c \<in> \<Sigma> \<sigma> \<and> c \<in> K"
  by (auto simp: paper_R_compressed_signature_exact split: if_splits)

lemma paper_R_compressed_signature_dummy_iff:
  "Inr () \<in> paper_R_compressed_signature \<Sigma> K \<sigma> \<longleftrightarrow> \<Sigma> \<sigma> - K \<noteq> {}"
  by (auto simp: paper_R_compressed_signature_exact split: if_splits)

lemma paper_R_compressed_signature_union_bound:
  "(\<Union>\<sigma>. paper_R_compressed_signature \<Sigma> K \<sigma>) \<subseteq> Inl ` K \<union> {Inr ()}"
  by (auto simp: paper_R_compressed_signature_def paper_R_compress_name_def split: if_splits)

theorem paper_R_compressed_signature_finite:
  assumes finite: "finite K"
  shows "finite (\<Union>\<sigma>. paper_R_compressed_signature \<Sigma> K \<sigma>)"
proof -
  have bound_finite: "finite (Inl ` K \<union> {Inr ()})" using finite by simp
  show ?thesis by (rule finite_subset[OF paper_R_compressed_signature_union_bound bound_finite])
qed

corollary paper_R_compressed_signature_countable:
  assumes finite: "finite K"
  shows "countable (\<Union>\<sigma>. paper_R_compressed_signature \<Sigma> K \<sigma>)"
  by (rule countable_finite[OF paper_R_compressed_signature_finite[OF finite]])

lemma paper_R_compression_language:
  assumes language: "paper_R_in_language \<Sigma> G A \<tau>"
  shows "paper_R_in_language (paper_R_compressed_signature \<Sigma> K) G (paper_R_constant_map (paper_R_compress_name K) A) \<tau>"
  by (rule paper_R_constant_map_language[OF language]; rule paper_R_compressed_signature_maps; assumption)

text \<open>
  The support is the named datatype's existing set1 selector, not a
  second recursive syntax. A finite K bounds the union of ALL declared
  compressed names even if the ambient original carrier is uncountable.
  Occurrence types remain unchanged. The dummy is declared at σ exactly
  when some discarded original name was declared at σ.

  This is finite-formula vocabulary compression only. It makes no claim
  to compress an arbitrary infinite theory or its models.
\<close>

end
