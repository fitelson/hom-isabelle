theory Goodman_Expansion_Language
  imports Goodman_Named_Root_Conversion
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Decoder_Conversion
begin

section \<open>The expansion belongs to the declared finite-context language\<close>

lemma gi_chart_encoding_lookup:
  assumes distinct: "distinct ns" and member: "n \<in> set ns"
  shows "lookup (map G ns) (named_index ns n) =
    Some (named_stack_stock G ns (named_index ns n))"
proof -
  obtain i where bound: "i < length ns" and at_i: "ns ! i = n"
    using member by (auto simp: in_set_conv_nth)
  have index: "named_index ns n = i"
    using named_index_nth_distinct[OF distinct bound] by (simp only: at_i)
  have looked: "lookup (map G ns) (named_index ns n) = Some (G n)"
    by (simp add: lookup_def index bound at_i)
  show ?thesis using looked by (simp only: named_stack_index_type)
qed

lemma gi_chart_encoding_type:
  assumes typed: "has_ntype L G A \<tau>"
    and support: "named_fv A \<subseteq> set ns" and distinct: "distinct ns"
  shows "has_stype L (map G ns) (named_to_source G ns A) \<tau>"
proof -
  have global: "has_sgtype L (named_stack_stock G ns) (named_to_source G ns A) \<tau>"
    by (rule named_to_source_global_type[OF typed])
  show ?thesis
  proof (rule source_global_to_finite_typing[OF global])
    fix i
    assume free: "i \<in> sfv (named_to_source G ns A)"
    obtain n where free_n: "n \<in> named_fv A" and index: "i = named_index ns n"
      using free by (auto simp: named_to_source_fv)
    have member: "n \<in> set ns" by (rule subsetD[OF support free_n])
    show "lookup (map G ns) i = Some (named_stack_stock G ns i)"
      unfolding index by (rule gi_chart_encoding_lookup[OF distinct member])
  qed
qed

theorem gi_expand_language:
  assumes rich: "sg_rich G" and typed: "\<Gamma> \<turnstile> A : \<tau>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and constants: "gi_constants_admitted k \<Sigma> A"
  shows "sterm_in_language book_minimal_logical_type \<Sigma> \<Gamma> (gi_expand G k A) \<tau>"
proof -
  let ?N = "gi_to_book G ns k A"
  have language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?N \<tau>"
    by (rule gi_to_book_language[OF rich typed chart constants])
  have support: "named_fv ?N \<subseteq> set ns" by (rule gi_to_book_fv_subset[OF rich typed chart])
  have finite_type: "has_stype book_minimal_logical_type (map G ns) (named_to_source G ns ?N) \<tau>"
    by (rule gi_chart_encoding_type[OF book_language_type[OF language] support distinct])
  have signature: "sterm_in_signature \<Sigma> (named_to_source G ns ?N)"
    by (simp only: named_to_source_signature; rule book_language_signature[OF language])
  have encoded: "named_to_source G ns ?N = gi_expand G k A"
    by (rule gi_to_book_relative_encoding[OF rich typed chart distinct])
  show ?thesis unfolding sterm_in_language_def
    using finite_type signature by (simp only: chart encoded)
qed

theorem gi_decoder_alignment:
  assumes rich: "sg_rich G" and typed: "\<Gamma> \<turnstile> A : \<tau>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and expanded: "has_stype book_minimal_logical_type \<Gamma> (gi_expand G k A) \<tau>"
  shows "named_alpha G (source_to_named G ns (gi_expand G k A)) (gi_to_book G ns k A)"
proof -
  have nc: "named_chart G \<Gamma> ns" by (rule gi_chart_is_named_chart[OF distinct chart])
  have first: "named_to_source G [] (source_to_named G ns (gi_expand G k A)) =
    srename (\<lambda>i. ns ! i) (gi_expand G k A)"
    by (rule source_to_named_empty_encoding[OF expanded nc rich])
  have second: "named_to_source G [] (gi_to_book G ns k A) =
    srename (\<lambda>i. ns ! i) (gi_expand G k A)"
    by (rule gi_to_book_empty_encoding[OF rich typed chart distinct])
  show ?thesis by (rule named_encoding_implies_alpha[OF rich]; simp only: first second)
qed

text \<open>
  The core decoder is now connected to our existing named translation
  by a proved α alignment. Language membership is derived, not assumed
  merely because the raw expansion has the intended shape.
\<close>

end
