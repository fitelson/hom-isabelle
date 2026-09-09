theory Bacon_Source_Named_Prefix_Roundtrip
  imports Bacon_Source_Named_Closed_Roundtrip Bacon_Source_Prefix_Preservation
begin

section \<open>Identity charts for prefixes supporting an open named term\<close>

text \<open>
  Use names [0,…,m−1] to chart the corresponding prefix of G. If that
  prefix covers the free slots of enc(A), decoding enc(A) and encoding
  again gives enc(A) exactly. The decoded named term is therefore an
  α-variant of A when G is rich.
  Source role: named-variable typing and binding in Bacon–Dorr §1.1,
  p.5, and adequate free-variable support in Definition 3.1, pp.43–44.

  Isabelle representation. The prefix bound applies to the source encoding.
  Its exact FV equation identifies those slots with the free names of A.
  The nth-prefix map is the identity only on this supported set; no claim
  is made about its out-of-range values. The named terms themselves need
  not be equal, because decoding may choose different bound names.
  This is syntax only: no assignment, denotation, or H proof is used.
\<close>

lemma named_identity_prefix_chart:
  "named_chart G (source_prefix G m) [0..<m]"
  by (simp add: named_chart_def source_prefix_def list_all2_conv_all_nth)

theorem named_encoding_prefix_language:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
    and bound: "source_free_bound (named_to_source G [] A) \<le> m"
  shows "sterm_in_language L \<Sigma> (source_prefix G m) (named_to_source G [] A) \<tau>"
proof -
  have global: "sgterm_in_language L \<Sigma> G (named_to_source G [] A) \<tau>"
    using named_to_source_global_language[where ns="[]", OF language]
    by (simp only: named_stack_stock.simps)
  show ?thesis by (rule source_language_in_prefix[OF global bound])
qed

lemma named_prefix_free_name:
  assumes bound: "source_free_bound (named_to_source G [] A) \<le> m"
    and free: "n \<in> named_fv A"
  shows "n < m"
proof -
  have source_free: "n \<in> sfv (named_to_source G [] A)"
    by (simp only: named_to_source_empty_fv; rule free)
  have before_bound: "n < source_free_bound (named_to_source G [] A)"
    by (rule source_free_bound_covers[OF source_free])
  show ?thesis by (rule less_le_trans[OF before_bound bound])
qed

theorem named_prefix_roundtrip_encoding:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
    and bound: "source_free_bound (named_to_source G [] A) \<le> m"
    and rich: "sg_rich G"
  shows "named_to_source G [] (source_to_named G [0..<m] (named_to_source G [] A)) = named_to_source G [] A"
proof -
  let ?E = "named_to_source G [] A"
  have prefix_language: "sterm_in_language L \<Sigma> (source_prefix G m) ?E \<tau>"
    by (rule named_encoding_prefix_language[OF language bound])
  have typed: "has_stype L (source_prefix G m) ?E \<tau>"
    using prefix_language unfolding sterm_in_language_def by (rule conjunct1)
  have decoded: "named_to_source G [] (source_to_named G [0..<m] ?E) = srename (\<lambda>i. [0..<m] ! i) ?E"
    by (rule source_to_named_empty_encoding[OF typed named_identity_prefix_chart rich])
  have agree: "srename (\<lambda>i. [0..<m] ! i) ?E = srename (named_index []) ?E"
  proof (rule srename_fv_agreement)
    fix n
    assume source_free: "n \<in> sfv ?E"
    have free: "n \<in> named_fv A" using source_free by (simp only: named_to_source_empty_fv)
    have index: "n < m" by (rule named_prefix_free_name[OF bound free])
    show "[0..<m] ! n = named_index [] n" using index by simp
  qed
  have identity: "srename (named_index []) ?E = ?E"
    by (rule named_to_source_stack_from_empty[where G=G and ns="[]" and A=A])
  show ?thesis by (rule trans[OF decoded trans[OF agree identity]])
qed

theorem named_prefix_roundtrip_alpha:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
    and bound: "source_free_bound (named_to_source G [] A) \<le> m"
    and rich: "sg_rich G"
  shows "named_alpha G (source_to_named G [0..<m] (named_to_source G [] A)) A"
  by (rule named_encoding_implies_alpha[OF rich named_prefix_roundtrip_encoding[OF language bound rich]])

end
