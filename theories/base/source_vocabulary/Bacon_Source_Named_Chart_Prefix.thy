theory Bacon_Source_Named_Chart_Prefix
  imports Bacon_Source_Named_Decoder_Roundtrip Bacon_Source_Variable_Embedding
    Bacon_Source_Named_Alpha_Characterization
begin

section \<open>Restricting a chart to a prefix supporting the same source term\<close>

text \<open>
  If Γ and its prefix Γ↾k both type M, decoding M with a chart ns
  or its prefix ns↾k gives α-equivalent named terms.
  Source role: the finite-support representation of the named variable
  convention in Bacon–Dorr §1.1, p.5.

  Isabelle representation. Both source typings are premises. The shorter
  typing bounds every free slot of M below the prefix length. Therefore
  nth ns and nth (take k ns) agree on precisely those slots. Their
  renamings, and hence the two empty-stack encodings, agree. The proved
  α characterization then supplies the named relation in a rich stock.

  Status. Syntax only: no environment restriction, denotation equality,
  model claim, or Γ-erasure result is asserted. Decoders may choose
  different bound names after the chart shrinks.
\<close>

lemma named_chart_take:
  assumes chart: "named_chart G \<Gamma> ns"
  shows "named_chart G (take k \<Gamma>) (take k ns)"
proof -
  have distinct: "distinct (take k ns)"
    by (rule distinct_take[OF named_chart_distinct[OF chart]])
  have types: "list_all2 (\<lambda>n \<sigma>. G n = \<sigma>) (take k ns) (take k \<Gamma>)"
    by (rule list_all2_takeI[OF named_chart_types[OF chart]])
  show ?thesis unfolding named_chart_def by (rule conjI[OF distinct types])
qed

theorem source_to_named_chart_prefix_encoding:
  assumes whole: "has_stype L \<Gamma> M \<tau>"
    and prefix: "has_stype L (take k \<Gamma>) M \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_to_source G [] (source_to_named G ns M) =
    named_to_source G [] (source_to_named G (take k ns) M)"
proof -
  have small_chart: "named_chart G (take k \<Gamma>) (take k ns)"
    by (rule named_chart_take[OF chart])
  have full_encoding: "named_to_source G [] (source_to_named G ns M) =
    srename (\<lambda>i. ns ! i) M"
    by (rule source_to_named_empty_encoding[OF whole chart rich])
  have small_encoding: "named_to_source G [] (source_to_named G (take k ns) M) =
    srename (\<lambda>i. (take k ns) ! i) M"
    by (rule source_to_named_empty_encoding[OF prefix small_chart rich])
  have support: "sfv M \<subseteq> {..<length (take k \<Gamma>)}"
    by (rule source_typed_fv_bound[OF prefix])
  have renamed: "srename (\<lambda>i. ns ! i) M = srename (\<lambda>i. (take k ns) ! i) M"
  proof (rule srename_fv_agreement)
    fix i
    assume free: "i \<in> sfv M"
    have bound: "i \<in> {..<length (take k \<Gamma>)}" by (rule subsetD[OF support free])
    have before_k: "i < k" using bound by simp
    show "ns ! i = (take k ns) ! i" by (rule sym[OF nth_take[OF before_k]])
  qed
  show ?thesis by (simp only: full_encoding small_encoding renamed)
qed

corollary source_to_named_chart_prefix_alpha:
  assumes whole: "has_stype L \<Gamma> M \<tau>"
    and prefix: "has_stype L (take k \<Gamma>) M \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_alpha G (source_to_named G ns M) (source_to_named G (take k ns) M)"
  by (rule named_encoding_implies_alpha[OF rich
    source_to_named_chart_prefix_encoding[OF whole prefix chart rich]])

end
