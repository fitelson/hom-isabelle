theory Bacon_Source_Named_Decoder_Roundtrip
  imports Bacon_Source_Named_Decoder Bacon_Source_Named_Alpha_Representation
begin

section \<open>The decoded free names implement the chart renaming\<close>

text \<open>
  If ns charts Γ, encoding the decoded term with no surrounding named
  binders gives A with each free slot i renamed to nsᵢ. The two chart
  maps are inverse only on their supported names and slots.
  Source role: the binding conventions of Bacon–Dorr §1.1, p.5.

  Isabelle representation. The proof uses the checked chart-relative
  round trip, the encoding's exact FV equation, and renaming agreement
  on free variables. It never assumes that nth ns is a total inverse
  outside the finite chart. No semantic interpretation or H rule is used.
\<close>

lemma named_chart_nth_index:
  assumes chart: "named_chart G \<Gamma> ns" and member: "n \<in> set ns"
  shows "ns ! named_index ns n = n"
proof -
  obtain i where bound: "i < length ns" and at_i: "ns ! i = n"
    using member by (auto simp: in_set_conv_nth)
  have index: "named_index ns (ns ! i) = i"
    by (rule named_index_nth_distinct[OF named_chart_distinct[OF chart] bound])
  have named_index: "named_index ns n = i" using index by (simp only: at_i)
  show ?thesis by (simp only: named_index at_i)
qed

theorem source_to_named_empty_encoding:
  assumes typed: "has_stype L \<Gamma> A \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_to_source G [] (source_to_named G ns A) = srename (\<lambda>i. ns ! i) A"
proof -
  let ?N = "source_to_named G ns A"
  let ?E = "named_to_source G [] ?N"
  have relative: "named_to_source G ns ?N = A"
    by (rule source_to_named_relative_roundtrip[OF typed chart rich])
  have stacked: "srename (named_index ns) ?E = A"
    by (rule trans[OF named_to_source_stack_from_empty[where G=G and ns=ns and A="?N"] relative])
  have mapped: "srename (\<lambda>i. ns ! i) (srename (named_index ns) ?E) = srename (\<lambda>i. ns ! i) A"
    by (rule arg_cong[where f="srename (\<lambda>i. ns ! i)", OF stacked])
  have composed: "srename ((\<lambda>i. ns ! i) \<circ> named_index ns) ?E = srename (\<lambda>i. ns ! i) A"
    using mapped by (simp only: srename_comp)
  have support: "named_fv ?N \<subseteq> set ns"
    by (rule source_to_named_fv_bound[OF typed chart rich])
  have agreement: "srename ((\<lambda>i. ns ! i) \<circ> named_index ns) ?E = srename (named_index []) ?E"
  proof (rule srename_fv_agreement)
    fix n
    assume free: "n \<in> sfv ?E"
    have named_free: "n \<in> named_fv ?N" using free by (simp only: named_to_source_empty_fv)
    have in_chart: "n \<in> set ns" by (rule subsetD[OF support named_free])
    have inverse: "ns ! named_index ns n = n" by (rule named_chart_nth_index[OF chart in_chart])
    show "((\<lambda>i. ns ! i) \<circ> named_index ns) n = named_index [] n"
      by (simp only: comp_def inverse named_index.simps)
  qed
  have restored: "srename ((\<lambda>i. ns ! i) \<circ> named_index ns) ?E = ?E"
    by (rule trans[OF agreement named_to_source_stack_from_empty[where G=G and ns="[]" and A="?N"]])
  show ?thesis by (rule trans[OF sym[OF restored] composed])
qed

lemma named_chart_image_inverse:
  assumes chart: "named_chart G \<Gamma> ns" and subset: "X \<subseteq> set ns"
  shows "(\<lambda>i. ns ! i) ` (named_index ns ` X) = X"
proof -
  have inverse: "ns ! named_index ns n = n" if "n \<in> X" for n
    by (rule named_chart_nth_index[OF chart subsetD[OF subset that]])
  show ?thesis using inverse by (auto simp: image_iff)
qed

theorem source_to_named_fv_exact:
  assumes typed: "has_stype L \<Gamma> A \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_fv (source_to_named G ns A) = (\<lambda>i. ns ! i) ` sfv A"
proof -
  let ?N = "source_to_named G ns A"
  have relative: "named_to_source G ns ?N = A"
    by (rule source_to_named_relative_roundtrip[OF typed chart rich])
  have fv_eq: "sfv (named_to_source G ns ?N) = sfv A"
    by (rule arg_cong[where f=sfv, OF relative])
  have indexed: "named_index ns ` named_fv ?N = sfv A"
    using fv_eq by (simp only: named_to_source_fv)
  have support: "named_fv ?N \<subseteq> set ns"
    by (rule source_to_named_fv_bound[OF typed chart rich])
  have inverse: "(\<lambda>i. ns ! i) ` (named_index ns ` named_fv ?N) = named_fv ?N"
    by (rule named_chart_image_inverse[OF chart support])
  have mapped: "(\<lambda>i. ns ! i) ` (named_index ns ` named_fv ?N) = (\<lambda>i. ns ! i) ` sfv A"
    by (rule arg_cong[where f="\<lambda>X. (\<lambda>i. ns ! i) ` X", OF indexed])
  show ?thesis by (rule trans[OF sym[OF inverse] mapped])
qed

corollary source_to_named_closed_roundtrip:
  assumes typed: "has_stype L [] A \<tau>" and rich: "sg_rich G"
  shows "named_to_source G [] (source_to_named G [] A) = A"
  by (rule source_to_named_relative_roundtrip[OF typed named_chart_Nil rich])

corollary source_to_named_closed_fv:
  assumes typed: "has_stype L [] A \<tau>" and rich: "sg_rich G"
  shows "named_fv (source_to_named G [] A) = {}"
  using source_to_named_fv_bound[OF typed named_chart_Nil rich] by simp

end
