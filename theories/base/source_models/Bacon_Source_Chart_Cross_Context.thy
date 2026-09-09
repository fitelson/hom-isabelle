theory Bacon_Source_Chart_Cross_Context
  imports Bacon_Source_Chart_Independence
begin

section \<open>Locality across frames with aligned names on the actual free slots\<close>

text \<open>
  Two frames may differ at slots unused by M. If their charts use the
  same name at each free slot of M, and their environments give equal
  values there, the decoded interpretations agree. Source: locality in
  Bacon–Dorr Definition 3.1(ii.c), p.44.

  The two decoded terms have equal empty-stack encodings because renaming
  consults only free slots. They are therefore α-equivalent. After changing
  one decoding by α, named locality compares the partial assignments only
  on its free names. No agreement on unused slots, equality of frames,
  Functionality, or original-domain disjointness is assumed.
\<close>

context paper_named_bbk_model
begin

theorem chart_denote_cross_context:
  assumes left: "sterm_in_language paper_logical_type signature \<Gamma> M \<tau>"
    and right: "sterm_in_language paper_logical_type signature \<Delta> M \<tau>"
    and first: "named_chart stock \<Gamma> ns" and second: "named_chart stock \<Delta> ms"
    and re: "pbbk_env_typed domain \<Gamma> \<rho>" and se: "pbbk_env_typed domain \<Delta> \<xi>"
    and names: "\<And>i. i \<in> sfv M \<Longrightarrow> ns ! i = ms ! i"
    and same_values: "\<And>i. i \<in> sfv M \<Longrightarrow> \<rho> i = \<xi> i"
  shows "chart_denote ns \<rho> M = chart_denote ms \<xi> M"
proof -
  let ?A = "source_to_named stock ns M"
  let ?B = "source_to_named stock ms M"
  let ?g = "named_chart_assignment ns \<rho>"
  let ?h = "named_chart_assignment ms \<xi>"
  have lt: "has_stype paper_logical_type \<Gamma> M \<tau>"
    and rt: "has_stype paper_logical_type \<Delta> M \<tau>"
    using left right unfolding sterm_in_language_def by auto
  have renamed: "srename (\<lambda>i. ns ! i) M = srename (\<lambda>i. ms ! i) M"
    by (rule srename_fv_agreement[OF names])
  have encodings: "named_to_source stock [] ?A = named_to_source stock [] ?B"
    by (simp only: source_to_named_empty_encoding[OF lt first stock_rich]
      source_to_named_empty_encoding[OF rt second stock_rich] renamed)
  have alpha: "named_alpha stock ?A ?B" by (rule named_encoding_implies_alpha[OF stock_rich encodings])
  have gt: "named_env_typed domain stock ?g" by (rule named_chart_assignment_typed[OF first re])
  have ht: "named_env_typed domain stock ?h" by (rule named_chart_assignment_typed[OF second se])
  have ga: "named_adequate ?g ?A" by (rule chart_decoder_adequate[OF lt first])
  have gb: "named_adequate ?g ?B"
    using ga named_alpha_fv[OF alpha] unfolding named_adequate_def by simp
  have hb: "named_adequate ?h ?B" by (rule chart_decoder_adequate[OF rt second])
  have decoded: "denote ?g ?A = denote ?g ?B"
    by (rule paper_named_alpha_denote[OF alpha source_to_named_language[OF left first stock_rich] gt ga])
  have agree: "?g n = ?h n" if free: "n \<in> named_fv ?B" for n
  proof -
    obtain i where source_free: "i \<in> sfv M" and named: "n = ms ! i"
      using free source_to_named_fv_exact[OF rt second stock_rich] by auto
    have lb: "i < length \<Gamma>" using subsetD[OF source_typed_fv_bound[OF lt] source_free] by simp
    have rb: "i < length \<Delta>" using subsetD[OF source_typed_fv_bound[OF rt] source_free] by simp
    have nb: "i < length ns" using lb named_chart_length[OF first] by simp
    have mb: "i < length ms" using rb named_chart_length[OF second] by simp
    have namel: "n = ns ! i" by (rule trans[OF named sym[OF names[OF source_free]]])
    have gv: "?g n = Some (\<rho> i)"
      by (simp only: namel named_chart_assignment_lookup[OF named_chart_distinct[OF first] nb])
    have hv: "?h n = Some (\<xi> i)"
      by (simp only: named named_chart_assignment_lookup[OF named_chart_distinct[OF second] mb])
    show "?g n = ?h n" by (simp only: gv hv same_values[OF source_free])
  qed
  have assignment: "denote ?g ?B = denote ?h ?B"
    by (rule denote_locality[OF source_to_named_language[OF right second stock_rich] gt ht gb hb agree])
  show ?thesis unfolding chart_denote_def by (rule trans[OF decoded assignment])
qed

end

end
