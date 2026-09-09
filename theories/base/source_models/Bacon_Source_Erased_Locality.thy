theory Bacon_Source_Erased_Locality
  imports Bacon_Source_Erased_Denotation Bacon_Source_Chart_Cross_Context
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Coherent_Charts
begin

section \<open>Context-free locality with different typing frames\<close>

text \<open>
  If Γ and Δ both type M, and ρ and ξ agree on M's actual free
  slots, tagged typing forces Γ and Δ to give those slots the same types.
  Choose charts that assign matching names precisely there. The checked
  cross-context named argument identifies their denotations; erased
  agreement transfers the equality to J(ρ,M) and J(ξ,M).
  Source: Bacon–Dorr Definition 3.1(ii.c), p.44.

  Unused slots may have different types and values, even below M's largest
  free index. The proof does not replace locality by its same-context
  special case. No model at the finite-frame level is assumed.
\<close>

theorem named_erased_denote_locality:
  assumes model: "paper_named_bbk_model \<Sigma> G (named_tag_domain D) J V"
    and left: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> M \<tau>"
    and right: "sterm_in_language paper_logical_type \<Sigma> \<Delta> M \<tau>"
    and re: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
    and se: "pbbk_env_typed (named_tag_domain D) \<Delta> \<xi>"
    and agree: "\<And>i. i \<in> sfv M \<Longrightarrow> \<rho> i = \<xi> i"
  shows "named_erased_denote G J \<rho> M = named_erased_denote G J \<xi> M"
proof -
  interpret Named: paper_named_bbk_model \<Sigma> G "named_tag_domain D" J V by (rule model)
  have lt: "has_stype paper_logical_type \<Gamma> M \<tau>"
    and rt: "has_stype paper_logical_type \<Delta> M \<tau>"
    using left right unfolding sterm_in_language_def by auto
  have types: "\<Gamma> ! i = \<Delta> ! i" if free: "i \<in> sfv M" for i
  proof -
    have lb: "i < length \<Gamma>" using subsetD[OF source_typed_fv_bound[OF lt] free] by simp
    have rb: "i < length \<Delta>" using subsetD[OF source_typed_fv_bound[OF rt] free] by simp
    have ltag: "fst (\<rho> i) = \<Gamma> ! i" by (rule named_tagged_env_nth_type[OF re lb])
    have rtag: "fst (\<xi> i) = \<Delta> ! i" by (rule named_tagged_env_nth_type[OF se rb])
    have tags: "fst (\<rho> i) = fst (\<xi> i)" by (simp only: agree[OF free])
    show "\<Gamma> ! i = \<Delta> ! i" by (rule trans[OF sym[OF ltag] trans[OF tags rtag]])
  qed
  define ns where "ns = named_coherent_chart G \<Gamma>"
  define ms where "ms = named_coherent_chart G \<Delta>"
  have nc: "named_chart G \<Gamma> ns"
    unfolding ns_def by (rule named_coherent_chart_valid[OF Named.stock_rich])
  have mc: "named_chart G \<Delta> ms"
    unfolding ms_def by (rule named_coherent_chart_valid[OF Named.stock_rich])
  have names: "ns ! i = ms ! i" if free: "i \<in> sfv M" for i
  proof -
    have lb: "i < length \<Gamma>" using subsetD[OF source_typed_fv_bound[OF lt] free] by simp
    have rb: "i < length \<Delta>" using subsetD[OF source_typed_fv_bound[OF rt] free] by simp
    show "ns ! i = ms ! i" unfolding ns_def ms_def
      by (rule named_coherent_chart_agreement[OF lb rb types[OF free]])
  qed
  have compared: "Named.chart_denote ns \<rho> M = Named.chart_denote ms \<xi> M"
    by (rule Named.chart_denote_cross_context[OF left right nc mc re se names agree])
  have la: "named_erased_denote G J \<rho> M = Named.chart_denote ns \<rho> M"
    using named_erased_denote_agrees[OF model left re nc] by (simp only: Named.chart_denote_def)
  have ra: "named_erased_denote G J \<xi> M = Named.chart_denote ms \<xi> M"
    using named_erased_denote_agrees[OF model right se mc] by (simp only: Named.chart_denote_def)
  show ?thesis by (rule trans[OF la trans[OF compared sym[OF ra]]])
qed

end
