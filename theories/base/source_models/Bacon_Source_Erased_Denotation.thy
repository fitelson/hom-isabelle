theory Bacon_Source_Erased_Denotation
  imports Bacon_Source_Framed_Denotation Bacon_Source_Tagged_Frames
    Bacon_Source_Vocabulary_Development.Bacon_Source_Minimal_Frame
begin

section \<open>Reading the necessary finite typing frame from tagged values\<close>

text \<open>
  Let b(M) be one beyond M's greatest free slot, or zero for a closed
  term. Read the first b(M) type tags of ρ, choose typed names for that
  frame, and interpret the decoded M. This defines J(ρ,M) without an
  explicit Γ argument. Source role: the representation bridge for
  Bacon–Dorr Definition 3.1, pp.43–44.

  The theorem below starts with an independently specified named model
  whose domains are the tagged copies D′σ. If Γ types M and ρ, its
  supported prefix equals the frame read from ρ. The previous restriction
  and name-choice theorems therefore recover interpretation along every
  chart of Γ. No tag is read beyond that proved bound.

  This leaf supplies a denotation agreement theorem. The later
  Bacon_Source_Named_Reverse_Model assembles the model after separate
  cross-frame locality and truth-clause proofs. Off the displayed
  language/environment guards, the total
  definition carries no semantic claim.
\<close>

definition named_erased_denote ::
  "sgcontext \<Rightarrow> ((otype \<times> 'v) named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> otype \<times> 'v)
    \<Rightarrow> (nat \<Rightarrow> otype \<times> 'v) \<Rightarrow> 'c paper_term \<Rightarrow> otype \<times> 'v" where
  "named_erased_denote G J \<rho> M =
    (let \<Gamma> = named_tagged_frame \<rho> (source_free_bound M);
         ns = named_chart_choice G \<Gamma>
     in J (named_chart_assignment ns \<rho>) (source_to_named G ns M))"

theorem named_erased_denote_agrees:
  assumes model: "paper_named_bbk_model \<Sigma> G (named_tag_domain D) J V"
    and language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> M \<tau>"
    and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
    and chart: "named_chart G \<Gamma> ns"
  shows "named_erased_denote G J \<rho> M = J (named_chart_assignment ns \<rho>) (source_to_named G ns M)"
proof -
  interpret Named: paper_named_bbk_model \<Sigma> G "named_tag_domain D" J V by (rule model)
  have typed: "has_stype paper_logical_type \<Gamma> M \<tau>"
    using language unfolding sterm_in_language_def by (rule conjunct1)
  have bound: "source_free_bound M \<le> length \<Gamma>" by (rule source_free_bound_le_context[OF typed])
  have prefix_type: "has_stype paper_logical_type (take (source_free_bound M) \<Gamma>) M \<tau>"
    by (rule source_typing_minimal_frame[OF typed])
  have recovered: "named_tagged_frame \<rho> (source_free_bound M) = take (source_free_bound M) \<Gamma>"
    by (rule named_tagged_frame_prefix[OF env bound])
  have erased: "named_erased_denote G J \<rho> M = Named.framed_denote (take (source_free_bound M) \<Gamma>) \<rho> M"
    by (simp only: named_erased_denote_def Let_def recovered Named.framed_denote_def Named.chart_denote_def)
  have restricted: "Named.framed_denote \<Gamma> \<rho> M = Named.framed_denote (take (source_free_bound M) \<Gamma>) \<rho> M"
    by (rule Named.framed_denote_prefix[OF language prefix_type env])
  have selected: "Named.framed_denote \<Gamma> \<rho> M = J (named_chart_assignment ns \<rho>) (source_to_named G ns M)"
    using Named.framed_denote_chart[OF language env chart] by (simp only: Named.chart_denote_def)
  show ?thesis by (rule trans[OF erased trans[OF sym[OF restricted] selected]])
qed

theorem named_erased_denote_type:
  assumes model: "paper_named_bbk_model \<Sigma> G (named_tag_domain D) J V"
    and language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> M \<tau>"
    and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
  shows "named_erased_denote G J \<rho> M \<in> named_tag_domain D \<tau>"
proof -
  interpret Named: paper_named_bbk_model \<Sigma> G "named_tag_domain D" J V by (rule model)
  let ?ns = "named_chart_choice G \<Gamma>"
  have chart: "named_chart G \<Gamma> ?ns" by (rule named_chart_choice_valid[OF Named.stock_rich])
  have agree: "named_erased_denote G J \<rho> M = Named.chart_denote ?ns \<rho> M"
    using named_erased_denote_agrees[OF model language env chart] by (simp only: Named.chart_denote_def)
  have member: "Named.chart_denote ?ns \<rho> M \<in> named_tag_domain D \<tau>"
    by (rule Named.chart_denote_type[OF language chart env])
  show ?thesis by (simp only: agree; rule member)
qed

end
