theory Bacon_Source_Chart_Denotation
  imports Bacon_Source_Chart_Assignments Bacon_Source_Named_BBK_Interface
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Decoder_Roundtrip
    Bacon_Source_Vocabulary_Development.Bacon_Source_Variable_Embedding
begin

section \<open>Interpreting a finite frame through its chosen typed names\<close>

text \<open>
  Given a chart ns for Γ, decode M using ns and interpret it under the
  finite partial assignment nsᵢ ↦ ρ(i). This defines ⟦M⟧ⁿˢ,ρ in an
  arbitrary named model of Bacon–Dorr Definition 3.1, pp.43–44.

  Γ remains in every typing guard. No identification of interpretations
  obtained from different charts or different frames is assumed here.
  The construction uses the original named model's domains, which need
  not be disjoint. Application is inherited from its heterogeneous clause;
  locality depends only on the source term's actual free slots.
\<close>

context paper_named_bbk_model
begin

definition chart_denote :: "nat list \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> 'c paper_term \<Rightarrow> 'v" where
  "chart_denote ns \<rho> M = denote (named_chart_assignment ns \<rho>) (source_to_named stock ns M)"

lemma chart_decoder_adequate:
  assumes typed: "has_stype paper_logical_type \<Gamma> M \<tau>"
    and chart: "named_chart stock \<Gamma> ns"
  shows "named_adequate (named_chart_assignment ns \<rho>) (source_to_named stock ns M)"
  by (rule named_chart_assignment_adequate,
    rule source_to_named_fv_bound[OF typed chart stock_rich])

theorem chart_denote_type:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> M \<tau>"
    and chart: "named_chart stock \<Gamma> ns" and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "chart_denote ns \<rho> M \<in> domain \<tau>"
proof -
  have typed: "has_stype paper_logical_type \<Gamma> M \<tau>"
    using language unfolding sterm_in_language_def by (rule conjunct1)
  show ?thesis unfolding chart_denote_def
    by (rule denote_type[OF source_to_named_language[OF language chart stock_rich]
      named_chart_assignment_typed[OF chart env] chart_decoder_adequate[OF typed chart]])
qed

theorem chart_denote_var:
  assumes chart: "named_chart stock \<Gamma> ns" and env: "pbbk_env_typed domain \<Gamma> \<rho>"
    and slot: "lookup \<Gamma> i = Some \<sigma>"
  shows "chart_denote ns \<rho> (SVar i) = \<rho> i"
proof -
  have assigned: "named_chart_assignment ns \<rho> (ns ! i) = Some (\<rho> i)"
    by (rule named_chart_assignment_lookup[OF named_chart_distinct[OF chart]
      named_chart_lookup_bound[OF chart slot]])
  show ?thesis unfolding chart_denote_def
    by (simp only: source_to_named.simps;
      rule denote_var[OF named_chart_assignment_typed[OF chart env] assigned])
qed

theorem chart_denote_application:
  assumes fl: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> \<tau>)"
    and al: "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>"
    and hl: "sterm_in_language paper_logical_type signature \<Delta> H (Arr \<upsilon> \<omega>)"
    and bl: "sterm_in_language paper_logical_type signature \<Delta> B \<upsilon>"
    and nc: "named_chart stock \<Gamma> ns" and mc: "named_chart stock \<Delta> ms"
    and re: "pbbk_env_typed domain \<Gamma> \<rho>" and se: "pbbk_env_typed domain \<Delta> \<xi>"
    and heads: "chart_denote ns \<rho> F = chart_denote ms \<xi> H"
    and args: "chart_denote ns \<rho> A = chart_denote ms \<xi> B"
  shows "chart_denote ns \<rho> (SApp F A) = chart_denote ms \<xi> (SApp H B)"
proof -
  have ft: "has_stype paper_logical_type \<Gamma> F (Arr \<sigma> \<tau>)"
    and at: "has_stype paper_logical_type \<Gamma> A \<sigma>"
    and ht: "has_stype paper_logical_type \<Delta> H (Arr \<upsilon> \<omega>)"
    and bt: "has_stype paper_logical_type \<Delta> B \<upsilon>"
    using fl al hl bl unfolding sterm_in_language_def by auto
  have ga: "named_adequate (named_chart_assignment ns \<rho>)
    (NApp (source_to_named stock ns F) (source_to_named stock ns A))"
    using chart_decoder_adequate[OF has_stype.App[OF ft at] nc]
    by (simp only: source_to_named.simps)
  have ha: "named_adequate (named_chart_assignment ms \<xi>)
    (NApp (source_to_named stock ms H) (source_to_named stock ms B))"
    using chart_decoder_adequate[OF has_stype.App[OF ht bt] mc]
    by (simp only: source_to_named.simps)
  show ?thesis using heads args unfolding chart_denote_def
    by (simp only: source_to_named.simps;
      rule denote_application_cong[OF source_to_named_language[OF fl nc stock_rich]
        source_to_named_language[OF al nc stock_rich] source_to_named_language[OF hl mc stock_rich]
        source_to_named_language[OF bl mc stock_rich] named_chart_assignment_typed[OF nc re]
        named_chart_assignment_typed[OF mc se] ga ha]; assumption)
qed

theorem chart_denote_locality:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> M \<tau>"
    and chart: "named_chart stock \<Gamma> ns"
    and re: "pbbk_env_typed domain \<Gamma> \<rho>" and se: "pbbk_env_typed domain \<Gamma> \<xi>"
    and agree: "\<And>i. i \<in> sfv M \<Longrightarrow> \<rho> i = \<xi> i"
  shows "chart_denote ns \<rho> M = chart_denote ns \<xi> M"
proof -
  have typed: "has_stype paper_logical_type \<Gamma> M \<tau>"
    using language unfolding sterm_in_language_def by (rule conjunct1)
  have names_agree: "named_chart_assignment ns \<rho> n = named_chart_assignment ns \<xi> n"
    if free: "n \<in> named_fv (source_to_named stock ns M)" for n
  proof -
    obtain i where source_free: "i \<in> sfv M" and name: "n = ns ! i"
      using free source_to_named_fv_exact[OF typed chart stock_rich] by auto
    have bound: "i < length \<Gamma>"
      using subsetD[OF source_typed_fv_bound[OF typed] source_free] by simp
    have chart_bound: "i < length ns" using bound named_chart_length[OF chart] by simp
    show ?thesis by (simp only: name named_chart_assignment_lookup[OF named_chart_distinct[OF chart] chart_bound]
      agree[OF source_free])
  qed
  show ?thesis unfolding chart_denote_def
    by (rule denote_locality[OF source_to_named_language[OF language chart stock_rich]
      named_chart_assignment_typed[OF chart re] named_chart_assignment_typed[OF chart se]
      chart_decoder_adequate[OF typed chart] chart_decoder_adequate[OF typed chart] names_agree])
qed

end

end
