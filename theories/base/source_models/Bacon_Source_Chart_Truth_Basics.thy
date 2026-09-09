theory Bacon_Source_Chart_Truth_Basics
  imports Bacon_Source_Chart_Conversion_Denotation
begin

section \<open>The non-quantifier truth clauses through a named chart\<close>

text \<open>
  Negation, conjunction, disjunction, and identity have their source truth
  clauses under chart interpretation. In particular A =σ B is true exactly
  when the two denotations are equal, not merely equally true.
  Source: Bacon–Dorr Definition 3.1(iii.a–c,f), p.44.

  Representation. The decoder preserves applications of the first-class
  logical constants literally. Language guards imply adequacy of the
  finite chart assignment. The underlying model is an arbitrary named
  model; no tagged-model origin or Functionality is assumed, and no
  quantifier clause is used in this leaf.
\<close>

context paper_named_bbk_model
begin

lemma chart_decoder_language_adequate:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> A \<tau>"
    and chart: "named_chart stock \<Gamma> ns"
  shows "named_adequate (named_chart_assignment ns \<rho>) (source_to_named stock ns A)"
proof -
  have typed: "has_stype paper_logical_type \<Gamma> A \<tau>"
    using language unfolding sterm_in_language_def by (rule conjunct1)
  show ?thesis by (rule chart_decoder_adequate[OF typed chart])
qed

theorem chart_valuation_neg:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> A Prop"
    and chart: "named_chart stock \<Gamma> ns" and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "valuation (chart_denote ns \<rho> (SApp (SLogical SNot) A)) = (\<not> valuation (chart_denote ns \<rho> A))"
proof -
  have clause: "valuation (denote (named_chart_assignment ns \<rho>)
    (NApp (NLogical SNot) (source_to_named stock ns A))) =
    (\<not> valuation (denote (named_chart_assignment ns \<rho>) (source_to_named stock ns A)))"
    by (rule valuation_neg[OF source_to_named_language[OF language chart stock_rich]
      named_chart_assignment_typed[OF chart env] chart_decoder_language_adequate[OF language chart]])
  show ?thesis using clause by (simp only: chart_denote_def source_to_named.simps)
qed

theorem chart_valuation_conj:
  assumes left: "sterm_in_language paper_logical_type signature \<Gamma> A Prop"
    and right: "sterm_in_language paper_logical_type signature \<Gamma> B Prop"
    and chart: "named_chart stock \<Gamma> ns" and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "valuation (chart_denote ns \<rho> (SApp (SApp (SLogical SAnd) A) B)) =
    (valuation (chart_denote ns \<rho> A) \<and> valuation (chart_denote ns \<rho> B))"
proof -
  have clause: "valuation (denote (named_chart_assignment ns \<rho>)
    (NApp (NApp (NLogical SAnd) (source_to_named stock ns A)) (source_to_named stock ns B))) =
    (valuation (denote (named_chart_assignment ns \<rho>) (source_to_named stock ns A)) \<and>
      valuation (denote (named_chart_assignment ns \<rho>) (source_to_named stock ns B)))"
    by (rule valuation_conj[OF source_to_named_language[OF left chart stock_rich]
      source_to_named_language[OF right chart stock_rich] named_chart_assignment_typed[OF chart env]
      chart_decoder_language_adequate[OF left chart] chart_decoder_language_adequate[OF right chart]])
  show ?thesis using clause by (simp only: chart_denote_def source_to_named.simps)
qed

theorem chart_valuation_disj:
  assumes left: "sterm_in_language paper_logical_type signature \<Gamma> A Prop"
    and right: "sterm_in_language paper_logical_type signature \<Gamma> B Prop"
    and chart: "named_chart stock \<Gamma> ns" and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "valuation (chart_denote ns \<rho> (SApp (SApp (SLogical SOr) A) B)) =
    (valuation (chart_denote ns \<rho> A) \<or> valuation (chart_denote ns \<rho> B))"
proof -
  have clause: "valuation (denote (named_chart_assignment ns \<rho>)
    (NApp (NApp (NLogical SOr) (source_to_named stock ns A)) (source_to_named stock ns B))) =
    (valuation (denote (named_chart_assignment ns \<rho>) (source_to_named stock ns A)) \<or>
      valuation (denote (named_chart_assignment ns \<rho>) (source_to_named stock ns B)))"
    by (rule valuation_disj[OF source_to_named_language[OF left chart stock_rich]
      source_to_named_language[OF right chart stock_rich] named_chart_assignment_typed[OF chart env]
      chart_decoder_language_adequate[OF left chart] chart_decoder_language_adequate[OF right chart]])
  show ?thesis using clause by (simp only: chart_denote_def source_to_named.simps)
qed

theorem chart_valuation_identity:
  assumes left: "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>"
    and right: "sterm_in_language paper_logical_type signature \<Gamma> B \<sigma>"
    and chart: "named_chart stock \<Gamma> ns" and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "valuation (chart_denote ns \<rho> (SApp (SApp (SLogical (SEq \<sigma>)) A) B)) =
    (chart_denote ns \<rho> A = chart_denote ns \<rho> B)"
proof -
  have clause: "valuation (denote (named_chart_assignment ns \<rho>)
    (NApp (NApp (NLogical (SEq \<sigma>)) (source_to_named stock ns A)) (source_to_named stock ns B))) =
    (denote (named_chart_assignment ns \<rho>) (source_to_named stock ns A) =
      denote (named_chart_assignment ns \<rho>) (source_to_named stock ns B))"
    by (rule valuation_identity[OF source_to_named_language[OF left chart stock_rich]
      source_to_named_language[OF right chart stock_rich] named_chart_assignment_typed[OF chart env]
      chart_decoder_language_adequate[OF left chart] chart_decoder_language_adequate[OF right chart]])
  show ?thesis using clause by (simp only: chart_denote_def source_to_named.simps)
qed

end

end
