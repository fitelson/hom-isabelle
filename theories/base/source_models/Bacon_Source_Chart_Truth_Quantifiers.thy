theory Bacon_Source_Chart_Truth_Quantifiers
  imports Bacon_Source_Chart_Quantifier_Instance
begin

section \<open>Universal and existential truth through finite named charts\<close>

text \<open>
  For F:σ → t, ∀σ F is true under a chart exactly when its extended
  instance is true for every a ∈ Dσ; ∃σ F uses some a ∈ Dσ instead.
  Source: Bacon–Dorr Definition 3.1(iii.d–e), pp.43–44.

  Representation: the fresh name n has type σ and lies outside the
  finite chart. Hence it is absent from the decoded F's free names.
  The named quantifier clauses and chart_quantifier_instance supply the
  equations below. Status: arbitrary independent named models, including
  overlapping domains. No Functionality or identification of different
  typing frames is assumed.
\<close>

context paper_named_bbk_model
begin

lemma chart_quantifier_name_fresh:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> F \<tau>"
    and chart: "named_chart stock \<Gamma> ns" and fresh: "n \<notin> set ns"
  shows "n \<notin> named_fv (source_to_named stock ns F)"
proof -
  have typed: "has_stype paper_logical_type \<Gamma> F \<tau>"
    using language unfolding sterm_in_language_def by (rule conjunct1)
  have support: "named_fv (source_to_named stock ns F) \<subseteq> set ns"
    by (rule source_to_named_fv_bound[OF typed chart stock_rich])
  show ?thesis using support fresh by blast
qed

theorem chart_valuation_forall:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> Prop)"
    and chart: "named_chart stock \<Gamma> ns"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
    and n_type: "stock n = \<sigma>" and fresh: "n \<notin> set ns"
  shows "valuation (chart_denote ns \<rho> (SApp (SLogical (SAll \<sigma>)) F)) =
    (\<forall>a \<in> domain \<sigma>. valuation (chart_denote (n # ns) (pbbk_extend a \<rho>)
      (SApp (sshift F) (SVar 0))))"
proof -
  let ?g = "named_chart_assignment ns \<rho>"
  let ?D = "source_to_named stock ns F"
  have decoded: "named_in_language paper_logical_type signature stock ?D (Arr \<sigma> Prop)"
    by (rule source_to_named_language[OF language chart stock_rich])
  have typed_assignment: "named_env_typed domain stock ?g"
    by (rule named_chart_assignment_typed[OF chart env])
  have adequate: "named_adequate ?g ?D"
    by (rule chart_decoder_language_adequate[OF language chart])
  have fresh_decoded: "n \<notin> named_fv ?D"
    by (rule chart_quantifier_name_fresh[OF language chart fresh])
  have clause: "valuation (denote ?g (NApp (NLogical (SAll \<sigma>)) ?D)) =
    (\<forall>a \<in> domain \<sigma>. valuation (denote (?g(n := Some a)) (NApp ?D (NVar n))))"
    by (rule valuation_forall[OF decoded typed_assignment adequate n_type fresh_decoded])
  have instances:
    "(\<forall>a \<in> domain \<sigma>. valuation (denote (?g(n := Some a)) (NApp ?D (NVar n)))) =
     (\<forall>a \<in> domain \<sigma>. valuation (chart_denote (n # ns) (pbbk_extend a \<rho>)
       (SApp (sshift F) (SVar 0))))"
  proof (rule ball_cong[OF refl])
    fix a
    assume member: "a \<in> domain \<sigma>"
    have same: "chart_denote (n # ns) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)) =
      denote (?g(n := Some a)) (NApp ?D (NVar n))"
      by (rule chart_quantifier_instance[OF language chart env n_type fresh member])
    show "valuation (denote (?g(n := Some a)) (NApp ?D (NVar n))) =
      valuation (chart_denote (n # ns) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)))"
      by (rule arg_cong[where f=valuation, OF sym[OF same]])
  qed
  show ?thesis using trans[OF clause instances]
    by (simp only: chart_denote_def source_to_named.simps)
qed

theorem chart_valuation_exists:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> Prop)"
    and chart: "named_chart stock \<Gamma> ns"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
    and n_type: "stock n = \<sigma>" and fresh: "n \<notin> set ns"
  shows "valuation (chart_denote ns \<rho> (SApp (SLogical (SEx \<sigma>)) F)) =
    (\<exists>a \<in> domain \<sigma>. valuation (chart_denote (n # ns) (pbbk_extend a \<rho>)
      (SApp (sshift F) (SVar 0))))"
proof -
  let ?g = "named_chart_assignment ns \<rho>"
  let ?D = "source_to_named stock ns F"
  have decoded: "named_in_language paper_logical_type signature stock ?D (Arr \<sigma> Prop)"
    by (rule source_to_named_language[OF language chart stock_rich])
  have typed_assignment: "named_env_typed domain stock ?g"
    by (rule named_chart_assignment_typed[OF chart env])
  have adequate: "named_adequate ?g ?D"
    by (rule chart_decoder_language_adequate[OF language chart])
  have fresh_decoded: "n \<notin> named_fv ?D"
    by (rule chart_quantifier_name_fresh[OF language chart fresh])
  have clause: "valuation (denote ?g (NApp (NLogical (SEx \<sigma>)) ?D)) =
    (\<exists>a \<in> domain \<sigma>. valuation (denote (?g(n := Some a)) (NApp ?D (NVar n))))"
    by (rule valuation_exists[OF decoded typed_assignment adequate n_type fresh_decoded])
  have instances:
    "(\<exists>a \<in> domain \<sigma>. valuation (denote (?g(n := Some a)) (NApp ?D (NVar n)))) =
     (\<exists>a \<in> domain \<sigma>. valuation (chart_denote (n # ns) (pbbk_extend a \<rho>)
       (SApp (sshift F) (SVar 0))))"
  proof (rule bex_cong[OF refl])
    fix a
    assume member: "a \<in> domain \<sigma>"
    have same: "chart_denote (n # ns) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)) =
      denote (?g(n := Some a)) (NApp ?D (NVar n))"
      by (rule chart_quantifier_instance[OF language chart env n_type fresh member])
    show "valuation (denote (?g(n := Some a)) (NApp ?D (NVar n))) =
      valuation (chart_denote (n # ns) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)))"
      by (rule arg_cong[where f=valuation, OF sym[OF same]])
  qed
  show ?thesis using trans[OF clause instances]
    by (simp only: chart_denote_def source_to_named.simps)
qed

end

end
