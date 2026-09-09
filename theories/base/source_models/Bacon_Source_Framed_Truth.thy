theory Bacon_Source_Framed_Truth
  imports Bacon_Source_Framed_Denotation Bacon_Source_Chart_Truth_Quantifiers
begin

section \<open>The six primitive truth clauses for the framed interpretation\<close>

text \<open>
  The interpretation J(Γ,ρ,A) inherits the truth clauses for ¬, ∧, ∨,
  ∀σ, ∃σ and =σ from every independent named BBK model.
  Source: Bacon–Dorr Definition 3.1(iii.a–f), pp.43–44.

  Representation: framed_denote selects a chart for Γ. For quantifier
  instances, extend that chart by a fresh name n:σ. The independently
  selected chart for σ # Γ need not equal n # ns: framed_denote_chart,
  with its body-language and updated-environment guards, equates their
  denotations. Status: Γ is retained throughout; original domains may
  overlap. No Functionality, disjointness or context-erasure premise is used.
\<close>

context paper_named_bbk_model
begin

theorem framed_valuation_neg:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> A Prop"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "valuation (framed_denote \<Gamma> \<rho> (paper_not A)) =
    (\<not> valuation (framed_denote \<Gamma> \<rho> A))"
  unfolding framed_denote_def paper_not_def
  by (rule chart_valuation_neg[OF language named_chart_choice_valid[OF stock_rich] env])

theorem framed_valuation_conj:
  assumes left: "sterm_in_language paper_logical_type signature \<Gamma> A Prop"
    and right: "sterm_in_language paper_logical_type signature \<Gamma> B Prop"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "valuation (framed_denote \<Gamma> \<rho> (paper_and A B)) =
    (valuation (framed_denote \<Gamma> \<rho> A) \<and> valuation (framed_denote \<Gamma> \<rho> B))"
  unfolding framed_denote_def paper_and_def
  by (rule chart_valuation_conj[OF left right named_chart_choice_valid[OF stock_rich] env])

theorem framed_valuation_disj:
  assumes left: "sterm_in_language paper_logical_type signature \<Gamma> A Prop"
    and right: "sterm_in_language paper_logical_type signature \<Gamma> B Prop"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "valuation (framed_denote \<Gamma> \<rho> (paper_or A B)) =
    (valuation (framed_denote \<Gamma> \<rho> A) \<or> valuation (framed_denote \<Gamma> \<rho> B))"
  unfolding framed_denote_def paper_or_def
  by (rule chart_valuation_disj[OF left right named_chart_choice_valid[OF stock_rich] env])

theorem framed_valuation_identity:
  assumes left: "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>"
    and right: "sterm_in_language paper_logical_type signature \<Gamma> B \<sigma>"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "valuation (framed_denote \<Gamma> \<rho> (SApp (SApp (SLogical (SEq \<sigma>)) A) B)) =
    (framed_denote \<Gamma> \<rho> A = framed_denote \<Gamma> \<rho> B)"
  unfolding framed_denote_def
  by (rule chart_valuation_identity[OF left right named_chart_choice_valid[OF stock_rich] env])

lemma framed_quantifier_chart_instance:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> Prop)"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
    and chart: "named_chart stock \<Gamma> ns"
    and n_type: "stock n = \<sigma>" and fresh: "n \<notin> set ns"
    and member: "a \<in> domain \<sigma>"
  shows "framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)) =
    chart_denote (n # ns) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0))"
proof -
  have body: "sterm_in_language paper_logical_type signature (\<sigma> # \<Gamma>)
    (SApp (sshift F) (SVar 0)) Prop"
    by (rule chart_quantifier_body_language[OF language])
  have extended_env: "pbbk_env_typed domain (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>)"
    by (rule pbbk_env_extend[OF env member])
  have extended_chart: "named_chart stock (\<sigma> # \<Gamma>) (n # ns)"
    by (rule named_chart_Cons[OF chart n_type fresh])
  show ?thesis by (rule framed_denote_chart[OF body extended_env extended_chart])
qed

theorem framed_valuation_forall:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> Prop)"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "valuation (framed_denote \<Gamma> \<rho> (SApp (SLogical (SAll \<sigma>)) F)) =
    (\<forall>a \<in> domain \<sigma>. valuation (framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>)
      (SApp (sshift F) (SVar 0))))"
proof -
  let ?ns = "named_chart_choice stock \<Gamma>"
  let ?n = "named_chart_fresh stock ?ns \<sigma>"
  have chart: "named_chart stock \<Gamma> ?ns"
    by (rule named_chart_choice_valid[OF stock_rich])
  have n_type: "stock ?n = \<sigma>" by (rule named_chart_fresh_type[OF stock_rich])
  have fresh: "?n \<notin> set ?ns" by (rule named_chart_fresh_notin[OF stock_rich])
  have clause: "valuation (chart_denote ?ns \<rho> (SApp (SLogical (SAll \<sigma>)) F)) =
    (\<forall>a \<in> domain \<sigma>. valuation (chart_denote (?n # ?ns) (pbbk_extend a \<rho>)
      (SApp (sshift F) (SVar 0))))"
    by (rule chart_valuation_forall[OF language chart env n_type fresh])
  have instances:
    "(\<forall>a \<in> domain \<sigma>. valuation (chart_denote (?n # ?ns) (pbbk_extend a \<rho>)
       (SApp (sshift F) (SVar 0)))) =
     (\<forall>a \<in> domain \<sigma>. valuation (framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>)
       (SApp (sshift F) (SVar 0))))"
  proof (rule ball_cong[OF refl])
    fix a
    assume member: "a \<in> domain \<sigma>"
    have same: "framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)) =
      chart_denote (?n # ?ns) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0))"
      by (rule framed_quantifier_chart_instance[OF language env chart n_type fresh member])
    show "valuation (chart_denote (?n # ?ns) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0))) =
      valuation (framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)))"
      by (rule arg_cong[where f=valuation, OF sym[OF same]])
  qed
  show ?thesis using trans[OF clause instances] by (simp only: framed_denote_def)
qed

theorem framed_valuation_exists:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> Prop)"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "valuation (framed_denote \<Gamma> \<rho> (SApp (SLogical (SEx \<sigma>)) F)) =
    (\<exists>a \<in> domain \<sigma>. valuation (framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>)
      (SApp (sshift F) (SVar 0))))"
proof -
  let ?ns = "named_chart_choice stock \<Gamma>"
  let ?n = "named_chart_fresh stock ?ns \<sigma>"
  have chart: "named_chart stock \<Gamma> ?ns"
    by (rule named_chart_choice_valid[OF stock_rich])
  have n_type: "stock ?n = \<sigma>" by (rule named_chart_fresh_type[OF stock_rich])
  have fresh: "?n \<notin> set ?ns" by (rule named_chart_fresh_notin[OF stock_rich])
  have clause: "valuation (chart_denote ?ns \<rho> (SApp (SLogical (SEx \<sigma>)) F)) =
    (\<exists>a \<in> domain \<sigma>. valuation (chart_denote (?n # ?ns) (pbbk_extend a \<rho>)
      (SApp (sshift F) (SVar 0))))"
    by (rule chart_valuation_exists[OF language chart env n_type fresh])
  have instances:
    "(\<exists>a \<in> domain \<sigma>. valuation (chart_denote (?n # ?ns) (pbbk_extend a \<rho>)
       (SApp (sshift F) (SVar 0)))) =
     (\<exists>a \<in> domain \<sigma>. valuation (framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>)
       (SApp (sshift F) (SVar 0))))"
  proof (rule bex_cong[OF refl])
    fix a
    assume member: "a \<in> domain \<sigma>"
    have same: "framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)) =
      chart_denote (?n # ?ns) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0))"
      by (rule framed_quantifier_chart_instance[OF language env chart n_type fresh member])
    show "valuation (chart_denote (?n # ?ns) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0))) =
      valuation (framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)))"
      by (rule arg_cong[where f=valuation, OF sym[OF same]])
  qed
  show ?thesis using trans[OF clause instances] by (simp only: framed_denote_def)
qed

end

end
