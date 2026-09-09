theory Bacon_Source_Framed_Denotation
  imports Bacon_Source_Chart_Independence Bacon_Source_Chart_Prefix_Denotation
    Bacon_Source_Chart_Truth_Basics
begin

section \<open>A finite-context interpretation independent of chosen names\<close>

text \<open>
  Define J(Γ,ρ,M) by choosing distinct names of the types in Γ,
  decoding M with those names, and using the corresponding partial
  assignment. The proved independence theorem makes this choice harmless.
  Source role: representing the adequate named assignments of Bacon–Dorr
  Definition 3.1, pp.43–44, by finite typed environments.

  Γ remains an argument. The original domains may overlap. This leaf
  neither erases Γ nor declares an assembled finite-frame model; it gives
  one interpretation agreeing with every permitted choice of names.
\<close>

definition named_chart_choice :: "sgcontext \<Rightarrow> ctx \<Rightarrow> nat list" where
  "named_chart_choice G \<Gamma> = (SOME ns. named_chart G \<Gamma> ns)"

lemma named_chart_choice_valid:
  assumes rich: "sg_rich G"
  shows "named_chart G \<Gamma> (named_chart_choice G \<Gamma>)"
  unfolding named_chart_choice_def by (rule someI_ex, rule named_chart_exists[OF rich])

context paper_named_bbk_model
begin

definition framed_denote :: "ctx \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> 'c paper_term \<Rightarrow> 'v" where
  "framed_denote \<Gamma> \<rho> M = chart_denote (named_chart_choice stock \<Gamma>) \<rho> M"

theorem framed_denote_chart:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> M \<tau>"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>" and chart: "named_chart stock \<Gamma> ns"
  shows "framed_denote \<Gamma> \<rho> M = chart_denote ns \<rho> M"
  unfolding framed_denote_def
  by (rule chart_denote_independent[OF language named_chart_choice_valid[OF stock_rich] chart env])

theorem framed_denote_type:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> M \<tau>"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "framed_denote \<Gamma> \<rho> M \<in> domain \<tau>"
  unfolding framed_denote_def
  by (rule chart_denote_type[OF language named_chart_choice_valid[OF stock_rich] env])

theorem framed_denote_var:
  assumes env: "pbbk_env_typed domain \<Gamma> \<rho>" and slot: "lookup \<Gamma> i = Some \<sigma>"
  shows "framed_denote \<Gamma> \<rho> (SVar i) = \<rho> i"
  unfolding framed_denote_def
  by (rule chart_denote_var[OF named_chart_choice_valid[OF stock_rich] env slot])

theorem framed_denote_locality:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> M \<tau>"
    and re: "pbbk_env_typed domain \<Gamma> \<rho>" and se: "pbbk_env_typed domain \<Gamma> \<xi>"
    and agree: "\<And>i. i \<in> sfv M \<Longrightarrow> \<rho> i = \<xi> i"
  shows "framed_denote \<Gamma> \<rho> M = framed_denote \<Gamma> \<xi> M"
  unfolding framed_denote_def
  by (rule chart_denote_locality[OF language named_chart_choice_valid[OF stock_rich] re se agree])

theorem framed_denote_prefix:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> M \<tau>"
    and prefix_type: "has_stype paper_logical_type (take k \<Gamma>) M \<tau>"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "framed_denote \<Gamma> \<rho> M = framed_denote (take k \<Gamma>) \<rho> M"
proof -
  let ?ns = "named_chart_choice stock \<Gamma>"
  have chart: "named_chart stock \<Gamma> ?ns" by (rule named_chart_choice_valid[OF stock_rich])
  have sig: "sterm_in_signature signature M" using language
    unfolding sterm_in_language_def by (rule conjunct2)
  have prefix_language: "sterm_in_language paper_logical_type signature (take k \<Gamma>) M \<tau>"
    unfolding sterm_in_language_def by (rule conjI[OF prefix_type sig])
  have restricted: "chart_denote ?ns \<rho> M = chart_denote (take k ?ns) \<rho> M"
    by (rule chart_denote_prefix[OF language prefix_type chart env])
  have chosen: "framed_denote (take k \<Gamma>) \<rho> M = chart_denote (take k ?ns) \<rho> M"
    by (rule framed_denote_chart[OF prefix_language chart_prefix_env_typed[OF env] named_chart_take[OF chart]])
  have original: "framed_denote \<Gamma> \<rho> M = chart_denote ?ns \<rho> M"
    by (simp only: framed_denote_def)
  show ?thesis by (rule trans[OF original trans[OF restricted sym[OF chosen]]])
qed

theorem framed_denote_conversion:
  assumes conversion: "sbeta_eta_equiv_in_signature paper_logical_type signature \<Gamma> \<tau> A B"
    and env: "pbbk_env_typed domain \<Gamma> \<rho>"
  shows "framed_denote \<Gamma> \<rho> A = framed_denote \<Gamma> \<rho> B"
  unfolding framed_denote_def
  by (rule chart_denote_conversion[OF conversion named_chart_choice_valid[OF stock_rich] env])

end

end
