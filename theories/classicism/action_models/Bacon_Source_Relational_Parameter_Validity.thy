theory Bacon_Source_Relational_Parameter_Validity
  imports Bacon_Source_Relational_Parameter_Theory Bacon_Source_Relational_Naming_Model
    Bacon_Source_Relational_Validity_Basics
begin

section \<open>The actual naming model validates the parameter extension\<close>

text \<open>
  If every member of T is valid in M, every member of T↑ is valid
  in the constructed naming model M⁺. A parameter formula supplies
  one chart whose replacement lies in T. Its overriding assignment is
  typed and adequate, so validity in M applies to that replacement.

  This argument uses the existential chart in the definition directly.
  No H-theory hypothesis, Propositional Equivalence closure, model
  existence theorem, or extra closure property of T↑ is assumed.
  Source role: the parameter-language part of p.51–52 n.73, separate
  from adding the positive diagram and the negative discriminator.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_parameter_formula_valid:
  assumes valid_source: "\<forall>B\<in>T. paper_R_valid B"
    and member: "A \<in> paper_R_parameter_theory signature stock domain T"
  shows "paper_R_bbk_model.paper_R_valid (paper_R_naming_signature signature domain) stock domain
    paper_R_naming_denote valuation A"
proof -
  interpret Expanded: paper_R_bbk_model "paper_R_naming_signature signature domain" stock domain
    paper_R_naming_denote valuation by (rule paper_R_naming_model)
  obtain x where language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A Prop"
    and chart: "paper_R_naming_chart stock (paper_R_naming_support A) (named_vars A) x"
    and replaced: "paper_R_naming_replace x A \<in> T"
    by (rule paper_R_parameter_theoryE[OF member])
  have valid_replacement: "paper_R_valid (paper_R_naming_replace x A)" using valid_source replaced by blast
  show ?thesis
  proof (rule Expanded.paper_R_validI[OF language])
    fix g
    assume typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    have override_type: "named_env_typed domain stock (paper_R_naming_override (paper_R_naming_support A) x g)"
      by (rule paper_R_naming_term_override_typed[OF language chart typed])
    have override_adequate: "named_adequate (paper_R_naming_override (paper_R_naming_support A) x g)
      (paper_R_naming_replace x A)"
      by (rule paper_R_naming_override_adequate[OF adequate subset_refl])
    have truth: "valuation (denote (paper_R_naming_override (paper_R_naming_support A) x g)
      (paper_R_naming_replace x A))"
      by (rule paper_R_validE[OF valid_replacement override_type override_adequate])
    show "valuation (paper_R_naming_denote g A)"
      by (simp only: paper_R_naming_denote_at_chart[OF language typed adequate chart]
        paper_R_naming_chart_denote_def; rule truth)
  qed
qed

theorem paper_R_parameter_theory_valid:
  assumes valid_source: "\<forall>B\<in>T. paper_R_valid B"
  shows "\<forall>A\<in>paper_R_parameter_theory signature stock domain T.
    paper_R_bbk_model.paper_R_valid (paper_R_naming_signature signature domain) stock domain
      paper_R_naming_denote valuation A"
  by (intro ballI; rule paper_R_parameter_formula_valid[OF valid_source]; assumption)

end

end
