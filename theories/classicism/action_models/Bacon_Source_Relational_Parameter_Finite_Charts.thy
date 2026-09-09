theory Bacon_Source_Relational_Parameter_Finite_Charts
  imports Bacon_Source_Relational_Parameter_Theory
    Bacon_Source_Relational_Naming_Finite_Family Bacon_Source_Relational_Naming_Substitution
begin

section \<open>Common finite charts for individual rule instances\<close>

theorem paper_R_parameter_family_chart:
  assumes rich: "paper_R_rich G" and finite: "finite F"
    and languages: "\<And>A. A \<in> F \<Longrightarrow>
      paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
  obtains x where "paper_R_naming_chart G (paper_R_naming_family_support F)
      (paper_R_naming_family_vars F) x"
proof -
  have typed: "\<exists>\<tau>. paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A \<tau>"
    if "A \<in> F" for A
    by (rule exI[where x=Prop], rule languages[OF that])
  obtain x where chart: "paper_R_naming_chart G (paper_R_naming_family_support F)
      (paper_R_naming_family_vars F) x"
    using paper_R_naming_family_chart_exists[OF rich finite typed] by blast
  show thesis by (rule that[OF chart])
qed

lemma paper_R_parameter_family_chart_at:
  assumes chart: "paper_R_naming_chart G (paper_R_naming_family_support F)
      (paper_R_naming_family_vars F) x" and member: "A \<in> F"
  shows "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
  by (rule paper_R_naming_chart_restrict[OF chart
    paper_R_naming_family_support_contains[OF member]
    paper_R_naming_family_vars_contains[OF member]])

lemma paper_R_parameter_family_fresh:
  assumes chart: "paper_R_naming_chart G (paper_R_naming_family_support F)
      (paper_R_naming_family_vars F) x"
    and member: "A \<in> F" and bound_name: "n \<in> paper_R_naming_family_vars F"
    and fresh: "n \<notin> named_fv A"
  shows "n \<notin> named_fv (paper_R_naming_replace x A)"
proof -
  have support: "paper_R_naming_support A \<subseteq> paper_R_naming_family_support F"
    by (rule paper_R_naming_family_support_contains[OF member])
  have marker: "n \<notin> image x (paper_R_naming_support A)"
    using chart support bound_name unfolding paper_R_naming_chart_def by blast
  show ?thesis by (rule paper_R_naming_replace_preserves_fresh[OF fresh marker])
qed

text \<open>
  F is a finite family of formulas involved in a single rule instance,
  not the entire original theory. Including the displayed quantifier
  conclusion in F makes its eigenvariable part of the avoided set.
  This preserves Gen/Inst freshness after replacing new parameters.
\<close>

end
