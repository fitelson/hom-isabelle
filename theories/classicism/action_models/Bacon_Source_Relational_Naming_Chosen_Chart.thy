theory Bacon_Source_Relational_Naming_Chosen_Chart
  imports Bacon_Source_Relational_Naming_Charts
begin

section \<open>Choose one finite chart for each term\<close>

definition paper_R_naming_chosen_chart ::
  "sgcontext \<Rightarrow> ('c + 'v, 'l) named_term \<Rightarrow> (otype \<times> 'v) \<Rightarrow> nat" where
  "paper_R_naming_chosen_chart G A =
    (SOME x. paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x)"

text \<open>
  The chosen chart is constrained only when its existence is proved.
  At an R-typed term every supported name has an R type, and richness
  supplies a finite injective chart avoiding all of that term's variables.
  No property of this choice at arbitrary ill-typed terms is asserted.
\<close>

theorem paper_R_naming_chosen_chart_valid:
  assumes rich: "paper_R_rich G" and typed: "paper_R_has_type G A \<tau>"
  shows "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) (paper_R_naming_chosen_chart G A)"
proof -
  have types: "\<forall>k\<in>paper_R_naming_support A. paper_R_type (fst k)"
    by (rule paper_R_naming_support_R_types[OF typed])
  have exists: "\<exists>x. paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
    by (rule paper_R_naming_chart_exists[OF rich paper_R_naming_support_finite types named_vars_finite])
  show ?thesis unfolding paper_R_naming_chosen_chart_def by (rule someI_ex[OF exists])
qed

corollary paper_R_naming_chosen_chart_language:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Omega> G A \<tau>"
  shows "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) (paper_R_naming_chosen_chart G A)"
proof -
  have typed: "paper_R_has_type G A \<tau>" using language unfolding paper_R_in_language_def by blast
  show ?thesis by (rule paper_R_naming_chosen_chart_valid[OF rich typed])
qed

end
