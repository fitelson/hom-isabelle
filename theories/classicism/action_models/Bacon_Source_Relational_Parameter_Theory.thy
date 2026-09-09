theory Bacon_Source_Relational_Parameter_Theory
  imports Bacon_Source_Relational_Theoretical_Naming_Independence
    Bacon_Source_Relational_Constant_Map
begin

section \<open>The finite-chart parameter extension of a supplied theory\<close>

text \<open>
  T↑ consists of expanded R formulas A whose replacement by one
  fresh typed chart belongs to T. The definition itself imposes no
  closure properties on T; the chart-independence theorem below uses
  precisely the original H-theory and R-richness assumptions.

  This parameter theory is distinct from the premise set T⁺ of
  p.51–52 n.73: neither the positive diagram nor the negative
  discriminator is added here. D is an arbitrary typed family of
  new names, not an assumed model or an inhabited domain family.
  H inclusion and rule closure remain separate proof obligations.
\<close>

definition paper_R_parameter_theory ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> (otype \<Rightarrow> 'v set) \<Rightarrow>
    'c paper_named_term set \<Rightarrow> ('c + 'v) paper_named_term set" where
  "paper_R_parameter_theory \<Sigma> G D T =
    {A. paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop \<and>
      (\<exists>x. paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x \<and>
        paper_R_naming_replace x A \<in> T)}"

lemma paper_R_parameter_theoryI:
  assumes language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    and chart: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
    and member: "paper_R_naming_replace x A \<in> T"
  shows "A \<in> paper_R_parameter_theory \<Sigma> G D T"
  using assms unfolding paper_R_parameter_theory_def by blast

lemma paper_R_parameter_theoryE:
  assumes member: "A \<in> paper_R_parameter_theory \<Sigma> G D T"
  obtains x where "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
    "paper_R_naming_replace x A \<in> T"
  using member that unfolding paper_R_parameter_theory_def by blast

lemma paper_R_parameter_theory_language:
  "A \<in> paper_R_parameter_theory \<Sigma> G D T \<Longrightarrow>
    paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
  unfolding paper_R_parameter_theory_def by blast

theorem paper_R_parameter_theory_at_chart_iff:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    and chart: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
  shows "(A \<in> paper_R_parameter_theory \<Sigma> G D T) \<longleftrightarrow> (paper_R_naming_replace x A \<in> T)"
proof
  assume member: "A \<in> paper_R_parameter_theory \<Sigma> G D T"
  obtain y where other: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) y"
    and original: "paper_R_naming_replace y A \<in> T"
    using paper_R_parameter_theoryE[OF member] by blast
  show "paper_R_naming_replace x A \<in> T"
    by (rule iffD1[OF paper_R_theoretical_naming_independent[
      OF rich theory_h language other chart] original])
next
  assume original: "paper_R_naming_replace x A \<in> T"
  show "A \<in> paper_R_parameter_theory \<Sigma> G D T"
    by (rule paper_R_parameter_theoryI[OF language chart original])
qed

theorem paper_R_parameter_theory_at_larger_chart_iff:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    and chart: "paper_R_naming_chart G K N x"
    and support: "paper_R_naming_support A \<subseteq> K" and avoid: "named_vars A \<subseteq> N"
  shows "(A \<in> paper_R_parameter_theory \<Sigma> G D T) \<longleftrightarrow> (paper_R_naming_replace x A \<in> T)"
  by (rule paper_R_parameter_theory_at_chart_iff[OF rich theory_h language
    paper_R_naming_chart_restrict[OF chart support avoid]])

theorem paper_R_parameter_theory_old_iff:
  fixes A :: "'c paper_named_term" and D :: "otype \<Rightarrow> 'v set"
  assumes theory_h: "paper_R_H_theory \<Sigma> G T"
  shows "(paper_R_constant_map Inl A \<in> paper_R_parameter_theory \<Sigma> G D T) \<longleftrightarrow> (A \<in> T)"
proof
  assume member: "paper_R_constant_map Inl A \<in> paper_R_parameter_theory \<Sigma> G D T"
  show "A \<in> T" using member
    by (auto simp only: paper_R_parameter_theory_def mem_Collect_eq paper_R_naming_replace_old)
next
  assume member: "A \<in> T"
  have old_language: "paper_R_in_language \<Sigma> G A Prop"
    by (rule paper_R_H_theory_language[OF theory_h member])
  have language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (paper_R_constant_map Inl A) Prop"
    by (rule paper_R_constant_map_language[OF old_language]; simp)
  have chart: "paper_R_naming_chart G (paper_R_naming_support (paper_R_constant_map Inl A :: ('c + 'v) paper_named_term))
      (named_vars (paper_R_constant_map Inl A)) (\<lambda>_. 0)"
    by (simp only: paper_R_naming_support_old_embedding; simp add: paper_R_naming_chart_def)
  have replaced: "paper_R_naming_replace (\<lambda>_ :: otype \<times> 'v. 0) (paper_R_constant_map Inl A) \<in> T"
    by (simp only: paper_R_naming_replace_old; rule member)
  show "paper_R_constant_map Inl A \<in> paper_R_parameter_theory \<Sigma> G D T"
    by (rule paper_R_parameter_theoryI[OF language chart replaced])
qed

end
