theory Bacon_Source_Relational_Naming_Finite_Family
  imports Bacon_Source_Relational_Naming_Charts
begin

section \<open>A common chart for a finite family of differently typed terms\<close>

definition paper_R_naming_family_support ::
  "('c + 'v, 'l) named_term set \<Rightarrow> (otype \<times> 'v) set" where
  "paper_R_naming_family_support T = (\<Union>A\<in>T. paper_R_naming_support A)"

definition paper_R_naming_family_vars :: "('c + 'v, 'l) named_term set \<Rightarrow> nat set" where
  "paper_R_naming_family_vars T = (\<Union>A\<in>T. named_vars A)"

lemma paper_R_naming_family_support_finite:
  assumes finite: "finite T"
  shows "finite (paper_R_naming_family_support T)"
  unfolding paper_R_naming_family_support_def
  by (rule finite_UN_I[OF finite]; rule paper_R_naming_support_finite)

lemma paper_R_naming_family_vars_finite:
  assumes finite: "finite T"
  shows "finite (paper_R_naming_family_vars T)"
  unfolding paper_R_naming_family_vars_def
  by (rule finite_UN_I[OF finite]; rule named_vars_finite)

lemma paper_R_naming_family_support_contains:
  "A \<in> T \<Longrightarrow> paper_R_naming_support A \<subseteq> paper_R_naming_family_support T"
  unfolding paper_R_naming_family_support_def by blast

lemma paper_R_naming_family_vars_contains:
  "A \<in> T \<Longrightarrow> named_vars A \<subseteq> paper_R_naming_family_vars T"
  unfolding paper_R_naming_family_vars_def by blast

lemma paper_R_naming_family_supported_types:
  assumes languages: "\<And>A. A \<in> T \<Longrightarrow> \<exists>\<tau>. paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A \<tau>"
  shows "\<forall>k\<in>paper_R_naming_family_support T. paper_R_type (fst k) \<and> snd k \<in> D (fst k)"
proof (intro ballI)
  fix k
  assume member: "k \<in> paper_R_naming_family_support T"
  obtain A where term_member: "A \<in> T" and key: "k \<in> paper_R_naming_support A"
    using member unfolding paper_R_naming_family_support_def by blast
  obtain \<tau> where language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A \<tau>"
    using languages[OF term_member] by blast
  have typed: "paper_R_has_type G A \<tau>"
    and names: "named_in_signature (paper_R_naming_signature \<Sigma> D) A"
    using language unfolding paper_R_in_language_def by blast+
  show "paper_R_type (fst k) \<and> snd k \<in> D (fst k)"
    using paper_R_naming_support_R_types[OF typed] paper_R_naming_support_values[OF names] key by blast
qed

theorem paper_R_naming_family_chart_exists:
  assumes rich: "paper_R_rich G" and finite: "finite T"
    and languages: "\<And>A. A \<in> T \<Longrightarrow> \<exists>\<tau>. paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A \<tau>"
  obtains x where "paper_R_naming_chart G (paper_R_naming_family_support T) (paper_R_naming_family_vars T) x"
    and "\<forall>k\<in>paper_R_naming_family_support T. snd k \<in> D (fst k)"
proof -
  note finish = that
  have supported: "\<forall>k\<in>paper_R_naming_family_support T. paper_R_type (fst k) \<and> snd k \<in> D (fst k)"
    by (rule paper_R_naming_family_supported_types[OF languages])
  have types: "\<forall>k\<in>paper_R_naming_family_support T. paper_R_type (fst k)"
    and payloads: "\<forall>k\<in>paper_R_naming_family_support T. snd k \<in> D (fst k)" using supported by blast+
  obtain x where chart: "paper_R_naming_chart G (paper_R_naming_family_support T) (paper_R_naming_family_vars T) x"
    using paper_R_naming_chart_exists[OF rich paper_R_naming_family_support_finite[OF finite]
      types paper_R_naming_family_vars_finite[OF finite]] by blast
  show thesis by (rule finish[OF chart payloads])
qed

end
