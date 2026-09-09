theory Bacon_Source_Relational_H_Retraction_Support
  imports Bacon_Source_Relational_Retraction_Syntax
begin

section \<open>A finite avoidance certificate for one H proof\<close>

definition paper_R_H_retraction_support where
  "paper_R_H_retraction_support \<Omega> G A N \<longleftrightarrow>
    finite N \<and> named_vars A \<subseteq> N \<and>
    (\<forall>v. (\<forall>\<rho>. paper_R_type \<rho> \<longrightarrow> G (v \<rho>) = \<rho>) \<longrightarrow>
      (\<forall>\<rho>. v \<rho> \<notin> N) \<longrightarrow> paper_R_named_H \<Omega> G (named_retract \<Omega> v A))"

lemma paper_R_H_retraction_supportI:
  assumes finite: "finite N" and names: "named_vars A \<subseteq> N"
    and transform: "\<And>v. (\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>) \<Longrightarrow>
      (\<And>\<rho>. v \<rho> \<notin> N) \<Longrightarrow> paper_R_named_H \<Omega> G (named_retract \<Omega> v A)"
  shows "paper_R_H_retraction_support \<Omega> G A N"
  using finite names transform unfolding paper_R_H_retraction_support_def by blast

lemma paper_R_H_retraction_support_finite:
  "paper_R_H_retraction_support \<Omega> G A N \<Longrightarrow> finite N"
  unfolding paper_R_H_retraction_support_def by blast

lemma paper_R_H_retraction_support_apply:
  assumes support: "paper_R_H_retraction_support \<Omega> G A N"
    and stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
    and fresh: "\<And>\<rho>. v \<rho> \<notin> N"
  shows "paper_R_named_H \<Omega> G (named_retract \<Omega> v A)"
  using support stock fresh unfolding paper_R_H_retraction_support_def by blast

lemma paper_R_H_retraction_at_names:
  assumes transform: "\<And>v. (\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>) \<Longrightarrow>
    (\<And>\<rho>. v \<rho> \<notin> named_vars A) \<Longrightarrow> paper_R_named_H \<Omega> G (named_retract \<Omega> v A)"
  shows "\<exists>N. paper_R_H_retraction_support \<Omega> G A N"
  by (rule exI[where x="named_vars A"], rule paper_R_H_retraction_supportI[OF named_vars_finite subset_refl transform])

end
