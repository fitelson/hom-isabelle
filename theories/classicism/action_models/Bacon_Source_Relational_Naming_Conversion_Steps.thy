theory Bacon_Source_Relational_Naming_Conversion_Steps
  imports Bacon_Source_Relational_Naming_Contractions
begin

section \<open>Fresh replacement lifts through every compatible context\<close>

lemma paper_R_naming_replace_compatible:
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>M N. R M N \<Longrightarrow>
      x ` paper_R_naming_support M \<inter> named_vars M = {} \<Longrightarrow>
      Q (paper_R_naming_replace x M) (paper_R_naming_replace x N)"
    and fresh: "x ` paper_R_naming_support A \<inter> named_vars A = {}"
  shows "named_compatible_step Q (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
  using step fresh
proof (induction rule: named_compatible_step.induct)
  case (root M N)
  have contraction: "Q (paper_R_naming_replace x M) (paper_R_naming_replace x N)"
    by (rule roots[OF root.hyps root.prems])
  show ?case by (rule named_compatible_step.root[where R=Q, OF contraction])
next
  case (App_left M N C)
  have subfresh: "x ` paper_R_naming_support M \<inter> named_vars M = {}"
    using App_left.prems by auto
  show ?case by (simp only: paper_R_naming_replace.simps;
    rule named_compatible_step.App_left[OF App_left.IH[OF subfresh]])
next
  case (App_right M N C)
  have subfresh: "x ` paper_R_naming_support M \<inter> named_vars M = {}"
    using App_right.prems by auto
  show ?case by (simp only: paper_R_naming_replace.simps;
    rule named_compatible_step.App_right[OF App_right.IH[OF subfresh]])
next
  case (Lam_body M N n)
  have subfresh: "x ` paper_R_naming_support M \<inter> named_vars M = {}"
    using Lam_body.prems by auto
  show ?case by (simp only: paper_R_naming_replace.simps;
    rule named_compatible_step.Lam_body[OF Lam_body.IH[OF subfresh]])
qed

theorem paper_R_naming_replace_beta_step:
  assumes step: "named_compatible_step named_beta_contract A B"
    and fresh: "x ` paper_R_naming_support A \<inter> named_vars A = {}"
  shows "named_compatible_step named_beta_contract (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
  by (rule paper_R_naming_replace_compatible[where R=named_beta_contract and Q=named_beta_contract,
    OF step _ fresh]; rule paper_R_naming_replace_beta_contract; assumption)

theorem paper_R_naming_replace_eta_step:
  assumes step: "named_compatible_step named_eta_contract A B"
    and fresh: "x ` paper_R_naming_support A \<inter> named_vars A = {}"
  shows "named_compatible_step named_eta_contract (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
  by (rule paper_R_naming_replace_compatible[where R=named_eta_contract and Q=named_eta_contract,
    OF step _ fresh]; rule paper_R_naming_replace_eta_contract; assumption)

corollary paper_R_naming_chart_beta_step:
  assumes step: "named_compatible_step named_beta_contract A B" and chart: "paper_R_naming_chart G K N x"
    and support: "paper_R_naming_support A \<subseteq> K" and avoid: "named_vars A \<subseteq> N"
  shows "named_compatible_step named_beta_contract (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
proof (rule paper_R_naming_replace_beta_step[OF step])
  show "x ` paper_R_naming_support A \<inter> named_vars A = {}"
    using chart support avoid unfolding paper_R_naming_chart_def by blast
qed

corollary paper_R_naming_chart_eta_step:
  assumes step: "named_compatible_step named_eta_contract A B" and chart: "paper_R_naming_chart G K N x"
    and support: "paper_R_naming_support A \<subseteq> K" and avoid: "named_vars A \<subseteq> N"
  shows "named_compatible_step named_eta_contract (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
proof (rule paper_R_naming_replace_eta_step[OF step])
  show "x ` paper_R_naming_support A \<inter> named_vars A = {}"
    using chart support avoid unfolding paper_R_naming_chart_def by blast
qed

end
