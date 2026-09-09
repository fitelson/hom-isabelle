theory Bacon_Source_Relational_Environment_Contractions
  imports Bacon_Source_Relational_Environment_Beta_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Conversion_Steps
begin

section \<open>Closed assigned payloads preserve the exact free-for guard\<close>

lemma paper_R_environment_subst_free_for:
  assumes closed: "\<And>n B. r n = Some B \<Longrightarrow> named_fv B = {}"
    and permitted: "named_free_for N x A" and fewer: "named_fv P \<subseteq> named_fv N"
  shows "named_free_for P x (paper_R_environment_subst r A)"
  using permitted closed
proof (induction A arbitrary: r)
  case (NVar n)
  show ?case
  proof (cases "r n")
    case None
    show ?thesis by (simp add: None)
  next
    case (Some B)
    have empty: "named_fv B = {}" by (rule NVar.prems(2)[OF Some])
    have fresh: "x \<notin> named_fv B" by (simp only: empty; simp)
    show ?thesis by (simp only: paper_R_environment_subst.simps Some option.case; rule named_free_for_fresh[OF fresh])
  qed
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have ff: "named_free_for N x F" and af: "named_free_for N x A" using NApp.prems(1) by simp_all
  show ?case by (simp only: paper_R_environment_subst.simps named_free_for.simps;
    rule conjI[OF NApp.IH(1)[OF ff NApp.prems(2)] NApp.IH(2)[OF af NApp.prems(2)]])
next
  case (NLam y A)
  show ?case
  proof (cases "y = x")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    have af: "named_free_for N x A" and guard: "y \<notin> named_fv N \<or> x \<notin> named_fv A"
      using NLam.prems(1) False by auto
    have body_closed: "\<And>n B. (r(y := None)) n = Some B \<Longrightarrow> named_fv B = {}"
      by (rule paper_R_environment_closed_delete[where r=r and n=y, OF NLam.prems(2)]; assumption)
    have body_free: "named_free_for P x (paper_R_environment_subst (r(y := None)) A)"
      by (rule NLam.IH[OF af body_closed])
    have support: "named_fv (paper_R_environment_subst (r(y := None)) A) \<subseteq> named_fv A"
      by (rule paper_R_environment_subst_fv_subset; rule body_closed; assumption)
    have transformed_guard: "y \<notin> named_fv P \<or> x \<notin> named_fv (paper_R_environment_subst (r(y := None)) A)"
      using guard fewer support by blast
    show ?thesis using False body_free transformed_guard
      by (simp only: paper_R_environment_subst.simps named_free_for.simps; blast)
  qed
qed

lemma paper_R_environment_subst_beta_free_for:
  assumes closed: "\<And>n B. r n = Some B \<Longrightarrow> named_fv B = {}"
    and permitted: "named_free_for N x A"
  shows "named_free_for (paper_R_environment_subst r N) x (paper_R_environment_subst (r(x := None)) A)"
proof -
  have body_closed: "\<And>n B. (r(x := None)) n = Some B \<Longrightarrow> named_fv B = {}"
    by (rule paper_R_environment_closed_delete[where r=r and n=x, OF closed]; assumption)
  have fewer: "named_fv (paper_R_environment_subst r N) \<subseteq> named_fv N"
    by (rule paper_R_environment_subst_fv_subset[OF closed])
  show ?thesis by (rule paper_R_environment_subst_free_for[OF body_closed permitted fewer])
qed

section \<open>Preservation of literal β and η root contractions\<close>

text \<open>
  The β result uses the exact interchange equation, with the contracted
  variable deleted from the body assignment. The η result uses deletion
  irrelevance for the fresh variable and FV(new)⊆FV(old). Undefined
  entries remain variables; no total completion or all-variable closed
  replacement hypothesis is introduced. Source: Figure 2, p.8.
\<close>

theorem paper_R_environment_subst_beta_contract:
  assumes closed: "\<And>n B. r n = Some B \<Longrightarrow> named_fv B = {}"
    and step: "named_beta_contract A C"
  shows "named_beta_contract (paper_R_environment_subst r A) (paper_R_environment_subst r C)"
  using step
proof (induction rule: named_beta_contract.induct)
  case (beta N x A)
  have permitted: "named_free_for (paper_R_environment_subst r N) x (paper_R_environment_subst (r(x := None)) A)"
    by (rule paper_R_environment_subst_beta_free_for[OF closed beta.hyps])
  have contraction: "named_beta_contract
      (NApp (NLam x (paper_R_environment_subst (r(x := None)) A)) (paper_R_environment_subst r N))
      (named_subst x (paper_R_environment_subst r N) (paper_R_environment_subst (r(x := None)) A))"
    by (rule named_beta_contract.beta[OF permitted])
  show ?case by (simp only: paper_R_environment_subst.simps paper_R_environment_subst_beta_commute[OF closed beta.hyps];
    rule contraction)
qed

theorem paper_R_environment_subst_eta_contract:
  assumes closed: "\<And>n B. r n = Some B \<Longrightarrow> named_fv B = {}"
    and step: "named_eta_contract A C"
  shows "named_eta_contract (paper_R_environment_subst r A) (paper_R_environment_subst r C)"
  using step
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  have same: "paper_R_environment_subst (r(x := None)) F = paper_R_environment_subst r F"
    by (rule paper_R_environment_subst_delete_fresh[OF eta.hyps])
  have support: "named_fv (paper_R_environment_subst r F) \<subseteq> named_fv F"
    by (rule paper_R_environment_subst_fv_subset; rule closed; assumption)
  have fresh: "x \<notin> named_fv (paper_R_environment_subst r F)"
    using eta.hyps support by blast
  have contraction: "named_eta_contract (NLam x (NApp (paper_R_environment_subst r F) (NVar x)))
      (paper_R_environment_subst r F)"
    by (rule named_eta_contract.eta[OF fresh])
  show ?case by (simp add: same; rule contraction)
qed

end
