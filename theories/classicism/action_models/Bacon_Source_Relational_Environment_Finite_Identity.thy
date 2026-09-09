theory Bacon_Source_Relational_Environment_Finite_Identity
  imports Bacon_Source_Relational_Environment_Update_Identity
begin

section \<open>Finite coordinate replacement between closed term assignments\<close>

definition paper_R_environment_paste :: "nat set \<Rightarrow> 'a named_assignment \<Rightarrow> 'a named_assignment \<Rightarrow> 'a named_assignment" where
  "paper_R_environment_paste K r s n = (if n \<in> K then s n else r n)"

lemma paper_R_environment_paste_empty:
  "paper_R_environment_paste {} r s = r"
  by (rule ext; simp add: paper_R_environment_paste_def)

lemma paper_R_environment_paste_insert:
  "paper_R_environment_paste (insert x K) r s = (paper_R_environment_paste K r s)(x := s x)"
  by (rule ext; auto simp: paper_R_environment_paste_def)

lemma paper_R_closed_term_assignment_paste:
  assumes first: "paper_R_closed_term_assignment \<Omega> G r" and second: "paper_R_closed_term_assignment \<Omega> G s"
  shows "paper_R_closed_term_assignment \<Omega> G (paper_R_environment_paste K r s)"
  using first second unfolding paper_R_closed_term_assignment_def paper_R_environment_paste_def by auto

theorem paper_R_environment_subst_finite_identity:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Omega> G A \<rho>"
    and first: "paper_R_closed_term_assignment \<Omega> G r" and second: "paper_R_closed_term_assignment \<Omega> G s"
    and domains: "dom r = dom s"
    and coordinates: "\<And>x B C. r x = Some B \<Longrightarrow> s x = Some C \<Longrightarrow>
      paper_R_named_derivable \<Omega> G S (named_paper_eq (G x) B C)"
    and finite: "finite K"
  shows "paper_R_named_derivable \<Omega> G S (named_paper_eq \<rho>
    (paper_R_environment_subst r A) (paper_R_environment_subst (paper_R_environment_paste K r s) A))"
  using finite
proof (induction K rule: finite_induct)
  case empty
  show ?case by (simp only: paper_R_environment_paste_empty;
    rule paper_R_named_identity_refl[OF paper_R_environment_subst_language[OF language first]])
next
  case (insert x K)
  let ?p = "paper_R_environment_paste K r s"
  let ?q = "paper_R_environment_paste (insert x K) r s"
  have pt: "paper_R_closed_term_assignment \<Omega> G ?p" by (rule paper_R_closed_term_assignment_paste[OF first second])
  have qt: "paper_R_closed_term_assignment \<Omega> G ?q" by (rule paper_R_closed_term_assignment_paste[OF first second])
  have pl: "paper_R_in_language \<Omega> G (paper_R_environment_subst ?p A) \<rho>"
    by (rule paper_R_environment_subst_language[OF language pt])
  have ql: "paper_R_in_language \<Omega> G (paper_R_environment_subst ?q A) \<rho>"
    by (rule paper_R_environment_subst_language[OF language qt])
  have step: "paper_R_named_derivable \<Omega> G S (named_paper_eq \<rho>
    (paper_R_environment_subst ?p A) (paper_R_environment_subst ?q A))"
  proof (cases "s x")
    case None
    have no_s: "x \<notin> dom s" using None by (simp add: dom_def)
    have no_r: "x \<notin> dom r" by (simp only: domains; rule no_s)
    have rx: "r x = None" using no_r by (auto simp: dom_def)
    have same: "?q = ?p" by (rule ext; auto simp: paper_R_environment_paste_def None rx)
    show ?thesis by (simp only: same; rule paper_R_named_identity_refl[OF pl])
  next
    case (Some C)
    have in_s: "x \<in> dom s" using Some by (simp add: dom_def)
    have in_r: "x \<in> dom r" by (simp only: domains; rule in_s)
    obtain B where rx: "r x = Some B" using in_r by (auto simp: dom_def)
    have bc: "B \<in> paper_R_closed_terms \<Omega> G (G x)" by (rule paper_R_closed_term_assignmentD[OF first rx])
    have cc: "C \<in> paper_R_closed_terms \<Omega> G (G x)" by (rule paper_R_closed_term_assignmentD[OF second Some])
    have equality: "paper_R_named_derivable \<Omega> G S (named_paper_eq (G x) B C)"
      by (rule coordinates[OF rx Some])
    have px: "?p x = Some B" by (simp add: paper_R_environment_paste_def insert.hyps(2) rx)
    have old_update: "?p(x := Some B) = ?p" by (rule ext; auto simp: px)
    have new_update: "?q = ?p(x := Some C)" by (simp only: paper_R_environment_paste_insert Some)
    have changed: "paper_R_named_derivable \<Omega> G S (named_paper_eq \<rho>
      (paper_R_environment_subst (?p(x := Some B)) A) (paper_R_environment_subst (?p(x := Some C)) A))"
      by (rule paper_R_environment_subst_update_identity[OF rich language pt bc cc equality])
    show ?thesis using changed by (simp only: old_update new_update)
  qed
  show ?case by (rule paper_R_named_identity_trans[
    OF rich paper_R_environment_subst_language[OF language first] pl ql insert.IH step])
qed

section \<open>Finite free-variable support gives identity for the whole substitution\<close>

text \<open>
  Corresponding defined payloads need only be locally derivably equal.
  Change the finitely many coordinates in FV(A), then use raw environment
  locality to identify the resulting substitution with Env(s,A).
  Undefined coordinates match because the two assignment domains agree.
  Source: representative independence in Theorem 3.2, footnote 64.
  No adequacy, Henkin or semantic model premise is needed for this
  derivable identity; residual open variables are permitted.
\<close>

theorem paper_R_environment_subst_assignment_identity:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Omega> G A \<rho>"
    and first: "paper_R_closed_term_assignment \<Omega> G r" and second: "paper_R_closed_term_assignment \<Omega> G s"
    and domains: "dom r = dom s"
    and coordinates: "\<And>x B C. r x = Some B \<Longrightarrow> s x = Some C \<Longrightarrow>
      paper_R_named_derivable \<Omega> G S (named_paper_eq (G x) B C)"
  shows "paper_R_named_derivable \<Omega> G S
    (named_paper_eq \<rho> (paper_R_environment_subst r A) (paper_R_environment_subst s A))"
proof -
  have finite_result: "paper_R_named_derivable \<Omega> G S (named_paper_eq \<rho>
    (paper_R_environment_subst r A) (paper_R_environment_subst (paper_R_environment_paste (named_fv A) r s) A))"
    by (rule paper_R_environment_subst_finite_identity[OF rich language first second domains coordinates named_fv_finite])
  have local: "paper_R_environment_subst (paper_R_environment_paste (named_fv A) r s) A =
    paper_R_environment_subst s A"
    by (rule paper_R_environment_subst_locality; simp add: paper_R_environment_paste_def)
  show ?thesis using finite_result by (simp only: local)
qed

end
