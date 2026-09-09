theory Bacon_Book_Contextual_Reduction_Language
  imports Bacon_Book_Reduction_Language
begin

section \<open>Language preservation lifts through every term context\<close>

text \<open>
  A root step preserving the type and declared symbols of its input also
  preserves them under application and abstraction contexts. The induction
  generalizes the result type, so the head of an application may have a
  higher type than the whole expression. No reverse reduction, semantics,
  or admitted-sublanguage closure is assumed.
\<close>

lemma book_compatible_step_language:
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>M N \<rho>. R M N \<Longrightarrow> book_in_language L \<Lambda> \<Sigma> G M \<rho>
      \<Longrightarrow> book_in_language L \<Lambda> \<Sigma> G N \<rho>"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_in_language L \<Lambda> \<Sigma> G B \<tau>"
  using step language
proof (induction arbitrary: \<tau> rule: named_compatible_step.induct)
  case (root M N)
  show ?case by (rule roots[OF root.hyps root.prems])
next
  case (App_left M M' N)
  obtain \<sigma> where head: "book_in_language L \<Lambda> \<Sigma> G M (Arr \<sigma> \<tau>)"
    and argument: "book_in_language L \<Lambda> \<Sigma> G N \<sigma>"
    by (rule book_language_App_obtain[OF App_left.prems]; rule that; assumption)
  show ?case by (rule book_language_App[OF App_left.IH[OF head] argument])
next
  case (App_right N N' M)
  obtain \<sigma> where head: "book_in_language L \<Lambda> \<Sigma> G M (Arr \<sigma> \<tau>)"
    and argument: "book_in_language L \<Lambda> \<Sigma> G N \<sigma>"
    by (rule book_language_App_obtain[OF App_right.prems]; rule that; assumption)
  show ?case by (rule book_language_App[OF head App_right.IH[OF argument]])
next
  case (Lam_body M M' n)
  obtain \<rho> where arrow: "\<tau> = Arr (G n) \<rho>"
    and body: "book_in_language L \<Lambda> \<Sigma> G M \<rho>"
    by (rule book_language_Lam_obtain[OF Lam_body.prems]; rule that; assumption)
  show ?case by (simp only: arrow; rule book_language_Lam[OF Lam_body.IH[OF body]])
qed

theorem book_beta_step_language:
  assumes step: "named_compatible_step named_beta_contract A B"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_in_language L \<Lambda> \<Sigma> G B \<tau>"
  by (rule book_compatible_step_language[OF step _ language]; rule book_beta_contract_language; assumption)

theorem book_eta_step_language:
  assumes step: "named_compatible_step named_eta_contract A B"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_in_language L \<Lambda> \<Sigma> G B \<tau>"
  by (rule book_compatible_step_language[OF step _ language]; rule book_eta_contract_language; assumption)

end
