theory Bacon_Book_Environment_Substitution_Contractions
  imports Bacon_Book_Environment_Substitution_Beta_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Conversion_Steps
begin

section \<open>Closed replacement preserves the literal free-for proviso\<close>

text \<open>
  If N is free for x in A and FV(P)⊆FV(N), then P remains free
  for x in A[r], when every r(n) is closed. Existing binder guards
  are preserved because substitution can only remove original free
  variables. A newly inserted closed term contains no free occurrence
  of x at which the subsequent replacement could act.
  Source role: the literal no-capture condition on β in Bacon,
  pp.97–98, for the representative operation used on p.321.

  These are untyped raw-syntax lemmas with explicit closed-payload
  hypotheses. The final theorems preserve individual β and η root
  contractions, not an assumed semantic equality or a full typed
  conversion relation. No Functionality or model premise is present.
\<close>

lemma book_environment_subst_free_for:
  assumes closed: "\<And>n. named_fv (r n) = {}"
    and permitted: "named_free_for N x A"
    and fewer_names: "named_fv P \<subseteq> named_fv N"
  shows "named_free_for P x (book_environment_subst B r A)"
  using permitted
proof (induction A arbitrary: B)
  case (NVar n)
  show ?case
  proof (cases "n \<in> B")
    case True
    show ?thesis by (simp only: book_environment_subst.simps True if_True named_free_for.simps)
  next
    case False
    have fresh: "x \<notin> named_fv (r n)" by (simp only: closed; simp)
    have free: "named_free_for P x (r n)" by (rule named_free_for_fresh[OF fresh])
    show ?thesis by (simp only: book_environment_subst.simps False if_False; rule free)
  qed
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have ff: "named_free_for N x F" and af: "named_free_for N x A"
    using NApp.prems by simp_all
  show ?case by (simp only: book_environment_subst.simps named_free_for.simps;
    rule conjI[OF NApp.IH(1)[OF ff] NApp.IH(2)[OF af]])
next
  case (NLam y A)
  show ?case
  proof (cases "y = x")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    have af: "named_free_for N x A"
      and guard: "y \<notin> named_fv N \<or> x \<notin> named_fv A"
      using NLam.prems False by auto
    have body_free: "named_free_for P x (book_environment_subst (insert y B) r A)"
      by (rule NLam.IH[OF af])
    have transformed_guard: "y \<notin> named_fv P \<or>
      x \<notin> named_fv (book_environment_subst (insert y B) r A)"
      using guard fewer_names by (simp only: book_environment_subst_fv[OF closed]; blast)
    show ?thesis by (simp only: book_environment_subst.simps named_free_for.simps;
      rule disjI2; rule conjI[OF body_free transformed_guard])
  qed
qed

corollary book_environment_subst_beta_free_for:
  assumes closed: "\<And>n. named_fv (r n) = {}"
    and permitted: "named_free_for N x A"
  shows "named_free_for (book_environment_subst B r N) x
    (book_environment_subst (insert x B) r A)"
proof -
  have fewer_names: "named_fv (book_environment_subst B r N) \<subseteq> named_fv N"
    by (simp only: book_environment_subst_fv[OF closed]; rule Int_lower1)
  show ?thesis by (rule book_environment_subst_free_for[OF closed permitted fewer_names])
qed

section \<open>Raw β and η root contractions are preserved\<close>

theorem book_environment_subst_beta_contract:
  assumes closed: "\<And>n. named_fv (r n) = {}"
    and step: "named_beta_contract A C"
  shows "named_beta_contract (book_environment_subst B r A) (book_environment_subst B r C)"
  using step
proof (induction rule: named_beta_contract.induct)
  case (beta N x A)
  have permitted: "named_free_for (book_environment_subst B r N) x
    (book_environment_subst (insert x B) r A)"
    by (rule book_environment_subst_beta_free_for[OF closed beta.hyps])
  have contraction: "named_beta_contract
    (NApp (NLam x (book_environment_subst (insert x B) r A)) (book_environment_subst B r N))
    (named_subst x (book_environment_subst B r N) (book_environment_subst (insert x B) r A))"
    by (rule named_beta_contract.beta[OF permitted])
  show ?case by (simp only: book_environment_subst.simps
    book_environment_subst_beta_commute[OF closed beta.hyps]; rule contraction)
qed

theorem book_environment_subst_eta_contract:
  assumes closed: "\<And>n. named_fv (r n) = {}"
    and step: "named_eta_contract A C"
  shows "named_eta_contract (book_environment_subst B r A) (book_environment_subst B r C)"
  using step
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  have same_head: "book_environment_subst (insert x B) r F = book_environment_subst B r F"
    by (rule book_environment_subst_bound_irrelevant[OF eta.hyps])
  have fresh: "x \<notin> named_fv (book_environment_subst B r F)"
    using eta.hyps by (simp only: book_environment_subst_fv[OF closed]; blast)
  have contraction: "named_eta_contract
    (NLam x (NApp (book_environment_subst B r F) (NVar x))) (book_environment_subst B r F)"
    by (rule named_eta_contract.eta[OF fresh])
  show ?case by (simp add: same_head; rule contraction)
qed

end
