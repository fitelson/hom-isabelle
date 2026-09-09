theory Bacon_Book_Environment_Substitution_Beta_Syntax
  imports Bacon_Book_Closed_Environment_Substitution
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Substitution
begin

section \<open>Inactive bound names and literal β substitution\<close>

text \<open>
  If x∉FV(A), protecting x makes no change to A[r]. With closed
  replacement terms and N free for x in A, substitution also satisfies
  A[N/x][r] = (A[r with x protected])[N[r]/x].
  Source role: literal capture-free β (Bacon, pp.97–98) in the
  representative interpretation of Theorem 15.3, p.321.

  The equality holds for every initial bound-name set B, including
  sets already containing x. At a distinct binder y, either y is
  fresh for N or x does not occur freely in that binder's body.
  Both source-permitted cases are treated explicitly. These are raw
  syntax equalities, not typed conversion or semantic assumptions.
\<close>

lemma book_environment_subst_bound_irrelevant:
  assumes fresh: "x \<notin> named_fv A"
  shows "book_environment_subst (insert x B) r A = book_environment_subst B r A"
  using fresh
proof (induction A arbitrary: B)
  case (NVar n)
  have distinct: "n \<noteq> x" using NVar.prems by simp
  show ?case by (simp add: distinct)
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have ff: "x \<notin> named_fv F" and af: "x \<notin> named_fv A"
    using NApp.prems by simp_all
  show ?case by (simp only: book_environment_subst.simps NApp.IH(1)[OF ff] NApp.IH(2)[OF af])
next
  case (NLam n A)
  show ?case
  proof (cases "n = x")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    have af: "x \<notin> named_fv A" using NLam.prems False by auto
    have commuted: "insert n (insert x B) = insert x (insert n B)" by blast
    show ?thesis by (simp only: book_environment_subst.simps commuted NLam.IH[OF af])
  qed
qed

theorem book_environment_subst_beta_commute:
  assumes closed: "\<And>n. named_fv (r n) = {}"
    and permitted: "named_free_for N x A"
  shows "book_environment_subst B r (named_subst x N A) =
    named_subst x (book_environment_subst B r N) (book_environment_subst (insert x B) r A)"
  using permitted
proof (induction A arbitrary: B)
  case (NVar n)
  show ?case
  proof (cases "n = x")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    have fresh: "x \<notin> named_fv (r n)" by (simp only: closed; simp)
    have unchanged: "named_subst x (book_environment_subst B r N) (r n) = r n"
      by (rule named_subst_fresh[OF fresh])
    show ?thesis by (cases "n \<in> B"; simp add: False unchanged)
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
  show ?case by (simp only: named_subst.simps book_environment_subst.simps
    NApp.IH(1)[OF ff] NApp.IH(2)[OF af])
next
  case (NLam y A)
  show ?case
  proof (cases "y = x")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    note binder_distinct = False
    have af: "named_free_for N x A"
      and guard: "y \<notin> named_fv N \<or> x \<notin> named_fv A"
      using NLam.prems binder_distinct by auto
    have commuted: "insert y (insert x B) = insert x (insert y B)" by blast
    show ?thesis
    proof (cases "y \<notin> named_fv N")
      case True
      have argument_same: "book_environment_subst (insert y B) r N = book_environment_subst B r N"
        by (rule book_environment_subst_bound_irrelevant[OF True])
      have body_equation: "book_environment_subst (insert y B) r (named_subst x N A) =
        named_subst x (book_environment_subst (insert y B) r N)
          (book_environment_subst (insert x (insert y B)) r A)"
        by (rule NLam.IH[OF af])
      show ?thesis by (simp only: named_subst.simps binder_distinct if_False book_environment_subst.simps
        body_equation argument_same commuted)
    next
      case False
      have absent: "x \<notin> named_fv A" using guard False by blast
      have original_fixed: "named_subst x N A = A" by (rule named_subst_fresh[OF absent])
      have bound_removed: "book_environment_subst (insert y (insert x B)) r A =
        book_environment_subst (insert y B) r A"
        by (simp only: commuted; rule book_environment_subst_bound_irrelevant[OF absent])
      have result_fresh: "x \<notin> named_fv (book_environment_subst (insert y B) r A)"
        by (simp only: book_environment_subst_fv[OF closed]; use absent in \<open>blast\<close>)
      have result_fixed: "named_subst x (book_environment_subst B r N)
        (book_environment_subst (insert y B) r A) = book_environment_subst (insert y B) r A"
        by (rule named_subst_fresh[OF result_fresh])
      show ?thesis by (simp only: named_subst.simps binder_distinct if_False book_environment_subst.simps
        original_fixed bound_removed result_fixed)
    qed
  qed
qed

end
