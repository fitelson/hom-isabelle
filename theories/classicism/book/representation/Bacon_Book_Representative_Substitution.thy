theory Bacon_Book_Representative_Substitution
  imports Bacon_Book_Term_Environment
begin

section \<open>Changing one closed representative under arbitrary binders\<close>

lemma book_environment_subst_unprotect:
  assumes closed: "\<And>n. named_fv (r n) = {}" and unprotected: "x \<notin> B"
  shows "named_subst x N (book_environment_subst (insert x B) r A) =
    book_environment_subst B (r(x := N)) A"
  using unprotected
proof (induction A arbitrary: B)
  case (NVar n)
  have fixed: "named_subst x N (r n) = r n"
    by (rule named_subst_fresh; simp only: closed; simp)
  show ?case using NVar.prems
    by (cases "n = x"; cases "n \<in> B"; simp add: fixed)
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  show ?case by (simp only: book_environment_subst.simps named_subst.simps
    NApp.IH(1)[OF NApp.prems] NApp.IH(2)[OF NApp.prems])
next
  case (NLam n A)
  show ?case
  proof (cases "n = x")
    case True
    have same: "book_environment_subst (insert x B) r A =
      book_environment_subst (insert x B) (r(x := N)) A"
      by (rule book_environment_subst_locality; simp)
    show ?thesis using same by (simp add: True fun_upd_def)
  next
    case False
    have fresh: "x \<notin> insert n B" using False NLam.prems by simp
    have swapped: "insert n (insert x B) = insert x (insert n B)" by blast
    show ?thesis by (simp only: book_environment_subst.simps named_subst.simps False if_False
      swapped NLam.IH[OF fresh])
  qed
qed

lemma book_closed_environment_instance:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and replacements: "\<And>n. r n \<in> book_closed_terms \<Sigma> G (G n)"
  shows "book_environment_subst {} r A \<in> book_closed_terms \<Sigma> G \<tau>"
proof (rule book_closed_termsI)
  show "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_environment_subst {} r A) \<tau>"
    by (rule book_environment_subst_language[OF language]; rule book_closed_terms_language[OF replacements])
  show "named_fv (book_environment_subst {} r A) = {}"
    by (rule book_environment_subst_closed; rule book_closed_terms_closed[OF replacements])
qed

lemma book_closed_environment_abstraction:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and replacements: "\<And>n. r n \<in> book_closed_terms \<Sigma> G (G n)"
  shows "NLam x (book_environment_subst {x} r A) \<in> book_closed_terms \<Sigma> G (Arr (G x) \<tau>)"
  using book_closed_environment_instance[OF book_language_Lam[where n=x, OF language] replacements]
  by (simp only: book_environment_subst.simps)

text \<open>
  A[r(x:=N)] is literally the result of substituting N for x in
  the body in which x was protected. All other payloads are closed,
  so the second substitution cannot alter their free occurrences.
  The equation holds under nested and repeated binders. Typing and
  closedness of the resulting instance and of its single abstraction
  are supplied separately; no identity or semantic premise is assumed.
\<close>

end
