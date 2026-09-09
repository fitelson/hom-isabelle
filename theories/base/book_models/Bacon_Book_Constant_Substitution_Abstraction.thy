theory Bacon_Book_Constant_Substitution_Abstraction
  imports Bacon_Book_Constant_Substitution_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Substitution
begin

section \<open>A fresh variable marker for constant substitution\<close>

text \<open>
  Choose x outside all variable names of A. Then replacing c:σ by x,
  followed by literal substitution of B for x, yields A[B/cσ]. Moreover,
  the constant-replacement capture condition makes B free for x in this
  intermediate term. Source: the capture-free replacement requirement in
  Bacon's Definition 5.2, p.99.

  Representation. Freshness concerns named_vars A, including its binders,
  not just FV(A). No condition excludes x from B: neither substitution
  recurses into its replacement. These lemmas do not choose x, assume a
  rich stock, or prove closure of a theory under constant substitution.
\<close>

lemma book_const_abstract_fv:
  assumes fresh: "x \<notin> named_vars A"
  shows "x \<in> named_fv (book_const_subst c \<sigma> (NVar x) A) \<longleftrightarrow> book_const_occurs c \<sigma> A"
  using fresh by (induction A) (auto split: if_splits)

theorem book_const_abstract_instantiate:
  assumes fresh: "x \<notin> named_vars A"
  shows "named_subst x B (book_const_subst c \<sigma> (NVar x) A) = book_const_subst c \<sigma> B A"
  using fresh
proof (induction A)
  case (NVar n)
  have distinct: "n \<noteq> x" using NVar.prems by simp
  show ?case by (simp only: book_const_subst.simps named_subst.simps distinct if_False)
next
  case (NConst d \<tau>)
  show ?case by (simp split: if_splits)
next
  case (NLogical l)
  show ?case by (simp only: book_const_subst.simps named_subst.simps)
next
  case (NApp F A)
  have fresh_F: "x \<notin> named_vars F" and fresh_A: "x \<notin> named_vars A"
    using NApp.prems by simp_all
  show ?case by (simp only: book_const_subst.simps named_subst.simps
      NApp.IH(1)[OF fresh_F] NApp.IH(2)[OF fresh_A])
next
  case (NLam n A)
  have distinct: "n \<noteq> x" and fresh_A: "x \<notin> named_vars A"
    using NLam.prems by auto
  show ?case by (simp only: book_const_subst.simps named_subst.simps distinct if_False NLam.IH[OF fresh_A])
qed

lemma book_const_abstract_free_for_iff:
  assumes fresh: "x \<notin> named_vars A"
  shows "named_free_for B x (book_const_subst c \<sigma> (NVar x) A) \<longleftrightarrow> book_const_free_for B c \<sigma> A"
  using fresh
proof (induction A)
  case (NVar n)
  show ?case by simp
next
  case (NConst d \<tau>)
  show ?case by (simp split: if_splits)
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fresh_F: "x \<notin> named_vars F" and fresh_A: "x \<notin> named_vars A"
    using NApp.prems by simp_all
  show ?case by (simp only: book_const_subst.simps named_free_for.simps book_const_free_for.simps
      NApp.IH(1)[OF fresh_F] NApp.IH(2)[OF fresh_A])
next
  case (NLam n A)
  have distinct: "n \<noteq> x" and fresh_A: "x \<notin> named_vars A"
    using NLam.prems by auto
  have marker: "x \<in> named_fv (book_const_subst c \<sigma> (NVar x) A) \<longleftrightarrow> book_const_occurs c \<sigma> A"
    by (rule book_const_abstract_fv[OF fresh_A])
  show ?case by (auto simp: distinct NLam.IH[OF fresh_A] marker)
qed

theorem book_const_abstract_free_for:
  assumes fresh: "x \<notin> named_vars A"
    and free_for: "book_const_free_for B c \<sigma> A"
  shows "named_free_for B x (book_const_subst c \<sigma> (NVar x) A)"
  by (simp only: book_const_abstract_free_for_iff[OF fresh]; rule free_for)

end
