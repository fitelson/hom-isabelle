theory Bacon_Book_Printed_Free_For
  imports Bacon_Book_Constant_Substitution_Syntax Bacon_Book_Logical_Substitution_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Substitution
begin

section \<open>The recursive free-for test printed in Definition 3.7\<close>

text \<open>
  N is printed-free for x in λy.P precisely when it is printed-free
  for x in P and y∉FV(N). Source: Bacon, Definition 3.7, p.70.
  The printed binder clause has neither a vacuous-body exception nor
  an exception for a binder that shadows x.

  Representation. This new predicate records that literal recursive
  condition over generic named syntax. It does not change substitution
  or the existing exact-capture predicate named_free_for. As printed,
  the test depends on N and the binders of A, not on the target x;
  the x argument is retained to display its intended substitution role.
  It suffices for each of the existing variable, nonlogical-constant,
  and logical-symbol no-capture predicates. Those implications concern
  syntax only, not logical-symbol substitution in a proof calculus.
\<close>

fun book_printed_free_for ::
  "('c,'l) named_term \<Rightarrow> nat \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool" where
  "book_printed_free_for N x (NVar n) = True"
| "book_printed_free_for N x (NConst c \<sigma>) = True"
| "book_printed_free_for N x (NLogical l) = True"
| "book_printed_free_for N x (NApp F A) =
    (book_printed_free_for N x F \<and> book_printed_free_for N x A)"
| "book_printed_free_for N x (NLam y A) =
    (book_printed_free_for N x A \<and> y \<notin> named_fv N)"

lemma book_printed_free_for_target_irrelevant:
  "book_printed_free_for N x A = book_printed_free_for N y A"
  by (induction A) simp_all

theorem book_printed_free_for_named:
  assumes printed: "book_printed_free_for N x A"
  shows "named_free_for N x A"
  using printed
proof (induction A)
  case (NVar n)
  show ?case by simp
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fp: "book_printed_free_for N x F" and ap: "book_printed_free_for N x A"
    using NApp.prems by simp_all
  show ?case by (simp only: named_free_for.simps;
    rule conjI[OF NApp.IH(1)[OF fp] NApp.IH(2)[OF ap]])
next
  case (NLam y A)
  have ap: "book_printed_free_for N x A" and fresh: "y \<notin> named_fv N"
    using NLam.prems by simp_all
  have body: "named_free_for N x A" by (rule NLam.IH[OF ap])
  show ?case by (simp only: named_free_for.simps;
    rule disjI2; rule conjI[OF body disjI1[OF fresh]])
qed

lemma book_printed_free_for_constant:
  assumes printed: "book_printed_free_for N x A"
  shows "book_const_free_for N c \<sigma> A"
  using printed
proof (induction A)
  case (NVar n)
  show ?case by simp
next
  case (NConst d \<tau>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fp: "book_printed_free_for N x F" and ap: "book_printed_free_for N x A"
    using NApp.prems by simp_all
  show ?case by (simp only: book_const_free_for.simps;
    rule conjI[OF NApp.IH(1)[OF fp] NApp.IH(2)[OF ap]])
next
  case (NLam y A)
  have ap: "book_printed_free_for N x A" and fresh: "y \<notin> named_fv N"
    using NLam.prems by simp_all
  have body: "book_const_free_for N c \<sigma> A" by (rule NLam.IH[OF ap])
  show ?case by (simp only: book_const_free_for.simps;
    rule conjI[OF body]; rule impI; rule fresh)
qed

lemma book_printed_free_for_logical:
  assumes printed: "book_printed_free_for N x A"
  shows "book_logical_free_for N l A"
  using printed
proof (induction A)
  case (NVar n)
  show ?case by simp
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical k)
  show ?case by simp
next
  case (NApp F A)
  have fp: "book_printed_free_for N x F" and ap: "book_printed_free_for N x A"
    using NApp.prems by simp_all
  show ?case by (simp only: book_logical_free_for.simps;
    rule conjI[OF NApp.IH(1)[OF fp] NApp.IH(2)[OF ap]])
next
  case (NLam y A)
  have ap: "book_printed_free_for N x A" and fresh: "y \<notin> named_fv N"
    using NLam.prems by simp_all
  have body: "book_logical_free_for N l A" by (rule NLam.IH[OF ap])
  show ?case by (simp only: book_logical_free_for.simps;
    rule conjI[OF body]; rule impI; rule fresh)
qed

lemma book_printed_free_for_closed:
  assumes closed: "named_fv N = {}"
  shows "book_printed_free_for N x A"
  using closed by (induction A) simp_all

section \<open>The reverse implication fails for the raw tests\<close>

lemma book_printed_free_for_vacuous_difference:
  "named_free_for (NVar 0 :: ('c,'l) named_term) 1 (NLam 0 (NVar 2)) \<and>
    \<not> book_printed_free_for (NVar 0 :: ('c,'l) named_term) 1 (NLam 0 (NVar 2))"
  by simp

lemma book_printed_free_for_shadowed_difference:
  "named_free_for (NVar 0 :: ('c,'l) named_term) 0 (NLam 0 (NVar 0)) \<and>
    \<not> book_printed_free_for (NVar 0 :: ('c,'l) named_term) 0 (NLam 0 (NVar 0))"
  by simp

text \<open>
  The existing calculus uses the exact-capture test. To establish reverse
  correspondence with a calculus using the printed test, a further
  admissibility theorem must simulate each allowed exact-capture β step:
  α-rename obstructing binders, perform a printed-permitted β step, and
  relate its result back by α. The required typed/signature-preserving
  freshening and substitution correspondence must be proved, not inferred
  merely from α being included in source conversion (Definitions 3.9–3.10,
  pp.70/73). This leaf does not claim that bridge. The difference is a
  source-correspondence obligation, not a failure of any checked proof
  about the already defined calculus.
\<close>

end
