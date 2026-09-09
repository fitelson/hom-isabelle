theory Bacon_Book_Printed_Alpha_Alignment
  imports Bacon_Book_Printed_Binder_Conversion
begin

section \<open>Literal substitution and fresh swapping coincide by printed conversion\<close>

text \<open>
  For a same-type fresh y, A[y/x] converts to (x y)·A using only
  printed β and η. The paired argument is staged: alignment for a
  strict subterm supplies binder conversion for that subterm. This
  handles shadowing without assuming the desired general α theorem.
  Source role: α transport derived from the Chapter 5 schemas, p.98,
  with the literal Definition 3.7 guard. No α constructor is introduced.
\<close>

theorem book_printed_subst_swap_conversion:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and same: "G x = G y" and fresh: "y \<notin> named_vars A"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G \<tau>
    (named_subst x (NVar y) A) (named_swap x y A)"
  using language same fresh
proof (induction A arbitrary: x y \<tau>)
  case (NVar n)
  have same_term: "named_subst x (NVar y) (NVar n) = named_swap x y (NVar n)"
    using NVar.prems(3) by (auto simp: named_swap_index_def)
  have swapped: "book_in_language L \<Lambda> \<Sigma> G (named_swap x y (NVar n)) \<tau>"
    by (rule book_printed_swap_language[OF NVar.prems(1,2)])
  show ?case by (simp only: same_term; rule book_printed_conversion.Refl[OF swapped])
next
  case (NConst c \<sigma>)
  show ?case by (simp only: named_subst.simps named_swap.simps;
    rule book_printed_conversion.Refl[OF NConst.prems(1)])
next
  case (NLogical l)
  show ?case by (simp only: named_subst.simps named_swap.simps;
    rule book_printed_conversion.Refl[OF NLogical.prems(1)])
next
  case (NApp F A)
  obtain \<sigma> where fn: "book_in_language L \<Lambda> \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
    by (rule book_language_App_obtain[OF NApp.prems(1)]; rule that; assumption)
  have fresh_F: "y \<notin> named_vars F" and fresh_A: "y \<notin> named_vars A"
    using NApp.prems(3) by simp_all
  have fc: "book_printed_conversion L \<Lambda> \<Sigma> G (Arr \<sigma> \<tau>)
    (named_subst x (NVar y) F) (named_swap x y F)"
    by (rule NApp.IH(1)[OF fn NApp.prems(2) fresh_F])
  have ac: "book_printed_conversion L \<Lambda> \<Sigma> G \<sigma>
    (named_subst x (NVar y) A) (named_swap x y A)"
    by (rule NApp.IH(2)[OF argument NApp.prems(2) fresh_A])
  show ?case by (simp only: named_subst.simps named_swap.simps;
    rule book_printed_conversion_App[OF fc ac])
next
  case (NLam n A)
  obtain \<rho> where ty: "\<tau> = Arr (G n) \<rho>"
    and body: "book_in_language L \<Lambda> \<Sigma> G A \<rho>"
    by (rule book_language_Lam_obtain[OF NLam.prems(1)]; rule that; assumption)
  have fresh_body: "y \<notin> named_vars A" and not_y: "n \<noteq> y"
    using NLam.prems(3) by auto
  have aligned: "book_printed_conversion L \<Lambda> \<Sigma> G \<rho>
    (named_subst x (NVar y) A) (named_swap x y A)"
    by (rule NLam.IH[OF body NLam.prems(2) fresh_body])
  show ?case
  proof (cases "n = x")
    case True
    have shadow: "book_printed_conversion L \<Lambda> \<Sigma> G (Arr (G x) \<rho>)
      (NLam x A) (NLam y (named_swap x y A))"
      by (rule book_printed_binder_from_alignment[OF body NLam.prems(2) fresh_body aligned])
    show ?thesis using shadow by (simp add: ty True)
  next
    case False
    have binder_index: "named_swap_index x y n = n"
      by (simp only: named_swap_index_def False not_y if_False)
    have under_binder: "book_printed_conversion L \<Lambda> \<Sigma> G (Arr (G n) \<rho>)
      (NLam n (named_subst x (NVar y) A)) (NLam n (named_swap x y A))"
      by (rule book_printed_conversion_Lam[OF aligned])
    show ?thesis using under_binder
      by (simp only: ty named_subst.simps False if_False named_swap.simps binder_index)
  qed
qed

corollary book_printed_fresh_binder_conversion:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and same: "G x = G y" and fresh: "y \<notin> named_vars A"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G (Arr (G x) \<tau>)
    (NLam x A) (NLam y (named_swap x y A))"
  by (rule book_printed_binder_from_alignment[OF language same fresh
    book_printed_subst_swap_conversion[OF language same fresh]])

end
