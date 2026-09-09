theory Bacon_Book_Classicism_Closed_Lists
  imports Bacon_Book_Classicism_Theory_Rules
begin

section \<open>Discharge a finite list of closed additional premises\<close>

fun book_C_imp_list :: "'c book_named_term list \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_C_imp_list [] P = P"
| "book_C_imp_list (A#As) P = book_imp A (book_C_imp_list As P)"

lemma book_C_imp_list_language:
  assumes entries: "list_all (book_theory_formula \<Sigma> G) As" and conclusion: "book_theory_formula \<Sigma> G P"
  shows "book_theory_formula \<Sigma> G (book_C_imp_list As P)"
  using entries by (induction As) (auto intro: book_imp_language conclusion)

theorem book_C_theory_closed_list_deduction:
  assumes rich: "sg_rich G"
    and entries: "list_all (\<lambda>A. book_theory_formula \<Sigma> G A \<and> named_fv A = {}) As"
    and derivation: "book_C_theory_derivable \<Sigma> G (set As \<union> S) P"
  shows "book_C_theory_derivable \<Sigma> G S (book_C_imp_list As P)"
  using entries derivation
proof (induction As arbitrary: S)
  case Nil
  show ?case using Nil.prems(2) by simp
next
  case (Cons A As)
  have al: "book_theory_formula \<Sigma> G A" and ac: "named_fv A = {}"
    and tail: "list_all (\<lambda>B. book_theory_formula \<Sigma> G B \<and> named_fv B = {}) As"
    using Cons.prems(1) by simp_all
  have sets: "set (A#As) \<union> S = set As \<union> insert A S" by auto
  have reordered: "book_C_theory_derivable \<Sigma> G (set As \<union> insert A S) P"
    using Cons.prems(2) by (simp only: sets)
  have inner: "book_C_theory_derivable \<Sigma> G (insert A S) (book_C_imp_list As P)"
    by (rule Cons.IH[OF tail reordered])
  show ?case by (simp only: book_C_imp_list.simps; rule book_C_theory_closed_deduction[OF rich al ac inner])
qed

end
