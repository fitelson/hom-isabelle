theory Bacon_Book_Classicism_Boxed_Lists
  imports Bacon_Book_Classicism_Closed_Lists Bacon_Book_Classicism_Normal_K
begin

section \<open>Iterated K in ordinary theory consequence over C\<close>

theorem book_C_theory_boxed_list_MP:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P"
    and entries: "list_all (book_theory_formula \<Sigma> G) As"
    and implication: "book_C_theory_derivable \<Sigma> G S (book_box G (book_C_imp_list As P))"
    and boxed: "\<And>A. A \<in> set As \<Longrightarrow> book_C_theory_derivable \<Sigma> G S (book_box G A)"
  shows "book_C_theory_derivable \<Sigma> G S (book_box G P)"
  using entries implication boxed
proof (induction As)
  case Nil
  show ?case using Nil.prems(2) by simp
next
  case (Cons A As)
  let ?Q = "book_C_imp_list As P"
  have al: "book_theory_formula \<Sigma> G A" and tail: "list_all (book_theory_formula \<Sigma> G) As"
    using Cons.prems(1) by simp_all
  have ql: "book_theory_formula \<Sigma> G ?Q" by (rule book_C_imp_list_language[OF tail pl])
  have ba: "book_theory_formula \<Sigma> G (book_box G A)" by (rule book_box_language[OF rich al])
  have bq: "book_theory_formula \<Sigma> G (book_box G ?Q)" by (rule book_box_language[OF rich ql])
  have K: "book_C_theory_derivable \<Sigma> G S (book_K_formula G A ?Q)"
    by (rule book_C_theory_from_C[OF rich book_C_normal_K[OF rich al ql]])
  have first: "book_C_theory_derivable \<Sigma> G S (book_box G (book_imp A ?Q))"
    using Cons.prems(2) by simp
  have conditional: "book_C_theory_derivable \<Sigma> G S (book_imp (book_box G A) (book_box G ?Q))"
    by (rule book_C_theory_MP[OF first _ book_imp_language[OF ba bq]]; use K in \<open>simp only: book_K_formula_def\<close>)
  have head: "book_C_theory_derivable \<Sigma> G S (book_box G A)" by (rule Cons.prems(3); simp)
  have remaining: "book_C_theory_derivable \<Sigma> G S (book_box G ?Q)"
    by (rule book_C_theory_MP[OF head conditional bq])
  show ?case by (rule Cons.IH[OF tail remaining]; rule Cons.prems(3); simp)
qed

end
