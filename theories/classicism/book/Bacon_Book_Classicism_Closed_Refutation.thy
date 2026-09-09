theory Bacon_Book_Classicism_Closed_Refutation
  imports Bacon_Book_Classicism_Theory_Consistency
begin

section \<open>The closed negative extension needed for canonical successors\<close>

theorem book_C_theory_closed_refutation:
  assumes rich: "sg_rich G" and language: "book_theory_formula \<Sigma> G A"
    and closed: "named_fv A = {}"
    and contradiction: "book_C_theory_derivable \<Sigma> G (insert (book_not G A) S) (book_bottom G)"
  shows "book_C_theory_derivable \<Sigma> G S A"
proof -
  let ?C = "{B. book_C_proves \<Sigma> G B}"
  have sets: "?C \<union> insert (book_not G A) S = insert (book_not G A) (?C \<union> S)" by blast
  have base: "book_theory_derivable \<Sigma> G (insert (book_not G A) (?C \<union> S)) (book_bottom G)"
    using contradiction by (simp only: book_C_theory_derivable_def sets)
  show ?thesis unfolding book_C_theory_derivable_def
    by (rule book_theory_closed_refutation[OF rich language closed base])
qed

corollary book_C_theory_consistent_negative_extension:
  assumes rich: "sg_rich G" and language: "book_theory_formula \<Sigma> G A"
    and closed: "named_fv A = {}" and missing: "\<not> book_C_theory_derivable \<Sigma> G S A"
  shows "book_C_theory_consistent \<Sigma> G (insert (book_not G A) S)"
  using book_C_theory_closed_refutation[OF rich language closed] missing
  unfolding book_C_theory_consistent_def by blast

text \<open>
  This is the refutation step in Proposition 18.3, p.399, now in the
  book's own full-F/minimal language. If A is not derivable from a
  successor seed over C, adding ¬A leaves that seed consistent.
  Closedness of A is explicit: the book's global-theory deduction
  rule is not an unrestricted open-assumption deduction theorem.

  No successor world is assumed or constructed here. One must still
  establish the modal lifting step for the unboxed seed, and supply
  negation/witness completion in a suitable expanded language.
\<close>

end
