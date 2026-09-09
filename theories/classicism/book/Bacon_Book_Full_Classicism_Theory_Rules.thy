theory Bacon_Book_Full_Classicism_Theory_Rules
  imports Bacon_Book_Full_Classicism_Theory_Consistency
begin

lemma book_full_C_theory_language:
  "sg_rich G \<Longrightarrow> book_full_C_theory_derivable \<Sigma> G S A \<Longrightarrow> book_theory_formula \<Sigma> G A"
  unfolding book_full_C_theory_derivable_def by (rule book_theory_derivable_language; assumption)

lemma book_full_C_theory_from_C:
  assumes rich: "sg_rich G" and theorem_C: "book_full_C_proves \<Sigma> G A"
  shows "book_full_C_theory_derivable \<Sigma> G S A"
  unfolding book_full_C_theory_derivable_def
  by (rule book_theory_derivable.Assumption; (simp add: theorem_C | rule book_full_C_proves_language[OF rich theorem_C]))

lemma book_full_C_theory_assume:
  "A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A \<Longrightarrow> book_full_C_theory_derivable \<Sigma> G S A"
  unfolding book_full_C_theory_derivable_def by (rule book_theory_derivable.Assumption; (rule UnI2 | assumption); assumption?)

lemma book_full_C_theory_MP:
  "book_full_C_theory_derivable \<Sigma> G S A \<Longrightarrow>
    book_full_C_theory_derivable \<Sigma> G S (book_imp A B) \<Longrightarrow>
    book_theory_formula \<Sigma> G B \<Longrightarrow> book_full_C_theory_derivable \<Sigma> G S B"
  unfolding book_full_C_theory_derivable_def by (rule book_theory_derivable.MP; assumption)

lemma book_full_C_theory_closed_deduction:
  assumes rich: "sg_rich G" and language: "book_theory_formula \<Sigma> G A"
    and closed: "named_fv A = {}" and derivation: "book_full_C_theory_derivable \<Sigma> G (insert A S) B"
  shows "book_full_C_theory_derivable \<Sigma> G S (book_imp A B)"
proof -
  let ?C = "{P. book_full_C_proves \<Sigma> G P}"
  have sets: "?C \<union> insert A S = insert A (?C \<union> S)" by blast
  have proof_B: "book_theory_derivable \<Sigma> G (insert A (?C \<union> S)) B"
    using derivation by (simp only: book_full_C_theory_derivable_def sets)
  show ?thesis unfolding book_full_C_theory_derivable_def
    by (rule book_theory_closed_deduction[OF rich language closed proof_B])
qed

end
