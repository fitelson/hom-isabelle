theory Bacon_Book_Theory_Propositional_Basics
  imports Bacon_Book_Theory_Derivation
begin

section \<open>Two elementary derivations using only PC1, PC2 and MP\<close>

text \<open>
  ⊢ A→A, and S ⊢ B implies S ⊢ A→B.
  Source: the literal propositional schemas and MP in Bacon,
  Chapter 5, pp.97–98. These are derivations, not appeals to an
  arbitrary-tautology constructor or to semantic validity.

  The formula-language guards are explicit. The premise set S and
  stock G are unchanged; no richness, model, or deduction theorem is
  assumed. Both derivations use only the printed implicational rules.
\<close>

lemma book_theory_imp_refl:
  assumes al: "book_theory_formula \<Sigma> G A"
  shows "book_theory_derivable \<Sigma> G S (book_imp A A)"
proof -
  have aa: "book_theory_formula \<Sigma> G (book_imp A A)"
    by (rule book_imp_language[OF al al])
  have a_aa: "book_theory_formula \<Sigma> G (book_imp A (book_imp A A))"
    by (rule book_imp_language[OF al aa])
  have tail: "book_theory_formula \<Sigma> G (book_imp (book_imp A (book_imp A A)) (book_imp A A))"
    by (rule book_imp_language[OF a_aa aa])
  have first: "book_theory_derivable \<Sigma> G S (book_imp A (book_imp (book_imp A A) A))"
    by (rule book_theory_derivable.PC1[OF al aa])
  have second: "book_theory_derivable \<Sigma> G S (book_imp A (book_imp A A))"
    by (rule book_theory_derivable.PC1[OF al al])
  have schema: "book_theory_derivable \<Sigma> G S
    (book_imp (book_imp A (book_imp (book_imp A A) A))
      (book_imp (book_imp A (book_imp A A)) (book_imp A A)))"
    by (rule book_theory_derivable.PC2[OF al aa al])
  have implication: "book_theory_derivable \<Sigma> G S
    (book_imp (book_imp A (book_imp A A)) (book_imp A A))"
    by (rule book_theory_derivable.MP[OF first schema tail])
  show ?thesis by (rule book_theory_derivable.MP[OF second implication aa])
qed

lemma book_theory_imp_weaken:
  assumes derivation: "book_theory_derivable \<Sigma> G S B"
    and al: "book_theory_formula \<Sigma> G A" and bl: "book_theory_formula \<Sigma> G B"
  shows "book_theory_derivable \<Sigma> G S (book_imp A B)"
proof -
  have schema: "book_theory_derivable \<Sigma> G S (book_imp B (book_imp A B))"
    by (rule book_theory_derivable.PC1[OF bl al])
  have language: "book_theory_formula \<Sigma> G (book_imp A B)"
    by (rule book_imp_language[OF al bl])
  show ?thesis by (rule book_theory_derivable.MP[OF derivation schema language])
qed

end
