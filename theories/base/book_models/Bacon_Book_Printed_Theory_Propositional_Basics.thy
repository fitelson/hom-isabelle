theory Bacon_Book_Printed_Theory_Propositional_Basics
  imports Bacon_Book_Printed_Theory_Derivation
begin

section \<open>Implication derivations using only the new PC1, PC2 and MP\<close>

text \<open>
  The printed calculus proves A→A, permits weakening a proved B to
  A→B, and chains A→B with B→C to obtain A→C.
  Source: Definition 5.1, pp.97–98. Every displayed proof below uses
  only the new judgment's PC1, PC2 and MP constructors.
  No old-calculus theorem, deduction theorem, α step, conversion chain,
  richness assumption, or model premise is used.
\<close>

lemma book_printed_theory_imp_refl:
  assumes al: "book_printed_theory_formula \<Sigma> G A"
  shows "book_printed_theory_derivable \<Sigma> G S (book_imp A A)"
proof -
  have aa: "book_printed_theory_formula \<Sigma> G (book_imp A A)"
    by (rule book_imp_language[OF al al])
  have a_aa: "book_printed_theory_formula \<Sigma> G (book_imp A (book_imp A A))"
    by (rule book_imp_language[OF al aa])
  have tail: "book_printed_theory_formula \<Sigma> G (book_imp (book_imp A (book_imp A A)) (book_imp A A))"
    by (rule book_imp_language[OF a_aa aa])
  have first: "book_printed_theory_derivable \<Sigma> G S (book_imp A (book_imp (book_imp A A) A))"
    by (rule book_printed_theory_derivable.PC1[OF al aa])
  have second: "book_printed_theory_derivable \<Sigma> G S (book_imp A (book_imp A A))"
    by (rule book_printed_theory_derivable.PC1[OF al al])
  have schema: "book_printed_theory_derivable \<Sigma> G S
    (book_imp (book_imp A (book_imp (book_imp A A) A))
      (book_imp (book_imp A (book_imp A A)) (book_imp A A)))"
    by (rule book_printed_theory_derivable.PC2[OF al aa al])
  have implication: "book_printed_theory_derivable \<Sigma> G S
    (book_imp (book_imp A (book_imp A A)) (book_imp A A))"
    by (rule book_printed_theory_derivable.MP[OF first schema tail])
  show ?thesis by (rule book_printed_theory_derivable.MP[OF second implication aa])
qed

lemma book_printed_theory_imp_weaken:
  assumes derivation: "book_printed_theory_derivable \<Sigma> G S B"
    and al: "book_printed_theory_formula \<Sigma> G A" and bl: "book_printed_theory_formula \<Sigma> G B"
  shows "book_printed_theory_derivable \<Sigma> G S (book_imp A B)"
proof -
  have schema: "book_printed_theory_derivable \<Sigma> G S (book_imp B (book_imp A B))"
    by (rule book_printed_theory_derivable.PC1[OF bl al])
  have language: "book_printed_theory_formula \<Sigma> G (book_imp A B)"
    by (rule book_imp_language[OF al bl])
  show ?thesis by (rule book_printed_theory_derivable.MP[OF derivation schema language])
qed

lemma book_printed_theory_imp_trans:
  assumes al: "book_printed_theory_formula \<Sigma> G A" and bl: "book_printed_theory_formula \<Sigma> G B"
    and cl: "book_printed_theory_formula \<Sigma> G C"
    and ab: "book_printed_theory_derivable \<Sigma> G S (book_imp A B)"
    and bc: "book_printed_theory_derivable \<Sigma> G S (book_imp B C)"
  shows "book_printed_theory_derivable \<Sigma> G S (book_imp A C)"
proof -
  have bcl: "book_printed_theory_formula \<Sigma> G (book_imp B C)" by (rule book_imp_language[OF bl cl])
  have abl: "book_printed_theory_formula \<Sigma> G (book_imp A B)" by (rule book_imp_language[OF al bl])
  have acl: "book_printed_theory_formula \<Sigma> G (book_imp A C)" by (rule book_imp_language[OF al cl])
  have tail: "book_printed_theory_formula \<Sigma> G (book_imp (book_imp A B) (book_imp A C))"
    by (rule book_imp_language[OF abl acl])
  have lifted: "book_printed_theory_derivable \<Sigma> G S (book_imp A (book_imp B C))"
    by (rule book_printed_theory_imp_weaken[OF bc al bcl])
  have schema: "book_printed_theory_derivable \<Sigma> G S
    (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)))"
    by (rule book_printed_theory_derivable.PC2[OF al bl cl])
  have implication: "book_printed_theory_derivable \<Sigma> G S (book_imp (book_imp A B) (book_imp A C))"
    by (rule book_printed_theory_derivable.MP[OF lifted schema tail])
  show ?thesis by (rule book_printed_theory_derivable.MP[OF ab implication acl])
qed

end

