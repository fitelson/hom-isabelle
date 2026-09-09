theory Bacon_Book_Printed_Theory_Conversion
  imports Bacon_Book_Printed_Theory_Propositional_Basics Bacon_Book_Printed_Conversion_Correspondence
begin

section \<open>Printed conversion chains yield two derivable implications\<close>

text \<open>
  Printed βη-equivalent formulas imply one another in the independently
  defined printed calculus. The paired induction handles symmetry by
  exchanging the two implications, and transitivity by PC1/PC2/MP.
  No conversion-chain or α constructor is added to the calculus.
  Source: the immediate schemas of Chapter 5, pp.97–98.
\<close>

theorem book_printed_theory_conversion_pair:
  assumes conversion: "book_printed_conversion book_minimal_logical_type UNIV \<Sigma> G \<tau> A B"
    and proposition_type: "\<tau> = Prop"
  shows "book_printed_theory_derivable \<Sigma> G S (book_imp A B) \<and>
    book_printed_theory_derivable \<Sigma> G S (book_imp B A)"
  using conversion proposition_type
proof (induction rule: book_printed_conversion.induct)
  case (Refl A \<tau>)
  have al: "book_printed_theory_formula \<Sigma> G A" using Refl.hyps by (simp only: Refl.prems)
  show ?case by (rule conjI; rule book_printed_theory_imp_refl[OF al])
next
  case (PrintedBeta A \<tau> B)
  have al: "book_printed_theory_formula \<Sigma> G A" using PrintedBeta.hyps(1) by (simp only: PrintedBeta.prems)
  have bl: "book_printed_theory_formula \<Sigma> G B" using PrintedBeta.hyps(2) by (simp only: PrintedBeta.prems)
  have forward: "book_printed_theory_derivable \<Sigma> G S (book_imp A B)"
    by (rule book_printed_theory_derivable.Beta[OF al bl], rule disjI1, rule PrintedBeta.hyps(3))
  have backward: "book_printed_theory_derivable \<Sigma> G S (book_imp B A)"
    by (rule book_printed_theory_derivable.Beta[OF bl al], rule disjI2, rule PrintedBeta.hyps(3))
  show ?case by (rule conjI[OF forward backward])
next
  case (Eta A \<tau> B)
  have al: "book_printed_theory_formula \<Sigma> G A" using Eta.hyps(1) by (simp only: Eta.prems)
  have bl: "book_printed_theory_formula \<Sigma> G B" using Eta.hyps(2) by (simp only: Eta.prems)
  have forward: "book_printed_theory_derivable \<Sigma> G S (book_imp A B)"
    by (rule book_printed_theory_derivable.Eta[OF al bl], rule disjI1, rule Eta.hyps(3))
  have backward: "book_printed_theory_derivable \<Sigma> G S (book_imp B A)"
    by (rule book_printed_theory_derivable.Eta[OF bl al], rule disjI2, rule Eta.hyps(3))
  show ?case by (rule conjI[OF forward backward])
next
  case (Sym \<tau> A B)
  show ?case using Sym.IH[OF Sym.prems] by blast
next
  case (Trans \<tau> A B C)
  have first: "book_printed_theory_derivable \<Sigma> G S (book_imp A B) \<and>
    book_printed_theory_derivable \<Sigma> G S (book_imp B A)" by (rule Trans.IH(1)[OF Trans.prems])
  have second: "book_printed_theory_derivable \<Sigma> G S (book_imp B C) \<and>
    book_printed_theory_derivable \<Sigma> G S (book_imp C B)" by (rule Trans.IH(2)[OF Trans.prems])
  have al: "book_printed_theory_formula \<Sigma> G A" and bl: "book_printed_theory_formula \<Sigma> G B"
    using book_printed_conversion_languages[OF Trans.hyps(1)] by (auto simp: Trans.prems)
  have cl: "book_printed_theory_formula \<Sigma> G C"
    using book_printed_conversion_languages[OF Trans.hyps(2)] by (auto simp: Trans.prems)
  show ?case by (rule conjI,
    rule book_printed_theory_imp_trans[OF al bl cl conjunct1[OF first] conjunct1[OF second]],
    rule book_printed_theory_imp_trans[OF cl bl al conjunct2[OF second] conjunct2[OF first]])
qed

theorem book_printed_theory_conversion_transport:
  assumes conversion: "book_printed_conversion book_minimal_logical_type UNIV \<Sigma> G Prop A B"
    and derivation: "book_printed_theory_derivable \<Sigma> G S A"
  shows "book_printed_theory_derivable \<Sigma> G S B"
proof -
  have bl: "book_printed_theory_formula \<Sigma> G B"
    by (rule conjunct2[OF book_printed_conversion_languages[OF conversion]])
  have implication: "book_printed_theory_derivable \<Sigma> G S (book_imp A B)"
    by (rule conjunct1[OF book_printed_theory_conversion_pair[OF conversion refl]])
  show ?thesis by (rule book_printed_theory_derivable.MP[OF derivation implication bl])
qed

end
