theory Bacon_Book_Full_Classicism_Calculus
  imports Bacon_Book_Full_Modalized_Functionality
begin

section \<open>Full-type Classicism: H, MF and Propositional Equivalence\<close>

inductive book_full_C_proves :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  H: "book_H \<Sigma> G A \<Longrightarrow> book_full_C_proves \<Sigma> G A"
| MF: "book_full_C_proves \<Sigma> G (book_MF_axiom G \<sigma> \<tau>)"
| MP: "book_full_C_proves \<Sigma> G A \<Longrightarrow> book_full_C_proves \<Sigma> G (book_imp A B) \<Longrightarrow>
    book_theory_formula \<Sigma> G B \<Longrightarrow> book_full_C_proves \<Sigma> G B"
| Gen: "book_full_C_proves \<Sigma> G (book_imp A B) \<Longrightarrow>
    book_theory_formula \<Sigma> G A \<Longrightarrow> book_theory_formula \<Sigma> G B \<Longrightarrow>
    n \<notin> named_fv A \<Longrightarrow> book_full_C_proves \<Sigma> G (book_imp A (book_all G n B))"
| PE: "book_full_C_proves \<Sigma> G (book_iff G P Q) \<Longrightarrow>
    book_theory_formula \<Sigma> G P \<Longrightarrow> book_theory_formula \<Sigma> G Q \<Longrightarrow>
    book_full_C_proves \<Sigma> G (book_leibniz G Prop P Q)"

theorem book_full_C_proves_language:
  assumes rich: "sg_rich G" and derivation: "book_full_C_proves \<Sigma> G A"
  shows "book_theory_formula \<Sigma> G A"
  using derivation
proof (induction rule: book_full_C_proves.induct)
  case H
  show ?case by (rule book_H_language[OF rich H.hyps])
next
  case MF
  show ?case by (rule book_MF_axiom_language[OF rich])
next
  case MP
  show ?case by (rule MP.hyps(3))
next
  case Gen
  show ?case by (rule book_imp_language[OF Gen.hyps(2) book_all_language[OF Gen.hyps(3)]])
next
  case PE
  show ?case by (rule book_leibniz_language[OF rich PE.hyps(2,3)])
qed

lemma book_full_C_from_empty_theory:
  assumes rich: "sg_rich G" and derivation: "book_theory_derivable \<Sigma> G {} A"
  shows "book_full_C_proves \<Sigma> G A"
  by (rule book_full_C_proves.H; simp only: book_H_iff_theory[OF rich]; rule derivation)

theorem book_full_C_contains_theory_derivation:
  assumes rich: "sg_rich G" and derivation: "book_theory_derivable \<Sigma> G S A"
    and support: "\<And>B. B \<in> S \<Longrightarrow> book_full_C_proves \<Sigma> G B"
  shows "book_full_C_proves \<Sigma> G A"
  using derivation support
proof (induction rule: book_theory_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case PC1
  show ?case by (rule book_full_C_from_empty_theory[OF rich]; rule book_theory_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_full_C_from_empty_theory[OF rich]; rule book_theory_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_full_C_from_empty_theory[OF rich]; rule book_theory_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_full_C_from_empty_theory[OF rich]; rule book_theory_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_full_C_from_empty_theory[OF rich]; rule book_theory_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_full_C_from_empty_theory[OF rich]; rule book_theory_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_full_C_proves.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_full_C_proves.Gen[OF Gen.IH[OF Gen.prems] Gen.hyps(2,3,4)])
qed

text \<open>
  This is the independent full-F presentation specified in Chapter 8,
  endnote 5. MF is an explicit family of axioms; PE is the proof rule
  from a proved biconditional to propositional identity. Vector
  Equivalence and Necessitation are not primitive rules here. Their
  admissibility, and the connection to book_C_proves, require proofs.
  The H-theory closure theorem supplies ordinary consequence from
  already proved full-C theorems, not PE on temporary assumptions.
\<close>

end
