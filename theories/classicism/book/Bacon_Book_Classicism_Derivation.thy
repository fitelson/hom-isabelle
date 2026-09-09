theory Bacon_Book_Classicism_Derivation
  imports Bacon_Book_Classicism_Syntax
begin

section \<open>Finite proofs from H, MP, Gen and the book's Equivalence rule\<close>

inductive book_C_proves :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  H: "book_H \<Sigma> G A \<Longrightarrow> book_C_proves \<Sigma> G A"
| MP: "book_C_proves \<Sigma> G A \<Longrightarrow> book_C_proves \<Sigma> G (book_imp A B) \<Longrightarrow>
    book_theory_formula \<Sigma> G B \<Longrightarrow> book_C_proves \<Sigma> G B"
| Gen: "book_C_proves \<Sigma> G (book_imp A B) \<Longrightarrow>
    book_theory_formula \<Sigma> G A \<Longrightarrow> book_theory_formula \<Sigma> G B \<Longrightarrow>
    n \<notin> named_fv A \<Longrightarrow> book_C_proves \<Sigma> G (book_imp A (book_all G n B))"
| Equivalence: "book_C_proves \<Sigma> G (book_iff G (book_vector_application R ns) (book_vector_application S ns)) \<Longrightarrow>
    book_equivalence_rule_instance \<Sigma> G ns R S \<Longrightarrow>
    book_C_proves \<Sigma> G (book_leibniz G (foldr Arr (map G ns) Prop) R S)"

theorem book_C_proves_language:
  assumes rich: "sg_rich G" and derivation: "book_C_proves \<Sigma> G A"
  shows "book_theory_formula \<Sigma> G A"
  using derivation
proof (induction rule: book_C_proves.induct)
  case H
  show ?case by (rule book_H_language[OF rich H.hyps])
next
  case MP
  show ?case by (rule MP.hyps(3))
next
  case Gen
  show ?case by (rule book_imp_language[OF Gen.hyps(2) book_all_language[OF Gen.hyps(3)]])
next
  case Equivalence
  show ?case by (rule book_equivalence_conclusion_language[OF rich Equivalence.hyps(2)])
qed

lemma book_C_from_empty_theory:
  "sg_rich G \<Longrightarrow> book_theory_derivable \<Sigma> G {} A \<Longrightarrow> book_C_proves \<Sigma> G A"
  by (rule book_C_proves.H; subst book_H_iff_theory; assumption)

theorem book_C_contains_theory_derivation:
  assumes rich: "sg_rich G" and derivation: "book_theory_derivable \<Sigma> G S A"
    and support: "\<And>B. B \<in> S \<Longrightarrow> book_C_proves \<Sigma> G B"
  shows "book_C_proves \<Sigma> G A"
  using derivation support
proof (induction rule: book_theory_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case PC1
  show ?case by (rule book_C_from_empty_theory[OF rich]; rule book_theory_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_C_from_empty_theory[OF rich]; rule book_theory_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_C_from_empty_theory[OF rich]; rule book_theory_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_C_from_empty_theory[OF rich]; rule book_theory_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_C_from_empty_theory[OF rich]; rule book_theory_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_C_from_empty_theory[OF rich]; rule book_theory_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_C_proves.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_C_proves.Gen[OF Gen.IH[OF Gen.prems] Gen.hyps(2,3,4)])
qed

theorem book_C_proofs_form_classicist_theory:
  assumes rich: "sg_rich G"
  shows "book_classicist_theory \<Sigma> G {A. book_C_proves \<Sigma> G A}"
proof (unfold book_classicist_theory_def, rule conjI)
  show "book_higher_order_theory \<Sigma> G {A. book_C_proves \<Sigma> G A}"
    unfolding book_higher_order_theory_def
  proof (rule conjI)
    show "\<forall>A\<in>{A. book_C_proves \<Sigma> G A}. book_theory_formula \<Sigma> G A"
      using book_C_proves_language[OF rich] by blast
  next
    show "\<forall>A. book_theory_derivable \<Sigma> G {B. book_C_proves \<Sigma> G B} A \<longrightarrow>
      A \<in> {B. book_C_proves \<Sigma> G B}"
    proof (intro allI impI)
      fix A
      assume derivation: "book_theory_derivable \<Sigma> G {B. book_C_proves \<Sigma> G B} A"
      have "book_C_proves \<Sigma> G A"
        by (rule book_C_contains_theory_derivation[OF rich derivation]; simp)
      then show "A \<in> {B. book_C_proves \<Sigma> G B}" by simp
    qed
  qed
next
  show "book_equivalence_closed \<Sigma> G {A. book_C_proves \<Sigma> G A}"
    unfolding book_equivalence_closed_def
    by (intro allI impI; simp only: mem_Collect_eq; rule book_C_proves.Equivalence; assumption)
qed

text \<open>
  This is a theoremhood calculus: MP/Gen apply to C theorems, not
  arbitrary temporary assumptions. H is the already checked least book
  logic. Its closure over a set of established C theorems is proved by
  the nine cases of the native book theory calculus above.
  The least-theory identification and local consistency interface follow
  separately. No earlier paper or R Classicism judgment is used.
\<close>

end
