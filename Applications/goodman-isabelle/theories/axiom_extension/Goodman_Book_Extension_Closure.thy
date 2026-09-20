theory Goodman_Book_Extension_Closure
  imports Goodman_Book_Axiom_Extension
begin

section \<open>Ordinary theory closure of the extension's theorems\<close>

text \<open>
  Let Cl(T) = {A : C+[T] ⊢ A}. We prove that ordinary C-consequence
  from Cl(T) yields exactly Cl(T), not that ordinary consequence from
  T already permits PE. This elementary bridge permits later use of
  the core's model-existence theorem on the closed set, provided its
  consistency is independently established. It does not establish it.
\<close>

definition goodman_book_closure where
  "goodman_book_closure \<Sigma> G T = {A. goodman_book_proves \<Sigma> G T A}"

definition goodman_book_consistent where
  "goodman_book_consistent \<Sigma> G T \<longleftrightarrow>
    \<not> goodman_book_proves \<Sigma> G T (book_bottom G)"

lemma goodman_book_contains_theory_derivation:
  assumes rich: "sg_rich G" and derivation: "book_theory_derivable \<Sigma> G S A"
    and support: "\<And>B. B \<in> S \<Longrightarrow> goodman_book_proves \<Sigma> G T B"
  shows "goodman_book_proves \<Sigma> G T A"
  using derivation support
proof (induction rule: book_theory_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case PC1
  show ?case by (rule goodman_book_proves.Base, rule book_full_C_from_empty_theory[OF rich],
    rule book_theory_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule goodman_book_proves.Base, rule book_full_C_from_empty_theory[OF rich],
    rule book_theory_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule goodman_book_proves.Base, rule book_full_C_from_empty_theory[OF rich],
    rule book_theory_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule goodman_book_proves.Base, rule book_full_C_from_empty_theory[OF rich],
    rule book_theory_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule goodman_book_proves.Base, rule book_full_C_from_empty_theory[OF rich],
    rule book_theory_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule goodman_book_proves.Base, rule book_full_C_from_empty_theory[OF rich],
    rule book_theory_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule goodman_book_proves.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
next
  case Gen
  show ?case by (rule goodman_book_proves.Gen[OF Gen.IH[OF Gen.prems] Gen.hyps(2,3,4)])
qed

lemma goodman_book_contains_C_theory:
  assumes rich: "sg_rich G" and derivation: "book_full_C_theory_derivable \<Sigma> G S A"
    and support: "\<And>B. B \<in> S \<Longrightarrow> goodman_book_proves \<Sigma> G T B"
  shows "goodman_book_proves \<Sigma> G T A"
  using derivation unfolding book_full_C_theory_derivable_def
  by (rule goodman_book_contains_theory_derivation[OF rich];
    auto intro: goodman_book_proves.Base support)

theorem goodman_book_ordinary_consequence_in_extension:
  assumes rich: "sg_rich G" and language: "\<And>B. B \<in> T \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and derivation: "book_full_C_theory_derivable \<Sigma> G T A"
  shows "goodman_book_proves \<Sigma> G T A"
  by (rule goodman_book_contains_C_theory[OF rich derivation],
    rule goodman_book_proves.Axiom; (assumption | rule language); assumption?)

theorem goodman_book_closure_theory_iff:
  assumes rich: "sg_rich G"
  shows "book_full_C_theory_derivable \<Sigma> G (goodman_book_closure \<Sigma> G T) A
    \<longleftrightarrow> goodman_book_proves \<Sigma> G T A"
proof
  assume derivation: "book_full_C_theory_derivable \<Sigma> G (goodman_book_closure \<Sigma> G T) A"
  show "goodman_book_proves \<Sigma> G T A"
    by (rule goodman_book_contains_C_theory[OF rich derivation]; simp add: goodman_book_closure_def)
next
  assume derivation: "goodman_book_proves \<Sigma> G T A"
  have member: "A \<in> goodman_book_closure \<Sigma> G T" using derivation by (simp add: goodman_book_closure_def)
  show "book_full_C_theory_derivable \<Sigma> G (goodman_book_closure \<Sigma> G T) A"
    by (rule book_full_C_theory_assume[OF member goodman_book_proves_language[OF rich derivation]])
qed

theorem goodman_book_closure_consistency_iff:
  "sg_rich G \<Longrightarrow>
    book_full_C_theory_consistent \<Sigma> G (goodman_book_closure \<Sigma> G T)
    \<longleftrightarrow> goodman_book_consistent \<Sigma> G T"
  by (simp only: book_full_C_theory_consistent_def goodman_book_consistent_def goodman_book_closure_theory_iff)

theorem goodman_book_closure_idempotent:
  assumes rich: "sg_rich G"
  shows "goodman_book_closure \<Sigma> G (goodman_book_closure \<Sigma> G T) = goodman_book_closure \<Sigma> G T"
proof (rule set_eqI)
  fix A
  show "A \<in> goodman_book_closure \<Sigma> G (goodman_book_closure \<Sigma> G T)
    \<longleftrightarrow> A \<in> goodman_book_closure \<Sigma> G T"
    unfolding goodman_book_closure_def
    by (auto intro: goodman_book_proves.Axiom goodman_book_proves_language[OF rich]
      elim: goodman_book_cut)
qed

end
