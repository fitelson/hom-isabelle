theory Bacon_Book_Classicism_Least_Theory
  imports Bacon_Book_Classicism_Derivation
begin

section \<open>The finite calculus is exactly the least Equivalence-closed theory\<close>

theorem book_classicist_theory_contains_proof:
  assumes rich: "sg_rich G" and target: "book_classicist_theory \<Sigma> G T"
    and derivation: "book_C_proves \<Sigma> G A"
  shows "A \<in> T"
proof -
  have theory_ok: "book_higher_order_theory \<Sigma> G T" and equivalent: "book_equivalence_closed \<Sigma> G T"
    using target unfolding book_classicist_theory_def by blast+
  have rules: "book_theory_rules \<Sigma> G T"
    using theory_ok book_higher_order_theory_iff_rules by blast
  show ?thesis using derivation
  proof (induction rule: book_C_proves.induct)
    case (H A)
    have proof_H: "book_theory_derivable \<Sigma> G {} A"
      using H.hyps by (simp only: book_H_iff_theory[OF rich])
    show ?case by (rule book_theory_contains_derivation[OF theory_ok proof_H empty_subsetI])
  next
    case MP
    show ?case using rules MP.IH unfolding book_theory_rules_def by blast
  next
    case Gen
    show ?case using rules Gen.IH Gen.hyps(4) unfolding book_theory_rules_def by blast
  next
    case Equivalence
    show ?case using equivalent Equivalence.IH Equivalence.hyps(2)
      unfolding book_equivalence_closed_def by blast
  qed
qed

theorem book_C_iff_proves:
  assumes rich: "sg_rich G"
  shows "book_C \<Sigma> G A \<longleftrightarrow> book_C_proves \<Sigma> G A"
proof
  assume least: "book_C \<Sigma> G A"
  have actual: "book_classicist_theory \<Sigma> G {B. book_C_proves \<Sigma> G B}"
    by (rule book_C_proofs_form_classicist_theory[OF rich])
  show "book_C_proves \<Sigma> G A" using least actual unfolding book_C_def by blast
next
  assume derivation: "book_C_proves \<Sigma> G A"
  have language: "book_theory_formula \<Sigma> G A" by (rule book_C_proves_language[OF rich derivation])
  show "book_C \<Sigma> G A" unfolding book_C_def
    by (rule conjI[OF language], intro allI impI; rule book_classicist_theory_contains_proof[OF rich _ derivation]; assumption)
qed

corollary book_C_contains_H:
  assumes rich: "sg_rich G" and base: "book_H \<Sigma> G A"
  shows "book_C \<Sigma> G A"
  by (simp only: book_C_iff_proves[OF rich]; rule book_C_proves.H[OF base])

corollary book_C_is_classicist_theory:
  assumes rich: "sg_rich G"
  shows "book_classicist_theory \<Sigma> G {A. book_C \<Sigma> G A}"
  by (simp only: book_C_iff_proves[OF rich]; rule book_C_proofs_form_classicist_theory[OF rich])

text \<open>
  This identifies two independently declared presentations of the
  book's Definition 6.1, p.126: the least higher-order theory closed
  under Equivalence and its finite H/MP/Gen/Equivalence calculus.
  The proof uses only the book's own H-theory interface.

  It does not yet identify this full-F/minimal-basis C with the
  paper's R-language calculus, the Classical Identities presentation,
  or a class of modal models. Those are separate correspondence and
  completeness obligations. In particular no paper modal theorem is
  silently imported to begin the book's canonical-frame proof.
\<close>

end
