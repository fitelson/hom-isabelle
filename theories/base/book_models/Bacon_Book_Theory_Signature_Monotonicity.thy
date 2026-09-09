theory Bacon_Book_Theory_Signature_Monotonicity
  imports Bacon_Book_Theory_Derivation
begin

section \<open>Enlarging the declared nonlogical signature preserves a theory proof\<close>

text \<open>
  If Σσ ⊆ Ωσ at every type, a derivation S ⊢Σ A is also a
  derivation S ⊢Ω A. Source role: the signature-relative theory
  definitions and proof sequences of Bacon, pp.97–102.

  Isabelle representation. Terms, the variable stock G, logical symbols,
  and the premise set S are unchanged. Only the nonlogical membership
  guards are weakened. The proof has exactly the nine constructors of
  book_theory_derivable, including Assumption, and retains the same
  immediate β/η steps and Gen freshness condition.

  Status. No substitution, H identification, model, richness, or
  signature-conservativity theorem is assumed. This is the enlargement
  direction only; removing foreign constants is a separate task.
\<close>

lemma book_named_signature_mono:
  fixes A :: "('c, 'l) named_term"
  assumes names: "named_in_signature \<Sigma> A"
    and inclusion: "\<And>\<sigma>. \<Sigma> \<sigma> \<subseteq> \<Omega> \<sigma>"
  shows "named_in_signature \<Omega> A"
  using names
proof (induction A)
  case (NVar n)
  show ?case by simp
next
  case (NConst c \<sigma>)
  have original: "c \<in> \<Sigma> \<sigma>" using NConst.prems by simp
  have enlarged: "c \<in> \<Omega> \<sigma>" by (rule subsetD[OF inclusion original])
  show ?case using enlarged by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fn: "named_in_signature \<Sigma> F" and arg: "named_in_signature \<Sigma> A"
    using NApp.prems by simp_all
  show ?case by (simp only: named_in_signature.simps; rule conjI[OF NApp.IH(1)[OF fn] NApp.IH(2)[OF arg]])
next
  case (NLam n A)
  have body: "named_in_signature \<Sigma> A" using NLam.prems by simp
  show ?case by (simp only: named_in_signature.simps; rule NLam.IH[OF body])
qed

lemma book_language_signature_mono:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and inclusion: "\<And>\<sigma>. \<Sigma> \<sigma> \<subseteq> \<Omega> \<sigma>"
  shows "book_in_language L \<Lambda> \<Omega> G A \<tau>"
proof -
  have typed: "has_ntype L G A \<tau>" by (rule book_language_type[OF language])
  have names: "named_in_signature \<Omega> A"
    by (rule book_named_signature_mono[OF book_language_signature[OF language] inclusion])
  have logicals: "named_logical_occurrences A \<subseteq> \<Lambda>"
    by (rule book_language_logical_occurrences[OF language])
  show ?thesis unfolding book_in_language_def named_in_language_def
    by (rule conjI[OF conjI[OF typed names] logicals])
qed

theorem book_theory_signature_mono:
  assumes derivation: "book_theory_derivable \<Sigma> G S A"
    and inclusion: "\<And>\<sigma>. \<Sigma> \<sigma> \<subseteq> \<Omega> \<sigma>"
  shows "book_theory_derivable \<Omega> G S A"
  using derivation
proof (induction rule: book_theory_derivable.induct)
  case Assumption
  show ?case by (rule book_theory_derivable.Assumption[OF Assumption.hyps(1)
    book_language_signature_mono[OF Assumption.hyps(2) inclusion]])
next
  case PC1
  show ?case by (rule book_theory_derivable.PC1[OF
    book_language_signature_mono[OF PC1.hyps(1) inclusion]
    book_language_signature_mono[OF PC1.hyps(2) inclusion]])
next
  case PC2
  show ?case by (rule book_theory_derivable.PC2[OF
    book_language_signature_mono[OF PC2.hyps(1) inclusion]
    book_language_signature_mono[OF PC2.hyps(2) inclusion]
    book_language_signature_mono[OF PC2.hyps(3) inclusion]])
next
  case PC3
  show ?case by (rule book_theory_derivable.PC3[OF
    book_language_signature_mono[OF PC3.hyps(1) inclusion]
    book_language_signature_mono[OF PC3.hyps(2) inclusion]])
next
  case UI
  show ?case by (rule book_theory_derivable.UI[OF
    book_language_signature_mono[OF UI.hyps(1) inclusion]
    book_language_signature_mono[OF UI.hyps(2) inclusion]])
next
  case Beta
  show ?case by (rule book_theory_derivable.Beta[OF
    book_language_signature_mono[OF Beta.hyps(1) inclusion]
    book_language_signature_mono[OF Beta.hyps(2) inclusion] Beta.hyps(3)])
next
  case Eta
  show ?case by (rule book_theory_derivable.Eta[OF
    book_language_signature_mono[OF Eta.hyps(1) inclusion]
    book_language_signature_mono[OF Eta.hyps(2) inclusion] Eta.hyps(3)])
next
  case MP
  show ?case by (rule book_theory_derivable.MP[OF MP.IH(1,2)
    book_language_signature_mono[OF MP.hyps(3) inclusion]])
next
  case Gen
  show ?case by (rule book_theory_derivable.Gen[OF Gen.IH
    book_language_signature_mono[OF Gen.hyps(2) inclusion]
    book_language_signature_mono[OF Gen.hyps(3) inclusion] Gen.hyps(4)])
qed

end
