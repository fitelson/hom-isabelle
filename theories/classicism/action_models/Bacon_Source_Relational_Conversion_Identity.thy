theory Bacon_Source_Relational_Conversion_Identity
  imports Bacon_Source_Relational_Conversion_Identity_Steps
    Bacon_Source_Relational_Signature_Conservativity Bacon_Source_Relational_Local_Exchange
begin

section \<open>Guarded R conversion chains yield locally derivable identity\<close>

theorem paper_R_named_derivable_signature_conversion_identity:
  assumes rich: "paper_R_rich G" and conversion: "paper_R_beta_eta_in_signature \<Sigma> G \<sigma> A B"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
  using conversion
proof (induction rule: paper_R_beta_eta_in_signature.induct)
  case Refl
  show ?case by (rule paper_R_named_identity_refl[OF Refl.hyps])
next
  case Beta
  show ?case by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_beta_identity[OF rich Beta.hyps]])
next
  case Eta
  show ?case by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_eta_identity[OF rich Eta.hyps]])
next
  case Sym
  show ?case by (rule paper_R_named_identity_sym[
    OF rich conjunct1[OF paper_R_signature_conversion_languages[OF Sym.hyps]]
      conjunct2[OF paper_R_signature_conversion_languages[OF Sym.hyps]] Sym.IH])
next
  case Trans
  show ?case by (rule paper_R_named_identity_trans[
    OF rich conjunct1[OF paper_R_signature_conversion_languages[OF Trans.hyps(1)]]
      conjunct2[OF paper_R_signature_conversion_languages[OF Trans.hyps(1)]]
      conjunct2[OF paper_R_signature_conversion_languages[OF Trans.hyps(2)]] Trans.IH])
qed

section \<open>Foreign intermediate constants are removed before the proof induction\<close>

text \<open>
  A≡βηB in raw R syntax implies ⊢HᴿA=σB when both endpoints
  belong to ℒᴿ(Σ). First retract the whole raw conversion chain
  into Σ using the checked R-rich signature-conservativity theorem.
  Then use Ref, the formula β/η certificates, symmetry and transitivity.
  The empty-local-consequence equivalence returns an actual H theorem.

  Source: Figure 2, p.8, and Theorem 3.2, footnote 64, p.45.
  Every result type in R is covered, including e. This is a derived
  proof theorem, not a newly assumed term-conversion identity axiom,
  a βη quotient definition, or a semantic BBK/Functionality principle.
  No F proof or F-model extension is used.
\<close>

theorem paper_R_named_H_raw_conversion_identity:
  assumes rich: "paper_R_rich G" and conversion: "paper_R_raw_beta_eta G \<sigma> A B"
    and left: "paper_R_in_language \<Sigma> G A \<sigma>" and right: "paper_R_in_language \<Sigma> G B \<sigma>"
  shows "paper_R_named_H \<Sigma> G (named_paper_eq \<sigma> A B)"
proof -
  have guarded: "paper_R_beta_eta_in_signature \<Sigma> G \<sigma> A B"
    by (rule paper_R_raw_to_signature[OF rich conversion left right])
  have local: "paper_R_named_derivable \<Sigma> G {} (named_paper_eq \<sigma> A B)"
    by (rule paper_R_named_derivable_signature_conversion_identity[OF rich guarded])
  show ?thesis by (rule iffD1[OF paper_R_named_derivable_empty_iff local])
qed

corollary paper_R_named_derivable_raw_conversion_identity:
  assumes rich: "paper_R_rich G" and conversion: "paper_R_raw_beta_eta G \<sigma> A B"
    and left: "paper_R_in_language \<Sigma> G A \<sigma>" and right: "paper_R_in_language \<Sigma> G B \<sigma>"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
  by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_raw_conversion_identity[OF rich conversion left right]])

end
