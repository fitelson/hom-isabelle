theory Bacon_Book_Printed_Conversion_Correspondence
  imports Bacon_Book_Source_Reduction_Conversion
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Raw_Conversion
begin

section \<open>Printed conversion implies the existing exact-capture conversion\<close>

lemma book_printed_beta_step_named:
  assumes step: "named_compatible_step book_printed_beta_contract A B"
  shows "named_compatible_step named_beta_contract A B"
  using step
  by (induction rule: named_compatible_step.induct)
     (auto intro: named_compatible_step.intros book_printed_beta_contract_named)

theorem book_printed_conversion_named:
  assumes conversion: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> A B"
  using conversion
proof (induction rule: book_printed_conversion.induct)
  case Refl
  show ?case by (rule named_beta_eta_in_language.Refl[OF book_language_named[OF Refl.hyps]])
next
  case PrintedBeta
  show ?case by (rule named_beta_eta_in_language.Beta[
    OF book_language_named[OF PrintedBeta.hyps(1)] book_language_named[OF PrintedBeta.hyps(2)]
      book_printed_beta_step_named[OF PrintedBeta.hyps(3)]])
next
  case Eta
  show ?case by (rule named_beta_eta_in_language.Eta[
    OF book_language_named[OF Eta.hyps(1)] book_language_named[OF Eta.hyps(2)] Eta.hyps(3)])
next
  case Sym
  show ?case by (rule named_beta_eta_in_language.Sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule named_beta_eta_in_language.Trans[OF Trans.IH])
qed

section \<open>Conversely, simulate each exact-capture β step\<close>

text \<open>
  With rich G, the two declared-nonlogical-signature conversion relations
  coincide when every logical symbol in L is permitted. Each exact-capture
  β step is simulated by the independently checked printed conversion.
  No untyped or foreign-nonlogical intermediate is introduced.

  The UNIV logical-signature specialization is explicit. This theorem
  does not retract foreign logical symbols from a chain for an arbitrary
  partial Λ, nor prove internal conversion for an arbitrary 𝒥.
\<close>

theorem book_named_conversion_printed:
  assumes rich: "sg_rich G"
    and conversion: "named_beta_eta_in_language L \<Sigma> G \<tau> A B"
  shows "book_printed_conversion L UNIV \<Sigma> G \<tau> A B"
  using conversion
proof (induction rule: named_beta_eta_in_language.induct)
  case (Refl A \<tau>)
  have language: "book_in_language L UNIV \<Sigma> G A \<tau>"
    using Refl.hyps by (simp only: book_language_UNIV)
  show ?case by (rule book_printed_conversion.Refl[OF language])
next
  case (Beta A \<tau> B)
  have language: "book_in_language L UNIV \<Sigma> G A \<tau>"
    using Beta.hyps(1) by (simp only: book_language_UNIV)
  show ?case by (rule book_exact_beta_step_printed_conversion[OF rich Beta.hyps(3) language])
next
  case (Eta A \<tau> B)
  have al: "book_in_language L UNIV \<Sigma> G A \<tau>"
    using Eta.hyps(1) by (simp only: book_language_UNIV)
  have bl: "book_in_language L UNIV \<Sigma> G B \<tau>"
    using Eta.hyps(2) by (simp only: book_language_UNIV)
  show ?case by (rule book_printed_conversion.Eta[OF al bl Eta.hyps(3)])
next
  case Sym
  show ?case by (rule book_printed_conversion.Sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule book_printed_conversion.Trans[OF Trans.IH])
qed

theorem book_named_conversion_iff_printed:
  assumes rich: "sg_rich G"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> A B \<longleftrightarrow>
    book_printed_conversion L UNIV \<Sigma> G \<tau> A B"
  by (rule iffI; (rule book_named_conversion_printed[OF rich] | rule book_printed_conversion_named); assumption)

corollary book_raw_conversion_iff_printed:
  assumes rich: "sg_rich G"
  shows "named_raw_beta_eta L G \<tau> A B \<longleftrightarrow>
    book_printed_conversion L UNIV (\<lambda>_. UNIV) G \<tau> A B"
  by (rule book_named_conversion_iff_printed[OF rich])

end
