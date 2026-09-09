theory Bacon_Book_Source_Reduction_Conversion
  imports Bacon_Book_Printed_Alpha_Conversion Bacon_Book_Printed_Contextual_Beta_Simulation
begin

section \<open>Eliminating α steps from source reduction\<close>

text \<open>
  Every source reduction beginning at a declared typed term yields a
  printed βη conversion. Its α cases use the independently replayed
  printed conversion theorem, not an α constructor. Reduction preserves
  every intermediate term's type and signature, so the conversion carries
  the required guards throughout. Source: Definitions 3.7–3.10, pp.70–73.
\<close>

lemma book_source_step_printed_conversion:
  assumes step: "book_source_reduction_step G A B"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B"
proof -
  have target: "book_in_language L \<Lambda> \<Sigma> G B \<tau>"
    by (rule book_source_reduction_step_language[OF step language])
  show ?thesis using step unfolding book_source_reduction_step_def
    by (blast intro: book_printed_conversion.PrintedBeta[OF language target]
        book_printed_conversion.Eta[OF language target]
        book_alpha_implies_printed_conversion[OF _ language])
qed

theorem book_source_reduces_printed_conversion:
  assumes reduction: "book_source_reduces G A B"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B"
  using reduction[unfolded book_source_reduces_def] language
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule book_printed_conversion.Refl[OF base.prems])
next
  case (step B C)
  have first: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B"
    by (rule step.IH[OF step.prems])
  have middle: "book_in_language L \<Lambda> \<Sigma> G B \<tau>"
    by (rule conjunct2[OF book_printed_conversion_languages[OF first]])
  have second: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> B C"
    by (rule book_source_step_printed_conversion[OF step.hyps(2) middle])
  show ?case by (rule book_printed_conversion.Trans[OF first second])
qed

theorem book_exact_beta_step_printed_conversion:
  assumes rich: "sg_rich G"
    and step: "named_compatible_step named_beta_contract A B"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B"
  by (rule book_source_reduces_printed_conversion[
    OF book_printed_beta_step_simulation[OF rich step language] language])

end
