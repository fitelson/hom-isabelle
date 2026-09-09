theory Bacon_Source_Closed_Set_Preservation
  imports Bacon_Source_Set_Preservation Bacon_Source_Sentence_Sets
    Bacon_Source_Target_Set_Context_Elimination
begin

section \<open>Forward consequence preservation for closed sentence sets\<close>

text \<open>
  If S and A are closed sentences in ℒ(Σ), and source S ⊢H A,
  then target tr(S) ⊢H tr(A) in the empty variable context.
  The proof first translates the finite source derivation with sufficient
  variable support. Only then is its unused target context removed.

  S itself may be infinite. Context elimination uses closedness of every
  member of S, not a claim that every assumption was used. No model,
  signature enlargement, or closed signature inhabitants are assumed.
  Reverse consequence preservation is a separate theorem.
\<close>

theorem paper_closed_set_preservation:
  assumes sentences: "paper_sentence_set \<Sigma> S"
    and conclusion: "sterm_in_language paper_logical_type \<Sigma> [] A Prop"
    and derivation: "paper_global_derivable \<Sigma> G S A"
  shows "pH_set_derivable \<Sigma> [] (image paper_to_pterm S) (paper_to_pterm A)"
proof -
  have eventual: "paper_target_set_eventual \<Sigma> G S A"
    by (rule paper_global_derivable_target_eventual[OF derivation])
  obtain N where supported: "\<forall>m\<ge>N. pH_set_derivable \<Sigma> (source_prefix G m)
    (image paper_to_pterm S) (paper_to_pterm A)"
    using eventual unfolding paper_target_set_eventual_def by (elim exE)
  have finite_frame: "pH_set_derivable \<Sigma> (source_prefix G N)
    (image paper_to_pterm S) (paper_to_pterm A)" using supported by auto
  have target_conclusion: "pterm_in_language \<Sigma> [] (paper_to_pterm A) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff conclusion])
  show ?thesis by (rule source_target_closed_set_context_elimination[
    OF paper_sentence_set_target[OF sentences] target_conclusion finite_frame])
qed

end
