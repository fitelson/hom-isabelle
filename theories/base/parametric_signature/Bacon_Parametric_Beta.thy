theory Bacon_Parametric_Beta
  imports Bacon_Parametric_Propositional
begin

text \<open>
  (λv.A)B →β A[B/v], A →η B, and propositional tautologies are separate syntactic
  ingredients of ⊢H A.

  Isabelle representation: this stable import wrapper combines Contraction
  (root steps and typing), Conversion (contexts and string translations),
  and Propositional (Boolean evaluation and tautologies).

  Status: an import boundary with independently checkable leaves.  H
  theoremhood, model semantics, and completeness are separate developments.
\<close>

end
