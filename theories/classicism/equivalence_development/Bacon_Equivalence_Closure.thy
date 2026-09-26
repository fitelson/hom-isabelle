theory Bacon_Equivalence_Closure
  imports Bacon_C_Rule_Equivalence
begin

section \<open>Closure of axiom-based C under Equivalence\<close>

text \<open>
  From ⊢C A ↔ B, derive ⊢C (λv̄.A) = (λv̄.B).
  Sources: Bacon--Dorr Proposition A.3, p.67, using A.1–A.2 on
  pp.65–67; Bacon, Theorem 6.1, printed pp.126–127.

  Isabelle representation. This import point gathers A.1, the complete
  C-proof induction A.2, and the resulting Equivalence theorem A.3.
  ObjTrue is ⊤₀ := ∀p.(p → p); C_boolean_truth is
  ⊤ᴮ := ⊤₀ ∨ ¬⊤₀. Their identity is proved in the imported development.

  Status.  C_Appendix_A1_universal_truth and its boxed corollary prove
  ⊢C (∀x:σ.⊤₀) =ₜ ⊤₀ and ⊢C □∀x:σ.⊤₀.  The A.2 files supply
  the vector truth identity for every C theorem, including mixed types
  and the empty vector. C_Appendix_A3 derives abstraction Equivalence.

  Scope.  Every derivability conclusion in these files is in axiom-based
  C.  CE adds propositional Equivalence, and CEV adds the vector rule;
  neither stronger calculus is used to justify closure of C.  This
  import point by itself does not identify the existing CE/CEV judgments:
  their presentation inductions and CEV's variable-order bridge are separate.
\<close>

subsection \<open>Downstream use and remaining obligations\<close>

text \<open>
  The connection of the existing CE/CEV presentation judgments to these
  C-only theorems is done in the separate Bacon_C_Presentation_Development
  session: CE_proves_to_C and CE_proves_iff_C_proves
  (presentation_reconciliation/Bacon_C_Propositional_Presentation) and
  CEV_proves_to_C and CEV_proves_iff_C_proves
  (presentation_reconciliation/Bacon_C_Vector_Presentation) use the
  Equivalence theorem A.3 gathered here.  What remains is literal source
  proof correspondence.
  Locators: Bacon--Dorr A.2, pp.65–67, and A.3, p.67.

  Representation and status. A.1–A.3 are statements in the represented
  full-F, unrestricted typed-string calculus, with its documented
  primitive-implication and IndividualExistence presentation adjustments.
  Exact source vocabulary and named-variable correspondence must still
  connect that implementation to the literal published language. No proof
  is added by this import-only theory.
\<close>

end
