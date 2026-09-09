theory Bacon_Book_Term_Logical_Audit
  imports Bacon_Book_Term_General_Model
begin

ML_file "../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("characteristic truth is independent of the proposition representative", "book_C_identity_world.term_valuation_class"),
    ("literal primitive symbols have typed class values", "book_C_identity_world.term_logical_value_typed"),
    ("the displayed bottom proposition is false", "book_C_identity_world.term_valuation_bottom"),
    ("implication has its truth clause on every proposition class", "book_C_identity_world.term_implication_truth"),
    ("universal quantification ranges over every typed class value", "book_C_identity_world.term_forall_truth"),
    ("the actual term data form a general model under witnesses and inhabitation", "book_C_identity_world.term_full_minimal_model"),
    ("each actual full-C world supplies those witnesses and nonempty domains", "book_full_C_canonical_frame.full_term_general_model")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-term-logical"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: pure HOL; no HOL-ZF import\n"
    ^ "SCOPE: actual canonical per-world general-model and truth clauses; not the complete modal-model certificate or C completeness\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-term-logical-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

text \<open>
  Per-world general-model claims and the stronger modal-model
  requirements remain distinct. The latter still require the exact
  future-valued logical operations and combinator/identity membership.
  All statement premises are retained; no oracle, residual hypothesis
  or flex-flex constraint is accepted by this audit.
\<close>

end
