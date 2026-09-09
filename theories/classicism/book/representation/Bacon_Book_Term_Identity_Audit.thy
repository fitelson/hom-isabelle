theory Bacon_Book_Term_Identity_Audit
  imports Bacon_Book_Term_Actual_Identity
begin

ML_file "../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("Leibniz equivalence is equality in the actual canonical term general models", "book_full_C_canonical_frame.full_term_leibniz_iff_equal")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-term-identity"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: pure HOL; no HOL-ZF import\n"
    ^ "SCOPE: actual full-C term-domain separation at all full types; no complete modal-model or completeness claim\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-term-identity-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

text \<open>
  Actual identity is proved, not added as a model field. This
  certificate does not assert complete modal-model membership,
  the remaining operation/combinator conditions, or C completeness.
  Statement and type-class premises remain explicit.
\<close>

end
