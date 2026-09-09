theory Bacon_Book_ZF_Generic_Interpretation_Audit
  imports Bacon_Book_ZF_Signature_Pullback
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("typed assignments transport to every accessible world", "book_ZF_modal_structure.assignment_move_typed"),
    ("assignment transport composes", "book_ZF_modal_structure.assignment_move_composition"),
    ("assignment transport commutes with a single update", "book_ZF_move_update"),
    ("the abstraction clause gives its exact future application", "book_ZF_modal_interpretation.abstraction_future_application"),
    ("every admissible interpretation is unique on typed inputs", "book_ZF_modal_interpretation.interpretation_unique"),
    ("formula validity is independent of the admissible interpretation", "book_ZF_modal_interpretation.formula_valid_independent"),
    ("theory satisfaction is independent of the admissible interpretation", "book_ZF_modal_interpretation.satisfaction_independent"),
    ("every modal model pulls back along a declared constant map", "book_ZF_modal_model.signature_pullback_model"),
    ("every admissible interpretation pulls back along the same map", "book_ZF_modal_interpretation.signature_pullback_interpretation"),
    ("signature pullback preserves and reflects formula validity", "book_ZF_signature_pullback_valid"),
    ("signature pullback preserves and reflects arbitrary theory satisfaction", "book_ZF_signature_pullback_satisfies")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-generic-interpretation"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; not pure HOL\n"
    ^ "SCOPE: Independent interpretation uniqueness, assignment transport and semantic signature pullback. No generic interpretation existence or soundness claim.\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-generic-interpretation-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

end

