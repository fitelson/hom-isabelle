theory Bacon_Book_ZF_Interpretation_Audit
  imports Bacon_Book_ZF_Future_Abstraction
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("inverse maps decode typed assignments", "book_full_C_coded_frame.full_ZF_assignment_decode_typed"),
    ("actual counterparts transport typed assignments", "book_full_C_coded_frame.full_ZF_assignment_move_typed"),
    ("assignment decoding commutes with actual counterpart transport", "book_full_C_coded_frame.full_ZF_assignment_decode_move"),
    ("assignment decoding commutes with variable update", "book_full_C_coded_frame.full_ZF_assignment_decode_update"),
    ("the actual represented interpretation has typed values", "book_full_C_coded_frame.full_ZF_denote_type"),
    ("the actual represented interpretation evaluates variables", "book_full_C_coded_frame.full_ZF_denote_var"),
    ("closed terms have their represented identity-class values", "book_full_C_coded_frame.full_ZF_denote_closed"),
    ("the represented interpretation is local", "book_full_C_coded_frame.full_ZF_denote_locality"),
    ("the represented interpretation evaluates actual graph application", "book_full_C_coded_frame.full_ZF_denote_app"),
    ("the represented interpretation commutes with counterparts", "book_full_C_coded_frame.full_ZF_denote_natural"),
    ("the represented interpretation respects raw typed conversion", "book_full_C_coded_frame.full_ZF_denote_conversion"),
    ("abstraction evaluates correctly at every future world and argument", "book_full_C_coded_frame.full_ZF_denote_lambda_future"),
    ("every interpreted abstraction is a genuine future homomorphism", "book_full_C_coded_frame.full_ZF_denote_lambda_homomorphism")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-interpretation"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; distinct from the pure-HOL term interpretation audit\n"
    ^ "SCOPE: actual represented interpretation over the coded full-C canonical frame (arbitrary name carrier), including all-future abstraction; no complete modal-model or completeness claim\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-interpretation-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

text \<open>
  These endpoints are checked separately from the earlier proof and
  representation audits. Their statement premises remain explicit.
  They do not assume or conclude a complete modal-model certificate
  or C completeness. The primitive logical clauses and final model
  and truth theorems are separate obligations.
\<close>

end
