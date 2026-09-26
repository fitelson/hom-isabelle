theory Bacon_Book_ZF_Operators_Audit
  imports Bacon_Book_ZF_S_Future_Value
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("the whole actual implication result has its future truth set", "book_full_C_coded_frame.full_ZF_implication_result"),
    ("the whole actual universal result has its future truth set", "book_full_C_coded_frame.full_ZF_forall_result"),
    ("the root implication operator has its two-stage future behavior", "book_full_C_coded_frame.full_ZF_implication_future_value"),
    ("the root universal operator has its full future behavior", "book_full_C_coded_frame.full_ZF_forall_future_value"),
    ("the universal future comprehension belongs to the chosen proposition domain", "book_full_C_coded_frame.full_ZF_forall_future_set_in_domain"),
    ("the implication future comprehension belongs to the chosen proposition domain", "book_full_C_coded_frame.full_ZF_implication_future_set_in_domain"),
    ("the actual implication set is the explicitly future-restricted difference and union", "book_full_C_coded_frame.full_ZF_implication_future_set"),
    ("the actual canonical k belongs to its full function domain", "book_full_C_coded_frame.full_ZF_K_value_type"),
    ("the actual canonical k commutes with counterparts", "book_full_C_coded_frame.full_ZF_K_value_natural"),
    ("the actual canonical k has Bacon's two-stage future behavior", "book_full_C_coded_frame.full_ZF_K_future_value"),
    ("the actual canonical s belongs to its full function domain", "book_full_C_coded_frame.full_ZF_S_value_type"),
    ("the actual canonical s commutes with counterparts", "book_full_C_coded_frame.full_ZF_S_value_natural"),
    ("the actual s body evaluates through graph application", "book_full_C_coded_frame.full_ZF_S_body_evaluation"),
    ("the actual canonical s has Bacon's three-stage future behavior", "book_full_C_coded_frame.full_ZF_S_future_value")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-operators"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; distinct from the pure-HOL combinator-syntax audit\n"
    ^ "SCOPE: actual canonical future implication (explicit future restriction), universal operator, k and s on the coded full-C frame (arbitrary name carrier); no complete modal-model or completeness claim\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-operators-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

text \<open>
  These checks concern the actual canonical witnesses. Implication
  retains its explicitly documented future restriction; no equality
  with the raw printed W-complement is asserted. The complete
  independent modal-model certificate and C soundness/completeness
  remain separate. No oracle or residual kernel obligation is accepted.
\<close>

end
