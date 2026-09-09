theory Bacon_Book_ZF_Logical_Audit
  imports Bacon_Book_ZF_General_Model
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("h at proposition type preserves literal world-membership truth", "book_full_C_canonical_frame.full_ZF_h_proposition_truth"),
    ("the represented interpretation preserves characteristic truth", "book_full_C_canonical_frame.full_ZF_denote_truth_correspondence"),
    ("a closed sentence is true exactly when it belongs to the world", "book_full_C_canonical_frame.full_ZF_closed_sentence_truth"),
    ("an open sentence is true exactly when its closed instance belongs to the world", "book_full_C_canonical_frame.full_ZF_substituted_sentence_truth"),
    ("actual pointwise graph application has the required type", "book_full_C_canonical_frame.full_ZF_app_type"),
    ("literal primitive symbols have typed represented values", "book_full_C_canonical_frame.full_ZF_logical_value_type"),
    ("literal primitive symbols denote those actual values", "book_full_C_canonical_frame.full_ZF_logical_denote"),
    ("implication has its truth clause on every represented proposition", "book_full_C_canonical_frame.full_ZF_implication_truth"),
    ("universal quantification ranges over the whole represented domain", "book_full_C_canonical_frame.full_ZF_forall_truth"),
    ("the actual represented interpretation satisfies the exact environment condition", "book_full_C_canonical_frame.full_ZF_full_environment"),
    ("the represented domain contains a displayed false proposition", "book_full_C_canonical_frame.full_ZF_false_proposition"),
    ("each represented world satisfies every full minimal general-model field", "book_full_C_canonical_frame.full_ZF_general_model")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-logical"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; distinct from the pure-HOL term-model audit\n"
    ^ "SCOPE: actual canonical per-world general-model and truth clauses; not the complete modal-model certificate or C completeness\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-logical-audit.txt")) [XML.Text report]
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
