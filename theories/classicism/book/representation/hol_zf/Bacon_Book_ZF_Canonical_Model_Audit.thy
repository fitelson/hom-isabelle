theory Bacon_Book_ZF_Canonical_Model_Audit
  imports Bacon_Book_ZF_Canonical_Modal_Model
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("typed two-stage future behavior identifies the prescribed curried graph", "book_ZF_modal_structure.function_as_two_lambdas"),
    ("typed three-stage future behavior identifies the prescribed curried graph", "book_ZF_modal_structure.function_as_three_lambdas"),
    ("future comprehensions commute with the actual world-code reindexing", "book_full_C_canonical_frame.full_ZF_collect_reindex"),
    ("compatible predicates give the same future comprehension after reindexing", "book_full_C_canonical_frame.full_ZF_collect_compatible"),
    ("the canonical k is exactly the independently prescribed k graph", "book_full_C_canonical_frame.full_ZF_K_identification"),
    ("the canonical s is exactly the independently prescribed s graph", "book_full_C_canonical_frame.full_ZF_S_identification"),
    ("the canonical implication is exactly the prescribed future-restricted graph", "book_full_C_canonical_frame.full_ZF_implication_identification"),
    ("the canonical universal operator is exactly the prescribed graph", "book_full_C_canonical_frame.full_ZF_universal_identification"),
    ("the canonical identity operator is exactly the prescribed graph", "book_full_C_canonical_frame.full_ZF_identity_identification"),
    ("all original declared constants have actual typed root values", "book_full_C_canonical_frame.full_ZF_constant_value_type"),
    ("original constants denote the counterparts of their actual root values", "book_full_C_canonical_frame.full_ZF_original_constant_denote"),
    ("the primitive root interpretations equal the independent prescribed values", "book_full_C_canonical_frame.full_ZF_logical_root_identification"),
    ("the canonical data instantiate every independent modal-model field", "book_full_C_canonical_frame.full_ZF_canonical_modal_model"),
    ("the canonical primitive denotations have the independent root interpretation", "book_full_C_canonical_frame.full_ZF_root_logical_denote")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-canonical-model"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; not pure HOL\n"
    ^ "SCOPE: Proposition 18.5 canonical modal-model certificate for the countable-name full-C frame, with the explicit future-domain implication convention; not generic interpretation, soundness or Theorem 18.4 completeness\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-canonical-model-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

text \<open>
  The endpoint is the independent modal-model predicate, not a
  structure-only or per-world general-model substitute. Its displayed
  canonical-frame premise and foundation remain explicit. Generic
  evaluation and the final semantic theorems are not supplied by
  this certificate. Oracle dependencies and residual kernel
  obligations are rejected by the audit.
\<close>

end
