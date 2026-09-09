theory Bacon_Book_ZF_Ambient_Existence_Audit
  imports Bacon_Book_ZF_Ambient_Model_Existence
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("canonical independent interpretation clause: type", "book_full_C_canonical_frame.full_ZF_J_type"),
    ("canonical independent interpretation clause: variable", "book_full_C_canonical_frame.full_ZF_J_variable"),
    ("canonical independent interpretation clause: constant", "book_full_C_canonical_frame.full_ZF_J_constant"),
    ("canonical independent interpretation clause: logical", "book_full_C_canonical_frame.full_ZF_J_logical"),
    ("canonical independent interpretation clause: application", "book_full_C_canonical_frame.full_ZF_J_application"),
    ("canonical independent interpretation clause: abstraction", "book_full_C_canonical_frame.full_ZF_J_abstraction"),
    ("the canonical interpretation satisfies all independent clauses", "book_full_C_canonical_frame.full_ZF_canonical_interpretation"),
    ("the canonical interpretation is unique on typed inputs", "book_full_C_canonical_frame.full_ZF_canonical_interpretation_unique"),
    ("root validity agrees with the established per-world interpretation", "book_full_C_canonical_frame.full_ZF_root_validity_bridge"),
    ("membership of a universal closure ensures original formula validity", "book_full_C_canonical_frame.full_ZF_universal_closure_truth"),
    ("the canonical model satisfies every original premise", "book_full_C_canonical_frame.full_ZF_original_theory_satisfied"),
    ("every admissible canonical interpretation satisfies the original theory", "book_full_C_canonical_frame.full_ZF_original_theory_all_interpretations"),
    ("full-C consistency constructs an actual model in a fixed countable ambient signature", "book_countable_ambient_signature.book_full_C_ambient_modal_model_exists")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-ambient-existence"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; not pure HOL\n"
    ^ "SCOPE: Canonical independent interpretation and original-theory truth; actual full-C model existence in a fixed countable ambient signature with infinite reserves. Explicit future-restricted implication convention; not generic soundness or unrestricted completeness.\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-ambient-existence-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

end
