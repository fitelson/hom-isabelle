theory Bacon_Book_Term_Interpretation_Audit
  imports Bacon_Book_Term_Interpretation_Naturality
begin

ML_file "../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("H validates identity of typed convertible terms", "book_H_conversion_identity"),
    ("identity classes contain typed conversion equivalence", "book_C_identity_world.identity_class_conversion"),
    ("the canonical term interpretation is typed", "book_C_identity_world.book_C_term_denote_type"),
    ("the canonical term interpretation evaluates variables", "book_C_identity_world.book_C_term_denote_var"),
    ("closed terms denote their actual world identity classes", "book_C_identity_world.book_C_term_denote_closed"),
    ("the canonical term interpretation preserves application", "book_C_identity_world.book_C_term_denote_app"),
    ("the canonical term interpretation is local", "book_C_identity_world.book_C_term_denote_locality"),
    ("the canonical term interpretation respects raw typed conversion", "book_C_identity_world.book_C_term_denote_conversion"),
    ("the term interpretation satisfies the exact full environment condition", "book_C_identity_world.book_C_term_full_environment"),
    ("the term interpretation has the ordinary abstraction equation", "book_C_identity_world.book_C_term_lambda_application"),
    ("finitely many equivalent representative changes preserve the result class", "book_C_identity_world.identity_environment_finite_changes"),
    ("representative independence requires agreement only on free variables", "book_C_identity_world.identity_environment_representative_independence"),
    ("every suitable choice of closed representatives computes the same interpretation", "book_C_identity_world.book_C_term_denote_any_representatives"),
    ("every actual full-C world instantiates the constructed environment", "book_full_C_canonical_frame.full_term_environment"),
    ("counterpart transport preserves typed source assignments", "book_full_C_canonical_frame.full_term_assignment_move_typed"),
    ("the actual term interpretation commutes with counterparts", "book_full_C_canonical_frame.full_term_denote_natural")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-term-interpretation"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: pure HOL; no HOL-ZF import\n"
    ^ "SCOPE: actual identity-class interpretation, representative independence, exact environment condition and counterpart naturality; no modal-model or completeness claim\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-term-interpretation-audit.txt")) [XML.Text report]
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
