theory Bacon_Book_ZF_Nontrivial_Audit
  imports Bacon_Book_ZF_Countable_Nontrivial_Existence
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("every nontrivial world has actual typed assignments", "book_ZF_nontrivial_modal_model.typed_assignment_exists"),
    ("nontriviality survives semantic signature pullback", "book_ZF_nontrivial_modal_model.nontrivial_signature_pullback"),
    ("a nontrivial model has a false proposition at its root", "book_ZF_nontrivial_modal_model.false_at_root"),
    ("no nontrivial world makes every proposition true", "book_ZF_nontrivial_modal_model.not_all_propositions_true"),
    ("canonical reindexed domains are inhabited", "book_full_C_coded_frame.full_ZF_reindexed_domains_nonempty"),
    ("each canonical reindexed world has a false proposition", "book_full_C_coded_frame.full_ZF_reindexed_false_at_world"),
    ("the canonical model satisfies the explicit nontrivial refinement", "book_full_C_coded_frame.full_ZF_canonical_nontrivial_modal_model"),
    ("fixed-ambient consistency constructs a nontrivial model", "book_coded_ambient_signature.book_full_C_ambient_nontrivial_modal_model_exists"),
    ("countably declared consistent theories have nontrivial original-signature models", "book_full_C_countable_nontrivial_modal_model_exists")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-nontrivial"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; not pure HOL\n"
    ^ "SCOPE: explicit nontrivial-model refinement and actual canonical and countably declared existence on arbitrary name carriers; generic soundness and completeness are certified by the modal soundness audit, not here\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-nontrivial-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

end
