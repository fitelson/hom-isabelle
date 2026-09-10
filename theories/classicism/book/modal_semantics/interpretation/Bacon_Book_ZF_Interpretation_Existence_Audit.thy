theory Bacon_Book_ZF_Interpretation_Existence_Audit
  imports Bacon_Book_ZF_Generic_Interpretation_Existence
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("typed K/S abstraction elimination", "book_comb_abstract_typed"),
    ("object-language translation preserves typing", "book_combinatory_translation_language"),
    ("generic k evaluation", "book_ZF_modal_model.generic_k_current"),
    ("generic s evaluation", "book_ZF_modal_model.generic_s_current"),
    ("derived identity belongs to every typed function domain", "book_ZF_modal_model.generic_identity_type"),
    ("derived identity has the exact future graph", "book_ZF_modal_model.generic_identity_graph"),
    ("combinatory evaluation remains in the chosen domains", "book_ZF_modal_model.generic_comb_eval_type"),
    ("combinatory evaluation commutes with counterparts", "book_ZF_modal_model.generic_comb_eval_natural"),
    ("abstracted combinatory evaluation has current beta behavior", "book_ZF_modal_model.generic_comb_abstract_current"),
    ("abstracted combinatory evaluation has future beta behavior", "book_ZF_modal_model.generic_comb_abstract_future"),
    ("abstraction is the exact future Lambda graph", "book_ZF_modal_model.generic_comb_abstract_graph"),
    ("constructed generic interpretation satisfies every independent clause", "book_ZF_modal_model.generic_interpretation_model"),
    ("every independent modal model has an admissible interpretation", "book_ZF_modal_model.generic_interpretation_exists"),
    ("constructed interpretation commutes with counterparts", "book_ZF_modal_model.generic_interpretation_natural"),
    ("admissible interpretations agree on every typed input", "book_ZF_modal_interpretation.interpretation_unique")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-interpretation-existence"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; not pure HOL\n"
    ^ "SCOPE: Generic interpretation existence for every independent full-minimal modal model, via typed K/S abstraction elimination; exact future Lambda graphs, type closure, naturality and typed-input uniqueness. No countability, richness, supplied interpreter or extra nonemptiness premise. Existing future-restricted implication convention unchanged. Not generic soundness or completeness.\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-interpretation-existence-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

end
