theory Bacon_Book_ZF_Modal_Soundness_Audit
  imports Bacon_Book_ZF_Full_C_Declared_Names_Completeness
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("denotations are natural under counterparts", "book_ZF_modal_interpretation.denote_natural"),
    ("denotations depend only on free variables", "book_ZF_modal_interpretation.denote_coincidence"),
    ("future membership is future truth under the moved assignment", "book_ZF_modal_interpretation.truth_at_future"),
    ("implication clause (future-restricted complement)", "book_ZF_modal_interpretation.truth_imp"),
    ("universal quantifier clause over the current domain", "book_ZF_modal_interpretation.truth_all"),
    ("bottom clause", "book_ZF_modal_interpretation.truth_bottom"),
    ("classical negation where bottom is false", "book_ZF_modal_interpretation.truth_not_classical"),
    ("unconditional biconditional clause", "book_ZF_modal_interpretation.truth_iff"),
    ("quantifier clause for an arbitrary predicate term", "book_ZF_modal_interpretation.truth_all_predicate"),
    ("the model's equality operation is an available predicate", "book_ZF_modal_interpretation.equality_predicate_available"),
    ("the model's equality operation separates values", "book_ZF_modal_interpretation.equality_predicate_separates"),
    ("Leibniz identity is value identity", "book_ZF_modal_interpretation.truth_leibniz"),
    ("the literal box is truth at every future world", "book_ZF_modal_interpretation.truth_box"),
    ("semantic substitution under the free-for guard", "book_ZF_modal_interpretation.denote_subst"),
    ("beta steps preserve denotation in every context", "book_ZF_modal_interpretation.denote_beta_step"),
    ("eta steps preserve denotation in every context", "book_ZF_modal_interpretation.denote_eta_step"),
    ("H theory derivations preserve validity at a world", "book_ZF_modal_interpretation.theory_derivable_valid_at"),
    ("every H theorem is valid at every world", "book_ZF_modal_interpretation.H_valid_at"),
    ("iterated quantification varies exactly the listed variables", "book_ZF_modal_interpretation.truth_all_list"),
    ("semantic universal closure is validity at the world", "book_ZF_modal_interpretation.truth_universal_closure"),
    ("bottom is false at every world of a nontrivial model", "book_ZF_nontrivial_modal_interpretation.bottom_false_at"),
    ("Modalized Functionality is valid at every world", "book_ZF_nontrivial_modal_interpretation.MF_valid_at"),
    ("Propositional Equivalence preserves validity everywhere", "book_ZF_nontrivial_modal_interpretation.PE_valid_everywhere"),
    ("every full-C theorem is valid at every world", "book_ZF_nontrivial_modal_interpretation.full_C_valid_everywhere"),
    ("full-C theory derivations are valid at the root", "book_ZF_nontrivial_modal_interpretation.full_C_theory_valid_at_root"),
    ("satisfiable theories are consistent", "book_ZF_nontrivial_modal_interpretation.satisfiable_theory_consistent"),
    ("full-C theory soundness over the nontrivial class", "book_full_C_theory_sound"),
    ("satisfiable theories are consistent (external form)", "book_full_C_satisfiable_consistent"),
    ("full-C theory completeness from model existence", "book_full_C_theory_complete_from_existence"),
    ("full-C theory completeness for countably declared signatures", "book_full_C_theory_complete"),
    ("full-C derivability iff modal consequence", "book_full_C_theory_derivable_iff_consequence"),
    ("full-C consistency iff satisfiability", "book_full_C_theory_consistent_iff_satisfiable"),
    ("full-C theory completeness for ZF-small name carriers", "book_full_C_theory_complete_small_carrier"),
    ("full-C derivability iff modal consequence for ZF-small name carriers", "book_full_C_theory_derivable_iff_consequence_small_carrier"),
    ("full-C consistency iff satisfiability for ZF-small name carriers", "book_full_C_theory_consistent_iff_satisfiable_small_carrier"),
    ("full-C derivability iff modal consequence over the uncountable carrier nat set", "book_full_C_theory_derivable_iff_consequence_nat_set"),
    ("full-C consistency iff satisfiability over the uncountable carrier nat set", "book_full_C_theory_consistent_iff_satisfiable_nat_set"),
    ("full-C theory completeness for ZF-small declared names on an arbitrary carrier", "book_full_C_theory_complete_small_declared"),
    ("full-C derivability iff modal consequence for ZF-small declared names on an arbitrary carrier", "book_full_C_theory_derivable_iff_consequence_small_declared"),
    ("full-C consistency iff satisfiability for ZF-small declared names on an arbitrary carrier", "book_full_C_theory_consistent_iff_satisfiable_small_declared"),
    ("full-C derivability iff modal consequence on carrier ZF with set-bounded declared names", "book_full_C_theory_derivable_iff_consequence_ZF_carrier"),
    ("full-C consistency iff satisfiability on carrier ZF with set-bounded declared names", "book_full_C_theory_consistent_iff_satisfiable_ZF_carrier")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-modal-soundness"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; not pure HOL\n"
    ^ "SCOPE: generic full-type C soundness for nontrivial book modal models with no signature-size restriction; completeness for signatures whose declared-name union has an injective code bounded by a ZF set, on an arbitrary carrier including the type ZF with set-bounded declared names, subsuming the retained countably declared and ZF-small-carrier scopes; rich stock, full minimal language, root consequence; declared unions with no bounded injection are outside this construction\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-modal-soundness-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

end
