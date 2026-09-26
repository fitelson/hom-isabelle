theory Bacon_Book_ZF_Representation_Audit
  imports Bacon_Book_ZF_Arrow_Homomorphisms
begin

section \<open>Separate HOL–ZF audit of the all-type book representation\<close>

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("term-set codes have exact elements", "book_full_C_coded_frame.class_code_elements"),
    ("term-set codes have a proved powerset bound", "book_full_C_coded_frame.class_codes_bound"),
    ("actual world codes are bijective on the canonical frame", "book_full_C_coded_frame.full_world_code_bijection"),
    ("actual term-class domains have exact coded carriers", "book_full_C_coded_frame.book_ZF_term_class_domain_bijection"),
    ("Replacement constructs each represented image as an actual set", "book_full_C_coded_frame.book_ZF_powerset_image_elements"),
    ("future pairs have the exact world and argument membership condition", "book_full_C_coded_frame.full_ZF_future_pair_member"),
    ("the all-type range sets have their exact elements", "book_full_C_coded_frame.full_ZF_D_elements"),
    ("every represented arrow is a function graph on its exact pair domain", "book_full_C_coded_frame.full_ZF_arrow_domain"),
    ("graph evaluation agrees with transported term application", "book_full_C_coded_frame.full_ZF_arrow_value"),
    ("the single recursive representation is injective at every full type", "book_full_C_coded_frame.full_ZF_h_injective"),
    ("the single recursive representation is bijective at every full type", "book_full_C_coded_frame.full_ZF_h_bijection"),
    ("the inverse recovers every source class", "book_full_C_coded_frame.full_ZF_jh"),
    ("the forward map recovers every represented value", "book_full_C_coded_frame.full_ZF_hj"),
    ("all recursively represented domains form modalized sets", "book_full_C_coded_frame.full_ZF_domains_modalized"),
    ("all recursive representation maps are modalized bijections", "book_full_C_coded_frame.full_ZF_representation_bijection"),
    ("every recursively represented domain is nonempty", "book_full_C_coded_frame.full_ZF_domains_nonempty"),
    ("the arrow representation commutes with literal graph restriction", "book_full_C_coded_frame.full_ZF_h_arrow_restriction"),
    ("arrow counterparts are literal graph restrictions", "book_full_C_coded_frame.full_ZF_i_arrow_restriction"),
    ("actual graph application preserves term application", "book_full_C_coded_frame.full_ZF_application_preserved"),
    ("proposition counterparts are literal future truncations", "book_full_C_coded_frame.full_ZF_i_proposition_restriction"),
    ("every proposition value is a subset of its future", "book_full_C_coded_frame.full_ZF_proposition_future"),
    ("the individual domain equals the coded term domain", "book_full_C_coded_frame.full_ZF_individual_domain"),
    ("every recursive arrow value decodes to a genuine future homomorphism", "book_full_C_coded_frame.full_ZF_arrow_domain_homomorphisms")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-representation"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; distinct from the pure-HOL core audit\n"
    ^ "SCOPE: one all-full-type recursive family on the coded full-C canonical frame; inverse, modalized-set, exact restriction, application and future-homomorphism laws; no complete modal-model or completeness claim\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-representation-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

text \<open>
  The kernel check rejects oracle dependencies, residual hypotheses and
  flex-flex constraints. The standard HOL–ZF axioms are the declared
  metalogical foundation, not new object-theory axioms. Countability
  and the canonical-frame assumptions remain explicit in the theorem
  statements. Logical-operation closure, the complete λ interpretation
  and the final modal-model/truth certificate remain separate obligations.
\<close>

end
