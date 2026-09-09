theory Bacon_Book_ZF_Model_Definition_Audit
  imports Bacon_Book_ZF_Model_Operator_Restriction Bacon_Book_ZF_Model_Graph_Regression
    Bacon_Book_ZF_Model_Function_Extensionality
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("dependent future pairs have their exact typed membership condition", "book_ZF_pairs_member"),
    ("single-valuedness and domain equality alone do not exclude non-pair junk", "book_ZF_isFun_domain_insufficient"),
    ("actual Lambda graphs reconstruct from their application", "book_ZF_graph_eta"),
    ("the prescribed k graph has its two-stage behavior", "book_ZF_k_value"),
    ("the prescribed s graph has its three-stage behavior", "book_ZF_s_value"),
    ("the prescribed implication graph has its explicit future-domain behavior", "book_ZF_if_future_value"),
    ("the prescribed universal graph has its full future behavior", "book_ZF_all_value"),
    ("the prescribed identity graph has its future equality behavior", "book_ZF_eq_value"),
    ("exact graph reconstruction implies single-valuedness and the required domain", "book_ZF_modal_structure.function_graph_domain"),
    ("the fixed root logical interpretation is typed in every independent model", "book_ZF_modal_model.logical_root_type"),
    ("restriction of an outer future family changes only its domain", "book_ZF_frame.outer_function_restriction"),
    ("root k membership yields membership at every world", "book_ZF_modal_model.k_member_at"),
    ("root s membership yields membership at every world", "book_ZF_modal_model.s_member_at"),
    ("root implication membership yields membership at every world", "book_ZF_modal_model.implication_member_at"),
    ("root universal membership yields membership at every world", "book_ZF_modal_model.universal_member_at"),
    ("root identity membership yields membership at every world", "book_ZF_modal_model.identity_member_at"),
    ("exact graph fields imply future quasi-functionality", "book_ZF_modal_structure.future_function_extensionality"),
    ("typed future behavior identifies an actual function with its prescribed Lambda graph", "book_ZF_modal_structure.function_as_lambda")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-model-definition"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; not pure HOL\n"
    ^ "SCOPE: independent Definition 18.1 data and prescribed operations, exact graph regression and all-world operator membership; no interpreter or completeness claim\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-model-definition-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

text \<open>
  Kernel cleanliness does not erase the displayed model/structure
  premises or establish a complete canonical modal-model certificate.
  Operator identification, root constants and final semantics retain
  their separate proof obligations. No oracle or residual kernel
  hypothesis is accepted by this audit.
\<close>

end
