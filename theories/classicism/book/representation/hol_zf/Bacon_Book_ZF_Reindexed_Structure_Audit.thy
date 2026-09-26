theory Bacon_Book_ZF_Reindexed_Structure_Audit
  imports Bacon_Book_ZF_Reindexed_Structure
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("the actual world codes instantiate the independent pointed frame", "book_full_C_coded_frame.full_ZF_reindexed_frame"),
    ("all actual reindexed domains are modalized sets", "book_full_C_coded_frame.full_ZF_reindexed_domains"),
    ("the independent future set is the actual canonical future set", "book_full_C_coded_frame.full_ZF_reindexed_future"),
    ("the independent pair domain is the actual canonical pair domain", "book_full_C_coded_frame.full_ZF_reindexed_pairs"),
    ("the independent restriction is the actual canonical restriction", "book_full_C_coded_frame.full_ZF_reindexed_restriction"),
    ("the actual graph functions satisfy the full future homomorphism equation", "book_full_C_coded_frame.full_ZF_future_homomorphism_equation"),
    ("every actual reindexed function is exactly its Lambda graph", "book_full_C_coded_frame.full_ZF_reindexed_graph_exact"),
    ("every actual reindexed function has typed future outputs", "book_full_C_coded_frame.full_ZF_reindexed_function_type"),
    ("actual reindexed functions commute with counterparts", "book_full_C_coded_frame.full_ZF_reindexed_function_natural"),
    ("actual reindexed function counterparts are restrictions", "book_full_C_coded_frame.full_ZF_reindexed_function_restriction"),
    ("actual reindexed propositions are future subsets", "book_full_C_coded_frame.full_ZF_reindexed_propositions"),
    ("actual reindexed proposition counterparts are truncations", "book_full_C_coded_frame.full_ZF_reindexed_proposition_restriction"),
    ("the construction instantiates every independent modalized-structure field", "book_full_C_coded_frame.full_ZF_reindexed_structure")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-reindexed-structure"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; not pure HOL\n"
    ^ "SCOPE: actual coded canonical frame (arbitrary name carrier) reindexed into the independent exact modalized-structure predicate; not the complete modal-model or completeness certificate\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-reindexed-structure-audit.txt")) [XML.Text report]
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
