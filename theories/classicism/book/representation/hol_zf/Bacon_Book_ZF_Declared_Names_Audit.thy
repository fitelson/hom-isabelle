theory Bacon_Book_ZF_Declared_Names_Audit
  imports Bacon_Book_ZF_Declared_Names_Existence
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("term-set codes are injective on admitted term sets", "book_full_C_coded_frame.class_code_injective"),
    ("term-set codes have exact element sets", "book_full_C_coded_frame.class_code_elements"),
    ("the class decoder inverts admitted term-set codes", "book_full_C_coded_frame.class_code_inverse"),
    ("Replacement images are exact on admitted term-set families", "book_full_C_coded_frame.book_ZF_powerset_image_elements"),
    ("canonical-world sentence sets are admitted term sets", "book_full_C_coded_frame.world_sentences_admitted"),
    ("identity classes at pairs inside the ambient signature are admitted term sets", "book_full_C_coded_frame.identity_domain_admitted"),
    ("the class decoder is typed on coded identity domains at admitted pairs", "book_full_C_coded_frame.book_ZF_term_class_decode_type"),
    ("world codes are injective on the rooted worlds", "book_full_C_coded_frame.full_world_code_injective"),
    ("domain elements are exactly the coded identity classes at admitted pairs", "book_full_C_coded_frame.full_ZF_D_elements"),
    ("the recursive inverse is a right inverse at admitted pairs", "book_full_C_coded_frame.full_ZF_hj"),
    ("assignment decoding is typed at admitted pairs", "book_full_C_coded_frame.full_ZF_assignment_decode_typed"),
    ("individual coding is injective at admitted pairs", "book_full_C_coded_frame.full_ZF_individual_injective"),
    ("the declared-name reserve contains the recoded declared signature", "book_ZF_declared_included"),
    ("the declared-name reserve leaves an infinite unused part at every type", "book_ZF_declared_reserve"),
    ("the declared-name reserve dominates the whole recoded declared union", "book_ZF_declared_large"),
    ("the recoded declared signature is an ambient signature inside the declared-name reserve", "book_ZF_declared_ambient"),
    ("the tagged name code is injective on declared-or-reserve names", "book_ZF_declared_name_code_injective"),
    ("the tagged name code is bounded on declared-or-reserve names", "book_ZF_declared_name_code_bound"),
    ("the tagged carrier bound is infinite without whole-carrier smallness", "book_ZF_carrier_bound_infinite_always"),
    ("the default code lies in the tagged carrier bound", "book_ZF_carrier_bound_default"),
    ("terms admitted by the declared-name reserve have a total bounded code injective on them", "book_ZF_small_declared_term_code"),
    ("the recoded declared signature is a coded ambient signature", "book_ZF_declared_coded_ambient"),
    ("whole-carrier smallness gives small declared names", "book_ZF_small_carrier_declared"),
    ("countably declared names give small declared names", "book_ZF_countable_declared"),
    ("consistent theories with small declared names have nontrivial original-signature models", "book_full_C_small_declared_nontrivial_modal_model_exists"),
    ("consistent theories on carrier ZF with set-bounded declared names have nontrivial models", "book_full_C_ZF_carrier_nontrivial_modal_model_exists"),
    ("the small-carrier existence theorem follows from the declared-names theorem", "book_full_C_small_carrier_nontrivial_modal_model_exists_from_small_declared"),
    ("the countably declared existence theorem follows from the declared-names theorem", "book_full_C_countable_nontrivial_modal_model_exists_from_small_declared"),
    ("the countably declared existence theorem is retained", "book_full_C_countable_nontrivial_modal_model_exists"),
    ("the small-carrier existence theorem is retained", "book_full_C_small_carrier_nontrivial_modal_model_exists"),
    ("the nat set existence theorem is retained", "book_full_C_nat_set_carrier_nontrivial_modal_model_exists")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-declared-names"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; not pure HOL\n"
    ^ "SCOPE: original-signature nontrivial model existence for signatures whose declared-name union has an injective code bounded by a ZF set, on an arbitrary HOL name carrier, including the type ZF with set-bounded declared names; the countable and whole-carrier theorems are subsumed and retained; term codes are total, bounded and injective on terms admitted by the ambient signature; declared unions with no bounded injection are outside this construction\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-declared-names-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

end
