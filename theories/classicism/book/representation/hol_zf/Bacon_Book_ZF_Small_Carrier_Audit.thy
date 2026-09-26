theory Bacon_Book_ZF_Small_Carrier_Audit
  imports Bacon_Book_ZF_Small_Carrier_Existence Bacon_Book_ZF_World_Codes
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("the finite syntax code of book terms is injective", "book_finite_syntax_code_injective"),
    ("terms over a bounded signature are cardinally bounded", "book_admitted_syntax_cardinal_bound"),
    ("all terms over a bounded carrier are cardinally bounded", "book_all_terms_cardinal_bound"),
    ("each Henkin stage signature is cardinally bounded", "book_henkin_stage_names_cardinal_bound"),
    ("the full Henkin signature is cardinally bounded", "book_henkin_full_names_cardinal_bound"),
    ("the general ambient name map is injective on the used Henkin names", "book_ambient_signature.book_ambient_name_map_injective"),
    ("the general ambient name map fixes declared names", "book_ambient_signature.book_ambient_name_map_fixes"),
    ("the enlarged signature contains the declared signature", "book_ambient_signature.book_ambient_henkin_signature_contains"),
    ("the enlarged signature stays inside the ambient signature", "book_ambient_signature.book_ambient_henkin_signature_inside"),
    ("the enlarged signature leaves an infinite reserve", "book_ambient_signature.book_ambient_henkin_signature_reserve"),
    ("the enlarged signature leaves a reserve at least as large as itself", "book_ambient_signature.book_ambient_henkin_signature_large"),
    ("the enlarged signature is again an ambient signature", "book_ambient_signature.book_ambient_henkin_signature_ambient"),
    ("full-C canonical worlds carry the cardinal reserve condition", "book_full_C_canonical_world_reserve_large"),
    ("term-set codes of the coded frame are injective on admitted term sets", "book_full_C_coded_frame.class_code_injective"),
    ("term-set codes of the coded frame are bounded", "book_full_C_coded_frame.class_codes_bound"),
    ("countable carriers are ZF-small", "book_ZF_small_carrier_countable"),
    ("powersets of ZF-small carriers are ZF-small", "book_ZF_small_carrier_powerset"),
    ("the uncountable carrier nat set is ZF-small", "book_ZF_small_carrier_nat_set"),
    ("the recoded carrier is ZF-small", "book_ZF_carrier_code_small"),
    ("terms over the recoded carrier have a bounded injective code", "book_ZF_small_carrier_term_code"),
    ("the recoded signature is a coded ambient signature", "book_ZF_recoded_coded_ambient"),
    ("coded ambient consistency constructs a nontrivial model", "book_coded_ambient_signature.book_full_C_ambient_nontrivial_modal_model_exists"),
    ("consistent theories over ZF-small carriers have nontrivial original-signature models", "book_full_C_small_carrier_nontrivial_modal_model_exists"),
    ("consistent theories over nat set have nontrivial original-signature models", "book_full_C_nat_set_carrier_nontrivial_modal_model_exists"),
    ("countably declared consistent theories on arbitrary carriers still have nontrivial models", "book_full_C_countable_nontrivial_modal_model_exists"),
    ("on countable carriers the coded-frame class code is the earlier countable set code", "book_countable_class_code"),
    ("on countable carriers the coded-frame world code is the earlier countable world code", "book_countable_world_code")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-small-carrier"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; not pure HOL\n"
    ^ "SCOPE: cardinal name reserves, bounded term codes and original-signature nontrivial model existence for ZF-small name carriers, with no restriction on declared-name cardinality; the countably declared theorem on arbitrary carriers, including ZF, is retained, and the generalized coded-frame class and world codes agree with the earlier countable codes on countable carriers; the whole HOL type ZF does not satisfy the small-carrier hypothesis\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-small-carrier-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

end
