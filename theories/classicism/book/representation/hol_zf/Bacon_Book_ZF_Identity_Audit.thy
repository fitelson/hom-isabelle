theory Bacon_Book_ZF_Identity_Audit
  imports Bacon_Book_ZF_Equality_Future_Value
begin

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("Leibniz equivalence is preserved and reflected by the representation", "book_full_C_coded_frame.full_ZF_leibniz_h_iff"),
    ("Leibniz equivalence is actual equality at every represented full type", "book_full_C_coded_frame.full_ZF_leibniz_iff_equal"),
    ("the literal Leibniz formula expresses actual equality under typed assignments", "book_full_C_coded_frame.full_ZF_identity_truth"),
    ("coded future truth sets are extensional on their actual worlds", "book_full_C_coded_frame.full_ZF_future_set_extensional"),
    ("a typed proposition is identified with its complete future comprehension", "book_full_C_coded_frame.full_ZF_proposition_eq_collect"),
    ("future truth agrees with membership in the original proposition", "book_full_C_coded_frame.full_ZF_proposition_future_truth"),
    ("closed canonical values belong to their represented domains", "book_full_C_coded_frame.full_ZF_closed_value_type"),
    ("closed canonical values commute with counterparts", "book_full_C_coded_frame.full_ZF_closed_value_natural"),
    ("closed canonical values preserve application", "book_full_C_coded_frame.full_ZF_closed_value_application"),
    ("literal primitive values commute with counterparts", "book_full_C_coded_frame.full_ZF_logical_value_natural"),
    ("future application agrees with application of the restricted graph", "book_full_C_coded_frame.full_ZF_future_application"),
    ("future graph application has the correct result type", "book_full_C_coded_frame.full_ZF_future_application_type"),
    ("pointwise graph application commutes with counterparts", "book_full_C_coded_frame.full_ZF_app_natural"),
    ("the actual closed equality operator belongs to its function domain", "book_full_C_coded_frame.full_ZF_equality_value_type"),
    ("the actual equality operator commutes with counterparts", "book_full_C_coded_frame.full_ZF_equality_value_natural"),
    ("the actual equality operator tests every typed pair", "book_full_C_coded_frame.full_ZF_equality_value_truth"),
    ("the actual equality result is the whole future equality set", "book_full_C_coded_frame.full_ZF_equality_result"),
    ("the root equality operator has the exact two-stage future behavior", "book_full_C_coded_frame.full_ZF_equality_future_value")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-identity"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; distinct from the pure-HOL term-identity audit\n"
    ^ "SCOPE: actual all-type equality and Definition 18.1(3.5) future equality operator on the coded full-C frame (arbitrary name carrier); no complete modal-model or completeness claim\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-identity-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

text \<open>
  Actual identity is proved, not added as a model field. This
  certificate does not assert complete modal-model membership,
  the remaining operation/combinator conditions, or C completeness.
  Statement and type-class premises remain explicit.
\<close>

end
