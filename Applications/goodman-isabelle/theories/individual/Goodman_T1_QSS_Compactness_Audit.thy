theory Goodman_T1_QSS_Compactness_Audit
  imports Goodman_T1_Transfer
    Goodman_Integration_Central_Stock.Goodman_Native_QSS
    Goodman_Integration_T6.Goodman_Extension_Finite_Support
begin

section \<open>Audit of individual T1, native QSS, and finite proof support\<close>

ML \<open>
local
  val names =
    ["gb_QSS_instance_language", "gb_QSS_language", "gb_QSS_instance_fv", "gb_QSS_closed",
     "gi_QSS_admitted", "gi_QSS_translation", "gi_repaired_native_QSS",
     "gi_QSS_unique_native_stock_exists", "gi_native_exists_fun_prime_from_QSS",
     "goodman_book_finite_support", "goodman_book_proves_iff_finite_support",
     "goodman_book_consistent_subset", "goodman_book_consistent_iff_finite_subsets",
     "goodman_book_inconsistent_iff_finite_refutation",
     "goodman_book_inconsistent_iff_finite_inconsistent_subset",
     "gb_recombination_PP_consistent_iff_finite_subsets",
     "gb_recombination_PP_negative_answer_iff_finite_refutation",
     "gi_T1_axioms_closed", "gb_T1_axioms_language", "gb_T1_axioms_closed",
     "gi_T1_axiom_from_native", "gi_T1_native_preservation", "gi_T1_extreme_admitted",
     "gi_T1_pure_propositions_extreme_translated", "gi_T1_extreme_translation",
     "gi_T1_pure_extreme_translation", "gi_T1_pure_propositions_extreme",
     "gi_T1_identity_operator_translation", "gi_T1_negation_operator_translation",
     "gi_T1_biconditional_operator_translation", "gi_T1_biconditional_classification_admitted",
     "gi_T1_biconditional_classification_translated", "gi_T1_biconditional_classification",
     "gi_T1_WI_axioms_closed", "gi_T1_WI_native_stock_language", "gi_T1_WI_axiom_from_native",
     "gi_T1_WI_implies_Inv_translated"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "T1/QSS/compactness: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("T1/QSS/compactness: residual obligations in " ^ name)
  val report = "GOODMAN-T1-QSS-COMPACTNESS-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: T1 minimal stock with zeroary Exhaustion; independent QSS/witness; actual axiom-extension finite support.\n"
    ^ "T1 retains source truth/falsity representatives; WI/Inv remain translated. No semantic compactness/model existence asserted.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t1-qss-compactness-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t1-qss-compactness-statements.txt")) [XML.Text statements]
in end
\<close>

end
