theory Goodman_Modal_Integration_Audit
  imports Goodman_Modal_Package_Preservation
begin

section \<open>Kernel audit of modal abbreviations and native package preservation\<close>

ML \<open>
local
  val names =
    ["gi_true_translation", "gi_old_top_language", "gi_old_top_closed",
     "book_full_minimal_model.gi_old_top_true", "gi_H_truth_equivalence",
     "gi_goodman_truth_identity", "gi_H_box_representative", "gi_goodman_box_equivalence",
     "gi_translated_box_equivalence", "gi_H_iff_reflexive", "gi_goodman_iff_reflexive",
     "gi_H_iff_imp_congruence", "gi_goodman_iff_imp_congruence",
     "gi_H_iff_all_congruence", "gi_goodman_iff_all_congruence",
     "gi_H_iff_forward", "gi_H_iff_symmetric", "gi_goodman_iff_transport",
     "gi_goodman_equivalent_proofs", "gi_gb_z_reversed",
     "gi_zeroary_recombination_shape", "gi_zeroary_exhaustion_shape",
     "gi_unary_recombination_shape", "gi_unary_exhaustion_shape", "gi_persistence_shape",
     "gi_gb_universal_language", "gi_zeroary_recombination_equivalence",
     "gi_zeroary_exhaustion_equivalence", "gi_unary_recombination_equivalence",
     "gi_unary_exhaustion_equivalence", "gi_persistence_equivalence",
     "gi_axiom_from_native_equivalent", "gi_zeroary_recombination_from_native",
     "gi_zeroary_exhaustion_from_native", "gi_unary_recombination_from_native",
     "gi_unary_exhaustion_from_native", "gi_persistence_from_native",
     "gi_background_axiom_from_native", "gi_PP_axiom_from_native",
     "gi_native_package_preservation", "gi_recombination_package_support",
     "gi_QLN_package_support", "gi_recombination_PP_preservation", "gi_QLN_PP_preservation",
     "gi_repaired_package_support", "gi_repaired_PP_preservation",
     "gi_persistent_QLN_package_support", "gi_persistent_QLN_PP_preservation",
     "gi_native_consistency_implies_CEV_axiom_consistency",
     "gi_recombination_PP_consistency_transfer", "gi_QLN_PP_consistency_transfer",
     "gi_repaired_PP_consistency_transfer", "gi_persistent_QLN_PP_consistency_transfer"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Modal-integration audit: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises="
      ^ string_of_int (Thm.nprems_of thm)
    else error ("Modal-integration audit: residual kernel obligations in " ^ name)
  val report = "GOODMAN-MODAL-INTEGRATION-AUDIT: "
    ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: proved truth identity and Box equivalence; zeroary/unary QLN and persistence; forward native package preservation.\n"
    ^ "Whole-proof targets retain the universal signature. Native consistency is a hypothesis, not a result.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "modal-integration-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn name =>
    name ^ ":\n" ^ XML.content_of (YXML.parse_body (Syntax.string_of_term @{context}
      (Thm.prop_of (Proof_Context.get_thm @{context} name))))) names)
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "modal-integration-statements.txt")) [XML.Text statements]
in end
\<close>

end
