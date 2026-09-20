theory Goodman_T6_Audit
  imports Goodman_T6_Transfer Goodman_Integration_Proof.Goodman_Extension_Rules_Audit
begin

section \<open>Final checkpoint: forward CEV+ preservation and all four T6 routes\<close>

ML \<open>
local
  val names =
    ["gi_prefix_types", "gi_prefix_distinct", "gi_prefix_length", "gi_arrow_fold",
     "gi_shift_by_prefix_alpha", "gi_translate_app_vec", "gi_translate_fresh_vars",
     "gi_alpha_fold_app", "gi_alpha_binary", "gi_alpha_expanded_iff", "gi_H_rule_raise_shift",
     "gi_map_rev", "gi_ordered_arguments", "gi_ordered_application_alpha",
     "gi_book_vector_language", "gi_ordered_vector_rule", "gi_zeta_body_order", "gi_H_body_order",
     "gi_HLE_preservation", "gi_C_preservation", "gi_CEV_base_preservation", "gi_CEV_to_book_full_C",
     "gi_CEV_axiom_preservation", "gi_H_translated_false_elim", "gi_CEV_closed_refutation",
     "gi_T6_core_closed", "gi_T6_TU_closed", "gi_T6_WI_closed",
     "gi_T6_Inv_refutation", "gi_T6_Inv_inconsistent",
     "gi_T6_TU_refutation", "gi_T6_TU_inconsistent",
     "gi_T6_WI_refutation", "gi_T6_WI_inconsistent",
     "gi_T6_RS_refutation", "gi_T6_RS_inconsistent"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "T6-transfer audit: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises="
      ^ string_of_int (Thm.nprems_of thm)
    else error ("T6-transfer audit: residual kernel obligations in " ^ name)
  val report = "GOODMAN-T6-TRANSFER-AUDIT: "
    ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: forward preservation; closed added stocks; full-F/minimal book extension; universal target signature.\n"
    ^ "T6: exact image stocks; native book_bottom; not a PP-alone refutation or a reflection theorem.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "t6-transfer-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn name =>
    name ^ ":\n" ^ XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of (Proof_Context.get_thm @{context} name)))))
    ["gi_CEV_axiom_preservation", "gi_CEV_closed_refutation",
     "gi_T6_Inv_refutation", "gi_T6_TU_refutation", "gi_T6_WI_refutation", "gi_T6_RS_refutation"])
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "t6-transfer-statements.txt")) [XML.Text statements]
in end
\<close>

end
