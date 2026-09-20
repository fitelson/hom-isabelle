theory Goodman_Exact_M5_Classifications_Audit
  imports Goodman_Exact_M5_Classifications
begin

ML \<open>
local
  val names = ["gi_M5_negation_value", "gi_M5_identity_application", "gi_M5_negation_application_truth",
    "gi_M5_identity_at_root_implies_preserving", "gi_M5_negation_at_root_implies_flipping",
    "gi_M5_Inv_root_classifies_group_member", "gi_exact_M5_rebuilt_Inv_false_at_root",
    "gi_M5_Inv_vocabulary", "gi_exact_M5_native_Inv_false_at_root", "gi_exact_M5_native_Inv_not_global",
    "gi_M5_Inv_not_derivable_from_QLN_background", "gi_M5_WI_entails_TU",
    "gi_M5_WI_not_derivable_from_QLN_background", "gi_exact_M5_native_WI_not_global"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "m5-classifications: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("m5-classifications: residual obligations in " ^ name)
  val report = "M5-CLASSIFICATIONS-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: actual rebuilt Inv root failure; native Inv and WI nonderivability from the explicit no-PP QLN background; WI failure of global validity via checked singleton-WI=>TU consequence. No WI root-falsity, added Persistence/Pure(Fun)/PP, or arbitrary pure-stock claim. HOL-ZF.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-classifications-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-classifications-statements.txt")) [XML.Text statements]
in end
\<close>

end
