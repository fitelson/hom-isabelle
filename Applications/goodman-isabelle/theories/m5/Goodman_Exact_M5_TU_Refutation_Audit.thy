theory Goodman_Exact_M5_TU_Refutation_Audit
  imports Goodman_Exact_M5_TU_Refutation
begin

ML \<open>
local
  val names = ["gi_M5_identity_value", "gi_M5_truth_preserving_value", "gi_M5_truth_flipping_value",
    "gi_exact_expanded_stock.gi_M5_rebuilt_group_member_value",
    "gi_exact_expanded_stock.gi_M5_self_compose_identity",
    "gi_exact_expanded_stock.gi_M5_rebuilt_involution_is_group_member",
    "gi_exact_expanded_stock.gi_M5_rebuilt_TU_implies_uniform",
    "gi_exact_M5_rebuilt_TU_false_at_root", "gi_M5_TU_vocabulary",
    "gi_exact_M5_native_TU_false_at_root", "gi_exact_M5_native_TU_not_global",
    "gi_M5_TU_not_derivable_from_QLN_background"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "m5-tu: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("m5-tu: residual obligations in " ^ name)
  val report = "M5-TU-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: actual TU formula false at root under rebuilt exact constants; translated native TU not globally valid and not derivable from the explicit no-PP QLN background. No added Persistence, PP countermodel, all-world falsity, or Inv/WI result. HOL-ZF.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-tu-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-tu-statements.txt")) [XML.Text statements]
in end
\<close>

end
