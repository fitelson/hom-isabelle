theory Goodman_T7_Audit
  imports Goodman_T7_Transfer
begin

section \<open>T7a proof objects and full statement export\<close>

ML \<open>
local
  val names = ["gi_T7_axioms_closed", "gi_T7_full_axioms_closed",
    "gi_T7_native_axioms_language", "gi_T7_native_full_axioms_language",
    "gi_T7_stock_inclusion", "gi_T7_full_stock_inclusion", "gi_T7_liar_admitted",
    "gi_T7_absorbed_admitted", "gi_T7_parameter_admitted", "gi_T7_result_admitted",
    "gi_T7a_parameter_translated", "gi_T7a_closed_translated", "gi_T7_liar_translation",
    "gi_T7_absorbed_var_translation", "gi_T7_parameter_claim_translation",
    "gi_T7_absorption_result_translation", "gi_T7a_parameter", "gi_T7a_closed",
    "gi_T7_native_core_in_repaired", "gi_T7a_repaired_central_stock"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "t7: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("t7: residual obligations in " ^ name)
  val report = "T7-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: T7a retains L2 and the purity/application/PP core; the closed result requires fun-prime existence, separately derived for the repaired central stock. No Inv/TU/WI, consistency result, or invented T7b.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t7-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t7-statements.txt")) [XML.Text statements]
in end
\<close>

end
