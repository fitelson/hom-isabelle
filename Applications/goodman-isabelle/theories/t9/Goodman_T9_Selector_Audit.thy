theory Goodman_T9_Selector_Audit
  imports Goodman_T9_PC_Selector
begin

ML \<open>
local
  val names = ["gi_T9_J_builder_type", "gi_T9_lower_builder_type",
    "gi_T9_builders_logical", "pp_e_constants.gi_T9_J_value_member",
    "pp_e_constants.gi_T9_lower_value_member", "pp_e_constants.gi_T9_J_value_holds",
    "pp_e_constants.gi_T9_fun_prime_formula_holds", "pp_e_constants.gi_T9_lower_value_holds",
    "gi_T9_native_purity.gi_T9_core_at_root",
    "gi_T9_native_purity.gi_T9_closed_logical_value_pure",
    "gi_T9_native_purity.gi_T9_closed_source_axiom_at_root",
    "gi_T9_native_purity.gi_T9_root_application_closed",
    "gi_T9_native_purity.gi_T9_root_Pure_pure",
    "gi_T9_native_purity.gi_T9_J_value_pure",
    "gi_T9_native_purity.gi_T9_lower_value_pure", "gi_T9_PC_witness_spec",
    "gi_T9_native_purity.gi_T9_PC_lowered_pure",
    "gi_T9_native_purity.gi_T9_PC_lowered_spec"]
  val entries = maps (fn name => map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)) names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "T9 selector oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("T9 selector residual obligations: " ^ name)
  val report = "T9-SELECTOR-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: actual exact carriers and native PP core; full external unary PC retained; typed higher-order selector lowered to a pure unary value. No cardinal bound or model existence claimed.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-selector-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-selector-statements.txt")) [XML.Text statements]
in end
\<close>

end
