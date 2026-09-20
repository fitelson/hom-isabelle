theory Goodman_Exact_M5_Rebuilt_Model_Audit
  imports Goodman_Exact_M5_Rebuilt_Model
begin

section \<open>The actual exact M5 model: full statements and kernel evidence\<close>

ML \<open>
local
  val local_names = ["gi_M5_basis_native_QLN_background_gvalid", "gi_M5_rebuilt_native_QLN_background_gvalid",
    "gi_M5_rebuilt_native_QLN_background_consistent", "gi_M5_rebuilt_Pure_value", "gi_M5_rebuilt_pure_clause",
    "gi_M5_rebuilt_closed_term_in_basis", "gi_M5_rebuilt_closed_term_pure", "gi_M5_rebuilt_K_pure",
    "gi_M5_rebuilt_K_pure_holds", "gi_M5_rebuilt_k_named_denotation", "gi_M5_rebuilt_named_closed_term_in_basis",
    "gi_M5_rebuilt_named_closed_term_pure", "gi_M5_identity_in_expanded_raw_stock",
    "gi_M5_K_in_expanded_raw_stock", "gi_M5_rebuilt_seed_changes"]
  val names = ["gi_M5_native_QLN_background_language"] @
    map (fn name => "gi_exact_expanded_stock." ^ name) local_names @
    ["gi_exact_M5_exotic_expanded_stock", "gi_exact_M5_rebuilt_QLN_model", "gi_exact_M5_rebuilt_exotic_pure",
    "gi_exact_M5_rebuilt_exotic_denotation", "gi_exact_M5_rebuilt_complete_purity",
    "gi_exact_M5_rebuilt_seed_not_old", "gi_exact_M5_rebuilt_certificate"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "m5-rebuilt-model: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("m5-rebuilt-model: residual obligations in " ^ name)
  val report = "M5-REBUILT-MODEL-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: actual rebuilt constants preserve exotic k and native Pure/Fun; all closed expanded terms pure; full no-PP zeroary/unary QLN background globally valid; exact exotic value pure and involutive but not truth-uniform; new seed differs from old R. No PP or inferred pp_TU/Inv/WI nonderivability. HOL-ZF.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-rebuilt-model-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-rebuilt-model-statements.txt")) [XML.Text statements]
in end
\<close>

end
