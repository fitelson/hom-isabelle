theory Goodman_Exact_Rebuilt_Constants_Audit
  imports Goodman_Exact_Rebuilt_Constants
begin

section \<open>Kernel audit of the actual rebuilt constant interpretation\<close>

ML \<open>
local
  val names = ["gi_M5_eval_constant_agreement",
    "gi_M5_named_constant_agreement",
    "gi_exact_expanded_stock.gi_M5_expanded_invariant_basis",
    "gi_exact_expanded_stock.gi_M5_rebuilt_constants_typed",
    "gi_exact_expanded_stock.gi_M5_rebuilt_constants_locale",
    "gi_exact_expanded_stock.gi_M5_rebuilt_constant_at",
    "gi_exact_expanded_stock.gi_M5_rebuilt_Pure_coordinate",
    "gi_exact_expanded_stock.gi_M5_rebuilt_Fun_coordinate",
    "gi_exact_expanded_stock.gi_M5_rebuilt_goodman_coordinate",
    "gi_exact_expanded_stock.gi_M5_rebuilt_basis_coordinate",
    "gi_exact_expanded_stock.gi_M5_rebuilt_expanded_eval",
    "gi_exact_expanded_stock.gi_M5_rebuilt_expanded_closed_denotation",
    "gi_exact_expanded_stock.gi_M5_rebuilt_named_expanded_denotation",
    "gi_exact_expanded_stock.gi_M5_rebuilt_named_basis_equal",
    "gi_exact_expanded_stock.gi_M5_rebuilt_exotic_constant_denotation",
    "gi_exact_expanded_stock.gi_M5_rebuilt_native_denotation",
    "gi_exact_expanded_stock.gi_M5_rebuilt_native_global_valid_iff"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-rebuilt-constants: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-rebuilt-constants: residual obligations in " ^ name)
  val report = "EXACT-REBUILT-CONSTANTS-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Actual rebuilt C interprets fresh k ONLY at t-to-t by K and preserves basis Pure/Fun coordinates. All five invariant-basis fields discharged from the complete expanded stock. Whole typed k-language preserves auxiliary generating denotations, including full closed native-language stock equality. Native Goodman denotations/global validity agree with basis model under its explicit signature guard. No background validity or PP inferred without the separate model theorems; exact HOL-ZF carriers retained.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-rebuilt-constants-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-rebuilt-constants-statements.txt")) [XML.Text statements]
in end
\<close>

end

