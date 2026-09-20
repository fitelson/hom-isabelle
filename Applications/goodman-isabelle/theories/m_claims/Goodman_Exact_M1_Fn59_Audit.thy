theory Goodman_Exact_M1_Fn59_Audit
  imports Goodman_Exact_M1_Fn59
begin

section \<open>Kernel audit of the exact footnote-59 obstruction\<close>

ML \<open>
local
  val names = ["gi_M1_native_pure_clause",
    "pp_e_constants.gi_M1_exact_fn59_liar_clause",
    "pp_e_constants.gi_M1_exact_QSS_clause",
    "pp_e_constants.gi_M1_exact_unique_fundamental_clause",
    "pp_e_constants.gi_M1_exact_fn59_liar_member",
    "pp_e_constants.gi_M1_exact_fn59_contradiction",
    "pp_e_constants.gi_M1_native_fn59_denotation",
    "pp_e_constants.gi_M1_native_QSS_denotation",
    "pp_e_constants.gi_M1_native_unique_denotation",
    "pp_e_constants.gi_M1_exact_native_fn59_contradiction",
    "pp_e_constants.gi_M1_no_exact_typed_interpretation_of_fn59_stock"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-M1-fn59: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-M1-fn59: residual obligations in " ^ name)
  val report = "EXACT-M1-FN59-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Actual footnote59 liar evaluation at arbitrary worlds and arbitrary typed constant interpretations on Bacon's exact carriers. D-purity plus QSS and unique fundamentality yields contradiction. Native D/QSS/unique denotations are transferred with source-vocabulary guards. The final global-stock exclusion RETAINS PP and Purity of Fun at t alongside logical purity/application/QSS/unique; no unconditional classifier impurity or answer without Pure(Fun). HOL-ZF scope retained.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m1-fn59-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m1-fn59-statements.txt")) [XML.Text statements]
in end
\<close>

end
