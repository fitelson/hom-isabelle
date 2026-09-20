theory Goodman_T9_Native_Conclusion_Audit
  imports Goodman_T9_Native_Conclusion
begin

ML \<open>
local
  val names = ["gi_T9_exists_fun_prime_vocabulary", "gi_T9_native_exists_fun_prime_language",
    "pp_e_constants.gi_T9_exists_fun_prime_formula_root_iff",
    "pp_e_constants.gi_T9_native_exists_fun_prime_root_witness",
    "gi_T9_native_purity.gi_T9_native_formula_counting_chain",
    "gi_T9_native_purity.gi_T9_native_formula_counting_bound",
    "gi_T9_native_purity.gi_T9_native_formula_cardinal_dichotomy",
    "gi_T9_native_purity.gi_T9_native_formula_infinite_kinds_bound"]
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length names = 8 andalso length facts = 9 then () else error "T9-native-conclusion: unexpected count"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "T9-native-conclusion: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("T9-native-conclusion: residual obligations in " ^ name)
  val report = "T9-NATIVE-CONCLUSION-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: T9 bounds and finite-kinds/exponential-group dichotomy for actual root-pure exact unary values, actual kinds and pure inverse group. Explicit native translated pp_L2 and pp_exists_fun_prime root inputs supply semantic L2 and the typed J witness. Native purity locale, rich variable stock, typed C/native environment, name guards, and FULL external unary PC remain. Infinitude is an additional hypothesis only in the final corollary. HOL-ZF foundations retained; not all arbitrary Henkin interfaces, a derivation of PC, or model existence.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-native-conclusion-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-native-conclusion-statements.txt")) [XML.Text statements]
in end
\<close>

end
