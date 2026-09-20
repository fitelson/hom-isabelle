theory Goodman_Exact_M3_Extreme_Audit
  imports Goodman_Exact_M3_Extreme_Views
begin

ML \<open>
local
  val names = ["gi_M3_box_term_type", "gi_M3_box_term_logical",
    "gi_M3_future_truth_iff_view", "gi_M3_box_raw", "gi_exact_M3_box_in_stock",
    "gi_exact_M3_box_nonzero", "gi_exact_M3_fun_prime_has_extreme_views",
    "gi_native_M3_fun_prime_has_extreme_views"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-m3-extreme: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-m3-extreme: residual obligations in " ^ name)
  val report = "EXACT-M3-EXTREME-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: Necessity/necessity-of-negation actually denoted in complete exact logical stock; every fun-prime input has true and false views. No PP, arbitrary stock, or all-views-free assertion.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m3-extreme-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m3-extreme-statements.txt")) [XML.Text statements]
in end
\<close>

end
