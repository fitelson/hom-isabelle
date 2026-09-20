theory Goodman_Exact_M3_No_All_View_Generator_Audit
  imports Goodman_Exact_M3_No_All_View_Generator
begin

ML \<open>
local
  val names = ["gi_exact_M3_empty_not_fun_prime", "gi_exact_M3_no_all_view_generator",
    "gi_exact_M3_some_view_not_fun_prime", "gi_exact_M3_fixed_necessitated_QSS_impossible",
    "gi_native_M3_no_all_view_generator", "gi_exact_generic_root_and_views_differ"]
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 6 then () else error "exact-no-all-view-generator: unexpected count"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-no-all-view-generator: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-no-all-view-generator: residual obligations in " ^ name)
  val report = "EXACT-NO-ALL-VIEW-GENERATOR-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: No fixed raw proposition has fun-prime at every view for the complete exact logical stock. The literal historical pp_stock_necessitated_QSS premise therefore has no exact-stock instance. This is distinct from object-language boxed QSS with its Fun antecedent, and does not refute intended M4/M6 conclusions or generic moving-seed QLN. HOL-ZF foundations retained.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-no-all-view-generator-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-no-all-view-generator-statements.txt")) [XML.Text statements]
in end
\<close>

end
