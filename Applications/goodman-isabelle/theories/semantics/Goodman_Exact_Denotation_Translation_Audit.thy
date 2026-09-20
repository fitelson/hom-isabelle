theory Goodman_Exact_Denotation_Translation_Audit
  imports Goodman_Exact_Denotation_Translation
begin

section \<open>Kernel audit of all-type exact denotation preservation\<close>

ML \<open>
local
  val names = ["gi_exact_chart_assignment_typed",
    "gi_exact_chart_update_lookup",
    "pp_e_constants.gi_exact_eval_agrees_on_context",
    "pp_e_constants.gi_exact_chart_body_eval",
    "pp_e_constants.gi_exact_translation_language",
    "pp_e_constants.gi_exact_translated_member",
    "pp_e_constants.gi_exact_translation_prop_ext",
    "pp_e_constants.gi_exact_named_not_holds",
    "pp_e_constants.gi_exact_named_and_holds",
    "pp_e_constants.gi_exact_named_or_holds",
    "pp_e_constants.gi_exact_named_exists_holds",
    "pp_e_constants.gi_exact_denotation_translation"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-denotation-translation: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-denotation-translation: residual obligations in " ^ name)
  val report = "EXACT-DENOTATION-TRANSLATION-AUDIT: " ^
    string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Value equality at every represented type for the original constructor-to-named translation; typed constants, rich variable stock, typed distinct chart and total typed assignment retained. Proposition extensionality ranges over every word; lambda equality uses Bacon's exact restricted function graphs. HOL-ZF foundation retained. No PP model or consistency conclusion.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "exact-denotation-translation-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm))))
    (names ~~ facts))
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "exact-denotation-translation-statements.txt")) [XML.Text statements]
in end
\<close>

end
