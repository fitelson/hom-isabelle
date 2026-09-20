theory Goodman_Exact_Denotation_Audit
  imports Goodman_Exact_Interpretation_Structure
begin

section \<open>Kernel audit and exact statement export\<close>

ML \<open>
local
  val names = ["gi_exact_named_denote_var",
    "gi_exact_named_denote_const",
    "gi_exact_named_denote_app",
    "gi_exact_assignment_prefix",
    "pp_e_constants.gi_exact_named_denote_type",
    "gi_exact_pterm_eval_locality",
    "gi_exact_named_denote_locality",
    "gi_exact_named_closed_assignment_independent",
    "pp_e_constants.gi_exact_book_interpretation_structure",
    "gi_exact_assignment_join_typed",
    "gi_exact_environment_from_same_assignment_conversion"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-denotation: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-denotation: residual obligations in " ^ name)
  val report = "EXACT-DENOTATION-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: Exact named evaluator equations, typing, locality, interpretation structure; environment reduction remains conditional on conversion. HOL-ZF foundation and pp_e_constants guards retained.\n" ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-denotation-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-denotation-statements.txt")) [XML.Text statements]
in end
\<close>

end

