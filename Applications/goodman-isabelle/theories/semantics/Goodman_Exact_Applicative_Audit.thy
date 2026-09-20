theory Goodman_Exact_Applicative_Audit
  imports Goodman_Exact_Applicative_Adapter
begin

section \<open>Audit of the displayed integration endpoints\<close>

ML \<open>
local
  val names = ["gi_exact_domain_member",
    "gi_exact_app_value",
    "gi_exact_app_closed",
    "gi_exact_book_applicative_structure",
    "gi_exact_default_member",
    "gi_exact_domain_nonempty",
    "gi_exact_book_assignment_iff",
    "gi_exact_default_assignment_typed",
    "gi_exact_total_assignment_exists",
    "gi_exact_assignment_lookup",
    "gi_exact_assignment_update"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-applicative: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-applicative: residual obligations in " ^ name)
  val report = "EXACT-APPLICATIVE-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: Exact HOL-ZF carriers, application closure, inhabited domains and total typed assignments only; NOT yet named denotation or global soundness. Relative to the imported HOL-ZF assumptions.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-applicative-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-applicative-statements.txt")) [XML.Text statements]
in end
\<close>

end

