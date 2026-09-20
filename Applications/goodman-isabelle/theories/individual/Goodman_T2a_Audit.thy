theory Goodman_T2a_Audit
  imports Goodman_T2a_Transfer
begin

section \<open>T2a: kernel audit and exact statements\<close>

ML \<open>
local
  val names = ["gi_T2a_reversible_admitted",
    "gi_T2a_group_member_admitted", "gi_T2a_reversible_translated",
    "gi_T2a_group_member_translated", "gi_T2a_negation_translated",
    "gb_T2a_fun_prime_chart_fresh", "gi_T2a_fun_prime_var1_translation",
    "gi_T2a_fun_prime_application_translation", "gi_T2a_reversible_var_translation",
    "gi_T2a_group_member_var_translation", "gi_T2a_reversible_claim_translation",
    "gi_T2a_group_member_claim_translation", "gi_T2a_reversible",
    "gi_T2a_group_member", "gi_T2a_negation_claim_translation", "gi_T2a_negation"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "t2a: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("t2a: residual obligations in " ^ name)
  val report = "T2A-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: T2a preservation of fun-prime by pure reversible operators, group members, and negation; original PP common core and antecedents retained. Native formulas use explicitly protected binder charts.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t2a-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t2a-statements.txt")) [XML.Text statements]
in end
\<close>

end
