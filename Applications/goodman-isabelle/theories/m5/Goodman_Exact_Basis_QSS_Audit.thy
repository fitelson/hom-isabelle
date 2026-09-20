theory Goodman_Exact_Basis_QSS_Audit
  imports Goodman_Exact_Basis_QSS
begin

ML \<open>
local
  val basis_names = ["gi_basis_fundamental_action", "gi_basis_QSS_at_world", "gi_basis_QSS_holds_iff",
    "gi_basis_QSS_holds", "gi_basis_fun_prime_holds_iff", "gi_basis_fundamental_fun_prime_holds",
    "gi_basis_moving_seed_fun_prime_at_world", "gi_basis_exists_fun_prime_holds",
    "gi_basis_native_QSS_gvalid", "gi_basis_native_exists_fun_prime_gvalid"]
  val names = map (fn name => "gi_exact_invariant_basis." ^ name) basis_names @
    ["gi_exact_expanded_stock.gi_M5_rebuilt_native_QSS_gvalid",
    "gi_exact_expanded_stock.gi_M5_rebuilt_native_exists_fun_prime_gvalid",
    "gi_exact_M5_rebuilt_QSS_gvalid", "gi_exact_M5_rebuilt_exists_fun_prime_gvalid"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "basis-qss: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("basis-qss: residual obligations in " ^ name)
  val report = "BASIS-QSS-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: actual worldwise QSS for the invariant-basis interpretation from proved equalizer-seed separation; moving witness fun-prime at its own world; native global QSS/existence under actual rebuilt constants. Not all views of one fixed seed. No PP, Pure(Fun), or assumed QSS.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "basis-qss-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "basis-qss-statements.txt")) [XML.Text statements]
in end
\<close>

end
