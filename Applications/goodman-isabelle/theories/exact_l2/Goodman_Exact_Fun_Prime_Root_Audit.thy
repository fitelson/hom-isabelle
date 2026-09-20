theory Goodman_Exact_Fun_Prime_Root_Audit
  imports Goodman_Exact_Fun_Prime_Root
begin

section \<open>Kernel audit of actual root fun′ evaluation\<close>

ML \<open>
local
  val names = ["gi_exact_eval_shift_two",
    "gi_exact_fun_prime_root_schema",
    "gi_exact_fun_prime_root_schema_values",
    "gi_exact_fun_prime_values_iff_raw",
    "gi_exact_fun_prime_root_iff",
    "gi_exact_generic_fun_prime_variable_root"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-fun-prime-root: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-fun-prime-root: residual obligations in " ^ name)
  val report = "EXACT-FUN-PRIME-ROOT-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Actual pp_fun_prime evaluation at the root equals the fixed-stock raw semantic property for each typed proposition term/environment in the exact generic interpretation. Complete closed-logical stock and faithful raw representation; not arbitrary enlarged stocks or identity/equality collapse at all worlds. HOL-ZF qualification retained.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-fun-prime-root-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-fun-prime-root-statements.txt")) [XML.Text statements]
in end
\<close>

end
