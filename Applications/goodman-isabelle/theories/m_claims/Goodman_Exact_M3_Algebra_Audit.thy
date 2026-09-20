theory Goodman_Exact_M3_Algebra_Audit
  imports Goodman_Exact_M3_Algebra
begin

ML \<open>
local
  val names = ["gi_M3_zero_term_type", "gi_M3_zero_term_logical",
    "gi_M3_difference_term_type", "gi_M3_difference_term_logical", "gi_M3_zero_raw",
    "gi_M3_difference_raw", "gi_exact_M3_zero_in_stock", "gi_exact_M3_difference_closed",
    "gi_M3_difference_zero_iff", "gi_exact_M3_fun_prime_iff_free",
    "gi_native_M3_fun_prime_iff_free", "gi_native_M3_free_generator_exists"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-m3-algebra: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-m3-algebra: residual obligations in " ^ name)
  val report = "EXACT-M3-ALGEBRA-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: Exact complete logical stock contains zero and is Boolean-difference closed by actual closed logical witnesses; fun-prime iff absence of nonzero unary law and free-generator existence. No PP, particular glued-r identification, extreme-view or topological conclusion. HOL-ZF foundations retained.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m3-algebra-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m3-algebra-statements.txt")) [XML.Text statements]
in end
\<close>

end
