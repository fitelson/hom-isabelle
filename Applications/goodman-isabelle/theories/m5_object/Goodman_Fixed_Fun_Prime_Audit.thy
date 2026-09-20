theory Goodman_Fixed_Fun_Prime_Audit
  imports Goodman_Fixed_Fun_Prime_Axiom
begin
ML \<open>
local
  val names = ["gi_fixed_fun_prime_truth_pure", "gi_fixed_fun_prime_theorem_collapses_minimal_stock",
    "gi_fixed_fun_prime_axiom_collapses_minimal_stock", "gi_fixed_fun_prime_axiom_native_refutation"]
  val entries = map (fn n => (n, Proof_Context.get_thm @{context} n)) names
  val _ = if null (Thm_Deps.all_oracles (map #2 entries)) then () else error "fixed fun-prime oracle"
  fun check (n,t) = if null (Thm.hyps_of t) andalso null (Thm.tpairs_of t)
    then n ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of t)
    else error ("fixed fun-prime residual obligations: " ^ n)
  val report = "FIXED-FUN-PRIME-AUDIT: " ^ string_of_int (length entries) ^ " clean endpoints\n"
    ^ "SCOPE: a fixed fun-prime theorem/axiom collapses T2 minimal stock; no PP used. Native closed image stock refuted under admission guards. Not a refutation of local or existential fun-prime.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "fixed-fun-prime-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (n,t) => n ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of t)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "fixed-fun-prime-statements.txt")) [XML.Text statements]
in end
\<close>
end
