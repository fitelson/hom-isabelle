theory Goodman_Exact_Generic_Fun_Prime_Audit
  imports Goodman_Exact_Generic_Fun_Prime
begin

ML \<open>
local
  val names = [
    "gi_generic_complement_term_type", "gi_generic_complement_term_logical",
    "gi_generic_complement_raw", "gi_exact_generic_complement_closed",
    "gi_exact_operator_index_in_generic_stock", "gi_exact_generic_seed_index_recombination",
    "gi_exact_generic_seed_vanishing_operator_zero", "gi_exact_generic_raw_seed_free",
    "gi_exact_generic_raw_seed_fun_prime", "gi_exact_generic_raw_seed_separates",
    "gi_exact_generic_root_seed_extract", "gi_exact_generic_root_seed_fun_prime",
    "gi_exact_generic_seed_native_fun_prime", "gi_exact_generic_seed_at_root",
    "gi_exact_generic_fundamental_root_fun_prime", "gi_exact_generic_Fun_implies_fun_prime_root"]
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 16 then () else error "exact-generic-fun-prime: unexpected count"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-generic-fun-prime: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-generic-fun-prime: residual obligations in " ^ name)
  val report = "EXACT-GENERIC-FUN-PRIME-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Complement closure of the complete exact logical stock, freeness and fun-prime of the ACTUAL chosen pp_e_generic_raw_seed, exact root-seed extraction, and actual generic Fun-to-fun-prime at the root. Not merely existence of some separator. HOL-ZF foundations retained; no identification with an arbitrary Theorem-10.1 glued assignment, no every-view claim, no PP.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-generic-fun-prime-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-generic-fun-prime-statements.txt")) [XML.Text statements]
in end
\<close>

end
