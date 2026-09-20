theory Goodman_Exact_M4_Repair_Audit
  imports Goodman_Exact_M4_Repair
begin

ML \<open>
local
  val names = ["gi_exact_M4_variation_square_nonzero", "gi_exact_M4_variation_square_in_stock",
    "gi_exact_M4_nonconstant_proper_view", "gi_exact_M4_fresh_letter",
    "gi_exact_M4_disjoint_lift_empty_view", "gi_exact_M4_lift_fun_prime",
    "gi_exact_M4_no_recovery_from_lift", "gi_exact_M4_no_recovery_excludes_reversible_image",
    "gi_exact_M4_lift_witness", "gi_exact_M4_fun_prime_outside_reversible_orbit",
    "gi_exact_M4_actual_generic_seed_witness", "gi_native_M4_fun_prime_outside_reversible_orbit"]
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 12 then () else error "exact-M4-repair: unexpected count"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-M4-repair: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-M4-repair: residual obligations in " ^ name)
  val report = "EXACT-M4-REPAIR-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: For every fun-prime proposition in the complete exact closed-logical stock, a fresh one-letter branch lift is fun-prime but admits no pure recovery of the original proposition, hence is outside its pure reversible orbit. The actual generic seed and complete native stock are included. No fixed-r all-view QSS premise, fixed predetermined branch, multiple-fundamental selection proposal, arbitrary enlarged stock, or PP consistency claim. HOL-ZF foundations retained.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m4-repair-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m4-repair-statements.txt")) [XML.Text statements]
in end
\<close>

end
