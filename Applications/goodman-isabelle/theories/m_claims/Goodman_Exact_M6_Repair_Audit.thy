theory Goodman_Exact_M6_Repair_Audit
  imports Goodman_Exact_M6_Repair
begin

section \<open>M6: repaired exact-stock statements and kernel audit\<close>

ML \<open>
local
  val names = ["gi_exact_M6_fun_prime_preimage", "gi_exact_M6_fun_prime_not_extreme",
    "gi_M6_fresh_letter", "gi_M6_fresh_branch_view", "gi_M6_fresh_branch_excludes",
    "gi_exact_M6_fun_prime_truth_separates", "gi_exact_M6_fun_prime_separates_distinct_substitutions",
    "gi_native_M6_fun_prime_separates_distinct_substitutions", "gi_M6_orbit_diagonal_differs",
    "gi_M6_single_proposition_independence_fails", "gi_M6_equivariant_empty_extreme",
    "gi_exact_M6_pure_empty_extreme", "gi_M6_reversible_orbit_subset_images", "gi_M6_copy_views",
    "gi_M6_views_preserve_inclusion", "gi_exact_M6_fun_prime_strict_pair", "gi_exact_M6_strict_pair_exists",
    "gi_native_M6_strict_pair_exists", "gi_M6_joint_assignment_blocked_by_inclusion",
    "gi_exact_M6_joint_assignment_counterexample"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-m6-repair: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-m6-repair: residual obligations in " ^ name)
  val report = "EXACT-M6-REPAIR-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: actual exact stock; one-view heredity, separation of substitutions, missing arbitrary single-coordinate target, strict fun-prime pair outside pure-operator images and blocked joint assignment. No fixed-r necessitated-QSS premise, particular glued-r identification, arbitrary enlarged stock, or PP model.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m6-repair-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m6-repair-statements.txt")) [XML.Text statements]
in end
\<close>

end
