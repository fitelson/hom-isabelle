theory Goodman_M5_Exotic_Operators_Audit
  imports Goodman_M5_Exotic_Operators
begin

section \<open>M5 transpositions: exact assumptions and kernel proof objects\<close>

ML \<open>
local
  val names = ["gi_M5_exotic_equivariant", "gi_M5_exotic_view",
    "gi_M5_no_echo_pair.pair_distinct", "gi_M5_no_echo_pair.flip_rule",
    "gi_M5_no_echo_pair.swaps_false", "gi_M5_no_echo_pair.swaps_true",
    "gi_M5_no_echo_pair.preserves_pair", "gi_M5_no_echo_pair.preimage_pair_only_at_root",
    "gi_M5_no_echo_pair.no_outsider_enters_pair", "gi_M5_no_echo_pair.pair_iff",
    "gi_M5_no_echo_pair.involution", "gi_M5_no_echo_pair.bijective",
    "gi_M5_no_echo_pair.pair_nonextreme", "gi_M5_no_echo_pair.fixes_extremes",
    "gi_M5_no_echo_pair.not_identity", "gi_M5_no_echo_pair.not_truth_uniform",
    "gi_M5_no_echo_pair.not_biconditional", "gi_M5_no_echo_pair.fixes_avoiding_orbit",
    "gi_M5_fixed_pair", "gi_M5_fixed_exotic_involution", "gi_M5_selector_zero",
    "gi_M5_selector_one", "gi_M5_diagonal_singleton", "gi_M5_diagonal_false",
    "gi_M5_diagonal_nonextreme", "gi_M5_diagonal_avoids_view", "gi_M5_diagonal_pair_avoids_orbit",
    "gi_M5_diagonal_view", "gi_M5_insert_root_view", "gi_M5_diagonal_no_echo_pair",
    "gi_M5_repaired_exotic_involution", "gi_M5_repaired_exotic_equivariant",
    "gi_M5_repaired_exotic_bijective", "gi_M5_repaired_exotic_swaps",
    "gi_M5_repaired_exotic_fixes_R", "gi_M5_repaired_exotic_not_identity",
    "gi_M5_repaired_exotic_not_truth_uniform", "gi_M5_repaired_exotic_not_biconditional",
    "gi_M5_old_seed_QSS_obstruction", "gi_exact_M5_exotic_member",
    "gi_exact_M5_exotic_invariant", "gi_exact_M5_exotic_raw", "gi_exact_M5_application_extract",
    "gi_exact_M5_exotic_involution", "gi_exact_M5_application_root",
    "gi_exact_M5_exotic_not_truth_uniform", "gi_exact_M5_old_seed_collision",
    "gi_exact_M5_exotic_fixes_seed"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "m5-exotic: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("m5-exotic: residual obligations in " ^ name)
  val report = "M5-EXOTIC-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: general no-echo transposition proof with explicit locale hypotheses; fixed[5] and repaired R-dependent orbit-avoiding pairs; actual exact-carrier invariant involution, truth-uniformity failure and old-seed collision. No purity, enlarged-model, or PP claim.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-exotic-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-exotic-statements.txt")) [XML.Text statements]
in end
\<close>

end
