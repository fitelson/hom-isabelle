theory Goodman_Exact_M7_Transfer_Audit
  imports Goodman_Exact_M7_Transfer
begin

ML \<open>
local
  val names = ["gi_exact_M7_operator_enum_range", "gi_exact_M7_operator_enum_member",
    "gi_exact_M7_diagonal_view", "gi_exact_M7_diagonal_differs",
    "gi_exact_M7_diagonal_outside_logical_range", "gi_exact_M7_diagonal_value_member",
    "gi_exact_M7_diagonal_value_unreachable", "gi_native_M7_logical_unary_completeness_fails",
    "gi_exact_M7_pure_proposition_constant_realization", "gi_exact_M7_diagonal_not_pure_proposition",
    "gi_native_M7_zeroary_unary_completeness_fails", "gi_exact_M7_invariant_raw_equivariant",
    "gi_exact_M7_invariant_reachable_iff_classifier", "gi_exact_M7_orbit_image_classifier",
    "gi_exact_M7_all_invariant_reachable_iff_orbit_injective", "gi_exact_M7_fun_prime_orbit_collision",
    "gi_exact_M7_fun_prime_orbit_not_injective", "gi_exact_M7_collision_blocks_singleton",
    "gi_exact_M7_fun_prime_singleton_unreachable", "gi_exact_M7_fun_prime_exact_invariant_unreachable",
    "gi_exact_M7_generic_orbit_not_injective", "gi_exact_M7_generic_invariant_unreachable",
    "gi_exact_M7_generic_fundamental_invariant_incomplete"]
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 23 then () else error "exact-M7: unexpected count"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-M7: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-M7: residual obligations in " ^ name)
  val report = "EXACT-M7-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Explicit natural-branch complement diagonal against every exact closed-logical unary output at a typed R, including native saturated-stock and zeroary cases. Exact invariant reachability iff orbit-map injectivity. Any exact-stock fun-prime raw r has distinct words with equal views, so an explicit singleton target is unreachable even by all exact invariant unary values; this applies to the actual generic root seed. No blanket noninjectivity for arbitrary r, no secondary Boolean model, no arbitrary Theorem-10.1 assignment identification, no enlarged-Pure or PP consistency claim. HOL-ZF foundations retained.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m7-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m7-statements.txt")) [XML.Text statements]
in end
\<close>

end
