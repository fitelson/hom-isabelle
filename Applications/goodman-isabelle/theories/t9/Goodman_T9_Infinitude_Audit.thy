theory Goodman_T9_Infinitude_Audit
  imports Goodman_T9_Infinitude
begin

section \<open>Kernel audit of actual typed kind infinitude\<close>

ML \<open>
local
  val names = ["gi_T9_cardinality_subset_spec",
    "gi_T9_native_purity.gi_T9_left_composition_respects_kind",
    "gi_T9_native_purity.gi_T9_left_action_member",
    "gi_T9_native_purity.gi_T9_left_action_bijective",
    "gi_T9_native_purity.gi_T9_selector_collision_covariance",
    "gi_T9_native_purity.gi_T9_selector_collision_preserves_card",
    "gi_T9_native_purity.gi_T9_native_PC_L2_infinitely_many_kinds",
    "gi_T9_native_purity.gi_T9_native_PC_L2_exponential_group_bound",
    "gi_T9_native_purity.gi_T9_native_formula_infinitely_many_kinds",
    "gi_T9_native_purity.gi_T9_native_formula_exponential_group_bound"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "T9-infinitude: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("T9-infinitude: residual obligations in " ^ name)
  val report = "T9-INFINITUDE-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Actual typed left composition permutes actual kinds; selector collisions preserve selected-set cardinality; finite actual kinds excluded; exponential lower bound on actual pure invertible group. Native purity locale and full external unary PC retained. Final two corollaries derive semantic root L2 and typed fun-prime witness from actual translated native formula inputs, not abstract postulates. Composition application uses explicitly typed r and B applied to r, not an unrestricted meta-domain law. No group-size/classification premise or model existence; HOL-ZF retained.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-infinitude-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-infinitude-statements.txt")) [XML.Text statements]
in end
\<close>

end
