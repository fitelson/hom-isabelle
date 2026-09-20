theory Goodman_M5_Local_Collision_Counterexample_Audit
  imports Goodman_M5_Local_Collision_Counterexample
begin

ML \<open>
local
  val names = ["gi_M5_view_complement", "gi_M5_raw_NC_view", "gi_M5_alternating_views_nonextreme",
    "gi_M5_alternating_NC_empty", "gi_M5_counter_input_views", "gi_M5_counter_input_fun_prime",
    "gi_M5_counter_NC_view_empty", "gi_M5_counter_collision_false_on_branch", "gi_M5_raw_collision_truth",
    "gi_M5_raw_collision_counterexample", "gi_M5_future_extract_iff", "gi_M5_eval_box_raw",
    "gi_M5_eval_neg_raw", "gi_M5_eval_disj_raw", "gi_M5_eval_iff_raw", "gi_M5_eval_NC_raw",
    "gi_M5_eval_truth_raw", "gi_M5_eval_collision_raw", "gi_M5_collision_result_typed",
    "gi_M5_actual_collision_result_false_at_root", "gi_M5_actual_local_collision_counterexample",
    "gi_M5_local_collision_universal_typed", "gi_M5_local_collision_universal_false_at_root",
    "gi_M5_local_collision_vocabulary", "gi_M5_native_local_collision_false_at_root",
    "gi_M5_local_collision_not_derivable_from_no_PP_QLN", "gi_M5_local_collision_not_derivable_from_T2_min"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "m5-local-collision: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("m5-local-collision: residual obligations in " ^ name)
  val report = "M5-LOCAL-COLLISION-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: actual historical collision formula fails as a LOCAL implication, in the original exact no-PP QLN model; explicit alternating-branch fun-prime counterexample, native universal implication not derivable from no-PP QLN or T2-min. Does not refute global-fun-prime-axiom theorem, assert operator injectivity, identify input as fundamental, or supply PP model. HOL-ZF.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-local-collision-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-local-collision-statements.txt")) [XML.Text statements]
in end
\<close>

end
