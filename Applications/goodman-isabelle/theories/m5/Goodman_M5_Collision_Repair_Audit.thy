theory Goodman_M5_Collision_Repair_Audit
  imports Goodman_M5_Collision_Repair
begin

ML \<open>
local
  val names = ["gi_M5_punctured_truth_nonextreme", "gi_M5_punctured_truth_view", "gi_M5_punctured_truth_NC",
    "gi_M5_raw_corrected_collision", "gi_M5_collision_operator_logical", "gi_M5_collision_operator_denotation",
    "gi_M5_collision_operator_member", "gi_M5_collision_application_extract", "gi_M5_collision_operator_raw",
    "gi_M5_equal_propositions_from_extract", "gi_M5_exact_corrected_collision", "gi_M5_exact_operator_not_injective",
    "gi_M5_corrected_collision_sentence_typed", "gi_M5_corrected_collision_sentence_root",
    "gi_M5_raw_collision_no_left_inverse", "gi_M5_actual_nonreversibility_at_root",
    "gi_M5_native_corrected_collision_at_root", "gi_M5_native_actual_nonreversibility_at_root"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "m5-collision-repair: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("m5-collision-repair: residual obligations in " ^ name)
  val report = "M5-COLLISION-REPAIR-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: actual historical operator has exact semantic collision on punctured truth and truth, with explicit unequal typed inputs; existential collision and nonreversibility true at root, including native translations. No new CEV+ theorem, local fun-prime NC(r) collision, or PP model. HOL-ZF.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-collision-repair-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-collision-repair-statements.txt")) [XML.Text statements]
in end
\<close>

end
