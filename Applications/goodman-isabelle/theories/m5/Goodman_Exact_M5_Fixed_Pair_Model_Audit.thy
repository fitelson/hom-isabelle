theory Goodman_Exact_M5_Fixed_Pair_Model_Audit
  imports Goodman_Exact_M5_Fixed_Pair_Model
begin

ML \<open>
local
  val names = ["gi_exact_M5_fixed_raw", "gi_exact_M5_fixed_expanded_stock", "gi_exact_M5_fixed_QLN_model",
    "gi_exact_M5_fixed_QSS_model", "gi_exact_M5_fixed_operator_pure", "gi_exact_M5_fixed_operator_denotation",
    "gi_exact_M5_fixed_operator_involution", "gi_exact_M5_fixed_operator_classification_failure"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "m5-fixed: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("m5-fixed: residual obligations in " ^ name)
  val report = "M5-FIXED-PAIR-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: literal fixed[5] pair in actual rebuilt exact QLN/QSS model, pure exact self-inverse operator with nonuniform/nonbiconditional raw action. No arbitrary old-orbit avoidance, PP, or root classification-formula assertion.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-fixed-pair-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-fixed-pair-statements.txt")) [XML.Text statements]
in end
\<close>

end
