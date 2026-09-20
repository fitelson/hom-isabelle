theory Goodman_Exact_QLN_Model_Audit
  imports Goodman_Exact_QLN_Model
begin

ML \<open>
local
  val names = ["gi_exact_generic_QLN_background_gvalid",
    "gi_exact_generic_QLN_background_consistent", "gi_exact_generic_target_PP_value",
    "gi_exact_generic_native_PP_holds_iff", "gi_exact_generic_native_PP_global_iff",
    "gi_exact_generic_native_QLN_PP_global_iff",
    "gi_exact_generic_native_QLN_PP_consistent_if_classifier"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-qln-model: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-qln-model: residual obligations in " ^ name)
  val report = "EXACT-QLN-MODEL-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: Native complete logical-purity/QLN background instantiated on Bacon exact carriers with generic seed; background consistency relative to HOL-ZF. PP validity remains equivalent to explicit classifier membership, not proved. No identification with a particular Theorem10.1 glued fundamental proposition.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-qln-model-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-qln-model-statements.txt")) [XML.Text statements]
in end
\<close>

end
