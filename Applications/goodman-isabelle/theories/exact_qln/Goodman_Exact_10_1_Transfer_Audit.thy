theory Goodman_Exact_10_1_Transfer_Audit
  imports Goodman_Exact_10_1_Transfer
begin

section \<open>Kernel audit of the full closed named-term gluing theorem\<close>

ML \<open>
local
  val names = ["gi_exact_minimal_logical_propositional_fragment",
    "gi_exact_named_propositional_encoding",
    "gi_exact_named_propositional_decode_iff",
    "gi_exact_old_propositional_result_type",
    "gi_exact_closed_named_propositional_result_type",
    "gi_exact_closed_named_decoder_value",
    "gi_exact_Bacon_10_1_named_action",
    "gi_exact_Bacon_10_1_named_truth_branch",
    "gi_exact_Bacon_10_1_named"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-10-1-transfer: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-10-1-transfer: residual obligations in " ^ name)
  val report = "EXACT-10-1-TRANSFER-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Exact Bacon10.1 branch gluing for every closed native string term in the directly defined t-generated fragment, with decoder correspondence and result-type check. Countable interpretation family is typed at t-generated types; glued constants are typed at all types. Arbitrary assignments are harmless only because terms are closed. HOL-ZF foundation retained; not generic-seed identification, PP, or syntactic completeness.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-10-1-transfer-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-10-1-transfer-statements.txt")) [XML.Text statements]
in end
\<close>

end
