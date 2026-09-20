theory Goodman_TU_Inv_Audit
  imports Goodman_TU_Inv_Exhaustion
begin

section \<open>Kernel audit and exact statement export\<close>

ML \<open>
local
  val names = ["gi_uniform_test_type",
    "gi_uniform_operator_type",
    "gi_uniform_literal_type",
    "gi_uniform_builder_type",
    "gi_uniform_builder_logical",
    "gi_uniform_builder_beta",
    "gi_uniform_builder_equality",
    "gi_uniform_test_pure_from",
    "gi_uniform_operator_shift",
    "gi_uniform_operator_beta",
    "gi_uniform_test_unfold",
    "gi_uniform_box_intens_test",
    "gi_uniform_branch_identity_from",
    "gi_TU_Exhaustion_group_classification",
    "gi_standard_operator_group_from",
    "gi_standard_operator_classification_converse",
    "gi_CEV_TU_Exhaustion_implies_Inv",
    "gi_CEV_TU_Exhaustion_exact_stock",
    "gi_TU_T1_axioms_closed",
    "gi_TU_T1_native_stock_language",
    "gi_TU_T1_axiom_from_native",
    "gi_TU_Exhaustion_implies_Inv_translated"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "tu-inv: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("tu-inv: residual obligations in " ^ name)
  val report = "TU-INV-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: Direct TU plus zeroary Exhaustion implies Inv over native T1; no PP, L2, or fun-prime witness. RS not established.\n" ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "tu-inv-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "tu-inv-statements.txt")) [XML.Text statements]
in end
\<close>

end

