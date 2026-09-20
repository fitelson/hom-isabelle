theory Goodman_Native_Stock_Audit
  imports Goodman_Native_Stock_Bridge
begin

section \<open>Kernel audit of the native-stock bridge\<close>

ML \<open>
local
  val names =
    ["gi_goodman_names_satisfiable", "gi_logical_constants_iff",
     "gi_Pure_translation", "gi_Fun_translation", "gi_pure_translation", "gi_fun_translation",
     "gi_PP_translation", "gi_application_translation", "gi_unique_fundamental_translation",
     "gi_no_fundamentals_translation", "gi_purity_schema_inclusion",
     "gi_application_schema_equality", "gi_no_other_fundamentals_schema_equality",
     "gi_background_inclusion", "gi_background_closed", "gi_background_proof_preservation",
     "gi_T6_core_inclusion", "gb_T6_core_language", "gb_T6_core_closed",
     "gi_T6_native_core_transfer", "gi_T6_native_core_Inv_refutation",
     "gi_T6_native_core_TU_refutation", "gi_T6_native_core_WI_refutation",
     "gi_T6_native_core_RS_refutation", "gi_T6_native_core_Inv_inconsistent",
     "gi_T6_native_core_TU_inconsistent", "gi_T6_native_core_WI_inconsistent",
     "gi_T6_native_core_RS_inconsistent"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Native-stock audit: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises="
      ^ string_of_int (Thm.nprems_of thm)
    else error ("Native-stock audit: residual kernel obligations in " ^ name)
  val report = "GOODMAN-NATIVE-STOCK-AUDIT: "
    ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: native nonmodal background; native T6 common core; translated route extras; universal target signature.\n"
    ^ "Logical purity: forward syntactic inclusion, NOT denotational equality or a model theorem.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "native-stock-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn name =>
    name ^ ":\n" ^ XML.content_of (YXML.parse_body (Syntax.string_of_term @{context}
      (Thm.prop_of (Proof_Context.get_thm @{context} name))))) names)
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "native-stock-statements.txt")) [XML.Text statements]
in end
\<close>

end
