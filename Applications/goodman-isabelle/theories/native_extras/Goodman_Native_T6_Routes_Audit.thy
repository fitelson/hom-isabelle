theory Goodman_Native_T6_Routes_Audit
  imports Goodman_Native_T6_Routes
begin

section \<open>Kernel audit of the fully native T6 routes\<close>

ML \<open>
local
  val names = ["gi_native_T6_Inv_refutation",
    "gi_native_T6_TU_refutation",
    "gi_native_T6_WI_refutation",
    "gi_native_T6_RS_refutation",
    "gi_native_central_T6_Inv_refutation",
    "gi_native_central_T6_TU_refutation",
    "gi_native_central_T6_WI_refutation",
    "gi_native_central_T6_RS_refutation",
    "gi_native_T6_Inv_inconsistent",
    "gi_native_T6_TU_inconsistent",
    "gi_native_T6_WI_inconsistent",
    "gi_native_T6_RS_inconsistent",
    "gi_native_central_T6_Inv_inconsistent",
    "gi_native_central_T6_TU_inconsistent",
    "gi_native_central_T6_WI_inconsistent",
    "gi_native_central_T6_RS_inconsistent",
    "gi_native_WI_derives_TU",
    "gi_native_T1_WI_derives_Inv",
    "gi_native_T1_TU_derives_Inv"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "native-T6-routes: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("native-T6-routes: residual obligations in " ^ name)
  val report = "NATIVE-T6-ROUTES-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Eight refutations/eight inconsistency corollaries in gb_signature with fully native closed extras and no final translation parameter. Weak-L2 common-core routes retain exists-fun-prime; repaired central stock derives it; RS routes retain strongL2+RS only. Three native classification consequences retain their exact stocks (WI alone for TU, T1 including zeroary Exhaustion for Inv). No PP-alone refutation or deduction-theorem conversion asserted.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "native-t6-routes-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "native-t6-routes-statements.txt")) [XML.Text statements]
in end
\<close>

end

