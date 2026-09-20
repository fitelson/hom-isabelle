theory Goodman_Exact_M1_Bottom_Audit
  imports Goodman_Exact_M1_Bottom
begin

section \<open>Kernel audit of exact M1 at the proposition type\<close>

ML \<open>
local
  val names = ["gi_M1_exact_closed_truth",
    "gi_M1_exact_closed_falsity",
    "gi_M1_exact_proposition_stock_noncontingency",
    "gi_M1_NC_body_language",
    "gi_M1_NC_language",
    "gi_M1_NC_closed",
    "gi_M1_NC_closed_logical",
    "gi_M1_NC_string_rename",
    "pp_e_constants.gi_M1_NC_body_holds",
    "pp_e_constants.gi_M1_NC_denotes_exact_classifier",
    "gi_M1_NC_native_closed_denotation",
    "gi_M1_exact_bottom_classifier_in_native_stock",
    "gi_M1_exact_native_purity_is_noncontingency",
    "gi_M1_exact_bottom_PP_gvalid"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-M1-bottom: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-M1-bottom: residual obligations in " ^ name)
  val report = "EXACT-M1-BOTTOM-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Proposition-type purity is noncontingency; the explicit closed logical NC term denotes its actual exact-carrier classifier, which belongs to the complete unary logical stock. The generic interpretation globally validates gb_purity_of_pure Prop, NOT the higher gb_target_PP. Exact carriers, rich names where needed, typed constants/assignments, and HOL-ZF retained. No invariant-implies-definable principle.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m1-bottom-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m1-bottom-statements.txt")) [XML.Text statements]
in end
\<close>

end
