theory Goodman_Native_TU_RS_Witness_Audit
  imports Goodman_Native_TU_RS_Witness
begin

section \<open>Kernel audit of the native TU ⇒ RS transfer\<close>

ML \<open>
local
  val names = ["gb_TU_RS_axioms_T1_form",
    "gb_TU_RS_axioms_language",
    "gb_TU_RS_axioms_closed",
    "gi_TU_RS_axioms_closed",
    "gi_TU_RS_literal_stock_inclusion",
    "gi_TU_RS_axiom_from_native",
    "gi_TU_RS_native_preservation",
    "gi_native_TU_RS_derives_RS",
    "gi_RS_plus_native_translation",
    "gi_RS_plus_shift_by",
    "gi_RS_plus_purity_admitted",
    "gi_RS_plus_specification_admitted",
    "gi_native_TU_RS_witness_pure",
    "gi_native_TU_RS_witness_translated",
    "gi_RS_plus_chart_alpha",
    "gi_RS_plus_specification_alpha",
    "gi_native_TU_RS_witness_specification"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "native-tu-rs-witness: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("native-tu-rs-witness: residual obligations in " ^ name)
  val report = "NATIVE-TU-RS-WITNESS-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Native stock gb_TU_RS_axioms = T6 PP core + zeroary Exhaustion + exists fun-prime + TU, in gb_signature. Endpoints: gb_RS, purity of the named witness gb_RS_plus, and its uniform rigid specification (via alpha transport of the translated witness). Exhaustion and exists fun-prime are retained; no weaker-scope TU implies RS claim, no deduction-theorem conversion, no consistency claim.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "native-tu-rs-witness-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "native-tu-rs-witness-statements.txt")) [XML.Text statements]
in end
\<close>

end
