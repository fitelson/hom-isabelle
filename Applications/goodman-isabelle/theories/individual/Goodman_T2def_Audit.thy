theory Goodman_T2def_Audit
  imports Goodman_T2def_Transfer
begin

section \<open>Audit of exact statements and kernel proof objects\<close>

ML \<open>
local
  val names = ["gi_T2_PP_native_preservation",
    "gi_T2d_admitted",
    "gi_T2d_possibly_pure_translated",
    "gi_T2d_claim_translation",
    "gi_T2d_possibly_pure",
    "gi_T2_box_translation",
    "gi_T2_noncontingent_translation",
    "gi_T2e_false_but_possible_translation",
    "gi_T2_noncontingent_admitted",
    "gi_T2e_admitted",
    "gi_T2e_false_but_possible_translated",
    "gi_T2e_claim_translation",
    "gi_T2e_false_but_possible",
    "gi_T2f_six_distinct_translation",
    "gi_T2f_admitted",
    "gi_T2f_six_distinct_translated",
    "gi_T2f_claim_translation",
    "gi_T2f_six_distinct"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "t2def: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("t2def: residual obligations in " ^ name)
  val report = "T2DEF-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: T2d/e/f retain exact stocks and fun-prime antecedents; all fifteen object inequalities written. Source truth/modal representations explicit.\n" ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t2def-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t2def-statements.txt")) [XML.Text statements]
in end
\<close>

end

