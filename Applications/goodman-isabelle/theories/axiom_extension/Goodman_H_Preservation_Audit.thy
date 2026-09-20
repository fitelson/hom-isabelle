theory Goodman_H_Preservation_Audit
  imports Goodman_H_Preservation_Regression Goodman_Context_H_Audit
begin

section \<open>Audit of the remaining H rules and whole-proof preservation\<close>

ML \<open>
local
  val names =
    ["gi_H_validity_certificate", "gi_H_alpha_transport", "gi_H_imp_trans", "gi_constants_universal",
     "gi_book_H_Ref", "gi_book_H_LL", "gi_book_H_Exists_Ref",
     "gi_H_Ref", "gi_H_LL", "gi_H_IndividualExistence",
     "book_full_minimal_model.gi_prop_eval_interpretation", "gi_H_PC",
     "gi_book_H_EG", "gi_book_H_Inst", "gi_alpha_imp_left", "gi_alpha_imp_right",
     "gi_H_EG", "gi_H_Gen", "gi_H_Inst",
     "gi_H_universal_preservation", "gi_H_preservation", "gi_H_closed_preservation",
     "gi_H_foreign_constant_regression"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "H-preservation audit: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises="
      ^ string_of_int (Thm.nprems_of thm)
    else error ("H-preservation audit: residual kernel obligations in " ^ name)
  val report = "GOODMAN-H-PRESERVATION-AUDIT: "
    ^ string_of_int (length facts) ^ " clean endpoints; whole-proof forward H preservation\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "h-preservation-audit.txt")) [XML.Text report]
  val _ = writeln report
in end
\<close>

text \<open>
  All eleven H_proves constructors are covered by the proof induction.
  This is forward preservation into full-F/minimal book H, with rich
  typed variable stock, distinct chart and conclusion-signature guards.
  Reflection and all CEV+/T6 transfers remain outside this audit's claim.
\<close>

end
