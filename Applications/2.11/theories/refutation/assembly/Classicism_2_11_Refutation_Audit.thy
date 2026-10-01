theory Classicism_2_11_Refutation_Audit
  imports Classicism_2_11_Refutation
begin

text \<open>Audit of the end-to-end refutation endpoints. It records their
  statements, checks theorem-object dependencies, and requires the main
  refutation theorem to have no premises.\<close>

ML \<open>
local
  val names = [
    "c211_proves_least", "c211_soundness", "c211_underivable",
    "c211_hypotheses_language", "c211_conclusion_language", "c211_conclusion_closed",
    "c211_box_holds", "c211_le_holds", "c211_le_neg_holds", "c211_atom_holds",
    "c211_atomicity_holds", "c211_box_atomicity_valid", "c211_BC_valid", "c211_BF_valid",
    "c211_RC_holds_root", "c211_RC_not_valid",
    "c211_root_realize_ex1", "c211_middle_realize_ex1", "c211_terminal_realize_ex1",
    "c211_rleq_root", "c211_rcur_limit_ulim", "c211_raw_complete", "c211_raw_atomic",
    "c211_transfer_leq", "c211_transfer_atomic", "c211_transfer_complete",
    "c211_raw_rigid_A0_fails", "c211_prigid_transfer", "c211_concrete_pRC_false",
    "c211_box_atomicity_concrete", "c211_BC_concrete", "c211_BF_concrete",
    "c211_hypotheses_valid", "c211_conclusion_not_valid",
    "proposition_2_11_refuted"]
  val premise_free = ["c211_conclusion_not_valid", "proposition_2_11_refuted"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "2.11 refutation: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("2.11 refutation: residual obligations in " ^ name)
  val _ = premise_free |> List.app (fn name =>
    let val th = Proof_Context.get_thm @{context} name
    in if Thm.nprems_of th = 0 then ()
       else error ("2.11 refutation: premises in " ^ name) end)
  val report = "CLASSICISM-2.11-REFUTATION-AUDIT: " ^ string_of_int (length facts) ^
    " clean endpoints\n" ^
    "SCOPE: Proposition 2.11 is refuted: in the concrete action model every Classicism theorem and every instance of □Atomicity, Boolean Completeness and BF is valid, the Rigid Comprehension instance at type t→t is not, hence it is not derivable in the smallest H-theory containing C and the hypotheses. Main theorem premise-free. HOL-ZF foundations.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm))))
    (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "2-11-refutation-audit.txt"))
    [XML.Text report]
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "2-11-refutation-statements.txt"))
    [XML.Text statements]
  val _ = writeln report
in end
\<close>

end
