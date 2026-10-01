theory Classicism_2_11_Audit
  imports Typed_Paper_Model Typed_Source_Soundness Normalization_Witness_Setup
begin

text \<open>This application audit records the actual statements and checks
  theorem-object dependencies. It does not turn the remaining semantic
  claims of Proposition 2.11 into source-formula theorems.\<close>

ML \<open>
local
  val names = [
    "normalization_fiber_Inf_bottom", "normalization_does_not_preserve_fiber",
    "normalized_middle_not_atom", "no_rigid_profile_for_zero_fiber",
    "root_prop_atomic", "footnote_setup_and_normalization_loss",
    "typed_M_finite", "typed_M_nonempty", "typed_S_finite", "typed_j_onto",
    "typed_R_joint_surjective", "typed_R_application_s", "typed_R_application_n",
    "typed_R_extensional", "zprop_carrier", "typed_normalization_action_failure",
    "typed_req_type", "typed_rall_type", "tc_rK_type", "tc_rS_type", "ti_r_type",
    "src_enc_injective", "src_modal_structure", "src_model", "src_nontrivial_model",
    "src_interpretation_exists", "src_full_C_interpretation",
    "paper_enc_injective", "paper_premodel", "paper_primitive_identification",
    "concrete_paper_action_model", "concrete_paper_standard_model",
    "concrete_paper_term_totality", "concrete_paper_classicism_truth"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "2.11: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("2.11: residual obligations in " ^ name)
  val report = "CLASSICISM-2.11-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Concrete normalization/rigidity calculations; all-type carriers; exact book and paper modelhood; full typed interpretation. No end-to-end source-formula certificate of all Proposition 2.11 hypotheses and failure. HOL-ZF foundations.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm))))
    (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "2-11-audit.txt")) [XML.Text report]
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "2-11-statements.txt")) [XML.Text statements]
  val _ = writeln report
in end
\<close>

end
