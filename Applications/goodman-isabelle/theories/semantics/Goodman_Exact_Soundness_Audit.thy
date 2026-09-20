theory Goodman_Exact_Soundness_Audit
  imports Goodman_Exact_Goodman_Soundness
begin

section \<open>Audit of exact statements and kernel proof objects\<close>

ML \<open>
local
  val names = ["pp_e_constants.gi_exact_MF_global_valid",
    "pp_e_constants.gi_exact_C_global_sound",
    "pp_e_constants.gi_exact_extension_global_sound",
    "pp_e_constants.gi_exact_bottom_not_global",
    "pp_e_constants.gi_exact_consistent_of_global_axioms",
    "gi_exact_future_pointwise_identity",
    "pp_e_constants.gi_exact_named_leibniz_holds",
    "pp_e_constants.gi_exact_named_imp_holds",
    "pp_e_constants.gi_exact_named_all_holds",
    "pp_e_constants.gi_exact_named_top_holds",
    "pp_e_constants.gi_exact_named_box_holds",
    "pp_e_constants.gi_exact_MF_body_holds",
    "pp_e_constants.gi_exact_MF_axiom_holds",
    "gi_exact_identity_test_term_type",
    "gi_exact_identity_test_denotation",
    "gi_exact_identity_test_member",
    "gi_exact_identity_test_apply",
    "gi_exact_identity_test_truth",
    "gi_exact_local_identity_implies_leibniz",
    "gi_exact_leibniz_implies_local_identity",
    "gi_exact_leibniz_iff_local_identity",
    "gi_exact_leibniz_iff_action_identity",
    "gi_exact_root_leibniz_iff_equality",
    "gi_exact_global_validI",
    "gi_exact_global_validD",
    "gi_exact_propositions_extensional",
    "pp_e_constants.gi_exact_H_global_sound",
    "pp_e_constants.gi_exact_global_MP",
    "pp_e_constants.gi_exact_global_Gen",
    "pp_e_constants.gi_exact_global_PE",
    "gi_goodman_string_term_as_constant_rename",
    "gi_exact_goodman_denote_pullback",
    "gi_exact_goodman_global_valid_iff",
    "pp_e_constants.gi_exact_goodman_minimal_model",
    "pp_e_constants.gi_exact_goodman_extension_global_sound",
    "pp_e_constants.gi_exact_goodman_consistent_of_global_axioms",
    "gi_exact_empty_native_extension_consistent",
    "pp_e_constants.gi_exact_book_minimal_model",
    "pp_e_constants.gi_exact_book_H_sound",
    "pp_e_constants.gi_exact_book_H_at_world",
    "gi_exact_named_logical_value",
    "gi_exact_logical_value_member",
    "gi_exact_implication_truth",
    "gi_exact_forall_truth",
    "gi_exact_false_proposition",
    "gi_exact_logical_value_witness",
    "pp_e_constants.gi_exact_pterm_beta_eval",
    "pp_e_constants.gi_exact_pterm_eta_eval",
    "pp_e_constants.gi_exact_pterm_raw_conversion_eval",
    "pp_e_constants.gi_exact_pterm_signature_conversion_eval",
    "pp_e_constants.gi_exact_named_denote_conversion",
    "pp_e_constants.gi_exact_named_environment",
    "pp_e_constants.gi_exact_book_environment_conditions",
    "pp_e_constants.gi_exact_book_full_environment",
    "pp_e_constants.gi_exact_named_lambda_application"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-soundness: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-soundness: residual obligations in " ^ name)
  val report = "EXACT-SOUNDNESS-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: Exact-carrier full minimal models, beta-eta environment, all-type MF, global PE, full-C/native axiom-extension soundness. HOL-ZF and typed constants retained. Added axioms require global validity; PP is not validated.\n" ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-soundness-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-soundness-statements.txt")) [XML.Text statements]
in end
\<close>

end

