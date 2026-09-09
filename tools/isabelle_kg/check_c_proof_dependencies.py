#!/usr/bin/env python3
"""Check exported proof dependencies for C, H, and book canonical constructions.

Run after a successful graph refresh. This complements the kernel-object
audit; it does not establish source fidelity or fill missing exported bodies.
"""

from collections import defaultdict
import argparse
import json
from pathlib import Path


ROOTS = (
    "theorem:Bacon_C_Appendix_A2.C_Appendix_A2",
    "theorem:Bacon_C_Appendix_A3.C_Appendix_A3",
    "theorem:Bacon_C_Rule_Equivalence.C_rule_equivalence",
)
FORBIDDEN = {"CE_proves", "CEV_proves"}
H_ONLY_ROOTS = (
    "theorem:Bacon_H_Vector_Body.H_vector_body_logical_equivalence",
    "theorem:Bacon_H_Quantifier_Proof_Basics.Hq_absorb_disj_forall",
    "theorem:Bacon_H_Quantifier_Proof_Basics.Hq_absorb_conj_exists",
    "theorem:Bacon_H_Forall_Distribution.Hq_dist_disj_forall",
    "theorem:Bacon_H_Exists_Distribution.Hq_dist_conj_exists",
    "theorem:Bacon_H_Material_Identity_Identity.H_material_IdentityIdentity",
    "theorem:Bacon_HLE_Boolean_Identities.HLE_BooleanIdentity",
    "theorem:Bacon_HLE_Identity_Identity.HLE_IdentityIdentity",
    "theorem:Bacon_HLE_Quantifier_Identities.HLE_absorb_disj_forall",
    "theorem:Bacon_HLE_Quantifier_Identities.HLE_absorb_conj_exists",
    "theorem:Bacon_HLE_Quantifier_Identities.HLE_dist_disj_forall",
    "theorem:Bacon_HLE_Quantifier_Identities.HLE_dist_conj_exists",
)
NAMED_SYNTAX_ROOTS = (
    "theorem:Bacon_Source_Named_Alpha_Characterization.named_alpha_iff_encoding",
    "theorem:Bacon_Source_Named_Substitution_Representation.named_beta_encoding",
    "theorem:Bacon_Source_Named_Eta_Representation.named_eta_encoding",
    "theorem:Bacon_Source_Named_Conversion_Steps.named_beta_step_encoding",
    "theorem:Bacon_Source_Named_Conversion_Steps.named_eta_step_encoding",
    "theorem:Bacon_Source_Named_Conversion.named_conversion_prefix_eventual",
    "theorem:Bacon_Source_Named_Alpha_Conversion.named_alpha_implies_beta_eta",
    "theorem:Bacon_Source_Named_Signature_Conservativity.named_raw_to_signature",
    "theorem:Bacon_Source_Named_Decoder_Roundtrip.source_to_named_empty_encoding",
    "theorem:Bacon_Source_Named_Decoder_Roundtrip.source_to_named_fv_exact",
    "theorem:Bacon_Source_Named_Decoder_Beta.source_to_named_beta_root_conversion",
    "theorem:Bacon_Source_Named_Decoder_Eta.source_to_named_eta_root_conversion",
    "theorem:Bacon_Source_Named_Vector_Encoding.named_chart_closed_abstractions_alpha",
    "theorem:Bacon_Source_Named_Decoder_Conversion.source_to_named_conversion",
    "theorem:Bacon_Source_Named_Chart_Prefix.source_to_named_chart_prefix_alpha",
    "theorem:Bacon_Source_Minimal_Frame.source_typing_minimal_frame",
    "theorem:Bacon_Source_Named_Coherent_Charts.named_coherent_chart_valid",
    "theorem:Bacon_Source_Named_Closed_Roundtrip.named_closed_roundtrip_alpha",
    "theorem:Bacon_Source_Named_Prefix_Roundtrip.named_prefix_roundtrip_alpha",
    "theorem:Bacon_Source_Named_Logical_Encoding.named_paper_imp_const_encoding",
    "theorem:Bacon_Source_Named_Logical_Encoding.named_paper_iff_const_encoding",
    "theorem:Bacon_Source_Named_Propositional.named_PC_encoding",
    "theorem:Bacon_Source_Named_Representation_Reflection.source_named_representation_exists",
    "theorem:Bacon_Source_Named_Representation_Reflection.named_representation_language_iff",
    "theorem:Bacon_Source_Named_Nat_Coding.named_nat_code_inj",
)
NAMED_MODEL_ROOTS = (
    "theorem:Bacon_Source_Named_Model_Type_Tagging_Model.paper_named_bbk_model.model_type_tagging",
    "theorem:Bacon_Source_Named_Model_Type_Tagging_Model.paper_named_bbk_model.model_tag_valid_iff",
    "theorem:Bacon_Source_Chart_Denotation.paper_named_bbk_model.chart_denote_locality",
    "theorem:Bacon_Source_Chart_Independence.paper_named_bbk_model.chart_denote_independent",
    "theorem:Bacon_Source_Chart_Prefix_Denotation.paper_named_bbk_model.chart_denote_prefix",
    "theorem:Bacon_Source_Chart_Conversion_Denotation.paper_named_bbk_model.chart_denote_conversion",
    "theorem:Bacon_Source_Chart_Truth_Quantifiers.paper_named_bbk_model.chart_valuation_forall",
    "theorem:Bacon_Source_Erased_Denotation.named_erased_denote_agrees",
    "theorem:Bacon_Source_Erased_Locality.named_erased_denote_locality",
    "theorem:Bacon_Source_Erased_Truth.erased_valuation_forall",
    "theorem:Bacon_Source_Named_Reverse_Closed_Truth.paper_named_bbk_model.paper_named_reverse_closed_truth",
    "theorem:Bacon_Source_Named_Reverse_Open_Truth.paper_named_bbk_model.paper_named_reverse_prefix_denote",
    "theorem:Bacon_Source_Named_Reverse_Completion_Truth.paper_named_bbk_model.paper_named_reverse_completion_denote",
    "theorem:Bacon_Source_Named_Recoding_Model.paper_named_bbk_model.named_recode_model",
    "theorem:Bacon_Source_Named_Recoding_Validity.paper_named_bbk_model.named_recode_valid_iff",
)
NAMED_REVERSE_MODEL_ROOTS = (
    "theorem:Bacon_Source_Named_Reverse_Model.paper_tagged_named_to_db_model",
    "theorem:Bacon_Source_Named_Reverse_Model.paper_named_bbk_model.paper_named_to_db_model",
)
NAMED_PROOF_ROOTS = (
    "theorem:Bacon_Source_Named_H_Forward.paper_named_H_encoding",
    "theorem:Bacon_Source_Named_Local_Forward.paper_named_derivable_encoding",
    "theorem:Bacon_Source_Named_Local_Forward.paper_named_derivable_finite_support",
    "theorem:Bacon_Source_Named_H_Correspondence.paper_named_H_iff",
    "theorem:Bacon_Source_Named_Local_Correspondence.paper_named_derivable_iff",
    "theorem:Bacon_Source_Named_Consistency_Correspondence.paper_named_consistency_iff",
    "theorem:Bacon_Source_Named_Existence.paper_named_type_existence",
)
NATIVE_H_ROOTS = (
    "theorem:Bacon_Source_Named_H_Conversion.paper_named_H_iff_conversion",
    "theorem:Bacon_Source_Named_H_Alpha.paper_named_H_same_encoding",
    "theorem:Bacon_Source_Named_H_Reverse_PC.paper_named_PC_preimage",
    "theorem:Bacon_Source_Named_H_Reverse_Conversion.paper_named_beta_preimage",
    "theorem:Bacon_Source_Named_H_Reverse_Rules.paper_named_Gen_preimage",
)
BOOK_ENV_ROOTS = (
    "theorem:Bacon_Book_Conjunction_Axiom_Truth.book_full_minimal_model.book_conjunction_axioms_truth",
    "theorem:Bacon_Book_Closed_Value_Convention.book_environment_conditions.book_closed_value_iff_all_assignments",
    "theorem:Bacon_Book_Closed_Value_Convention.book_environment_conditions.book_closed_value_iff_at",
    "theorem:Bacon_Book_General_Environment.book_full_environment.book_full_environment_general_restriction",
    "theorem:Bacon_Book_General_Environment.book_general_full_environment_iff",
    "theorem:Bacon_Book_General_Application.book_general_environment_conditions.book_general_denote_app",
    "theorem:Bacon_Book_General_Interpretation.book_general_interpretation.book_general_interpretation_application",
    "theorem:Bacon_Book_General_Interpretation.book_general_interpretation_restrict_full",
    "theorem:Bacon_Book_Constant_Model_Pullback.book_full_environment.book_constant_pullback_full_environment",
    "theorem:Bacon_Book_Constant_Model_Pullback.book_full_minimal_model.book_constant_pullback_full_minimal_model",
    "theorem:Bacon_Book_Universal_Closure_Truth.book_full_minimal_model.book_formula_valid_universal_closure_iff",
    "theorem:Bacon_Book_Universal_Closure_Truth.book_full_minimal_model.book_formula_valid_universal_closures_iff",
    "theorem:Bacon_Book_Minimal_Existential_Truth.book_full_minimal_model.book_exists_application_truth",
    "theorem:Bacon_Book_Minimal_Existential_Truth.book_full_minimal_model.book_exists_truth",
    "theorem:Bacon_Book_Two_Abstractions.book_full_environment.book_two_abstractions_denote",
    "theorem:Bacon_Book_Minimal_Leibniz_Truth.book_full_minimal_model.book_leibniz_truth",
    "theorem:Bacon_Book_Total_Assignments.book_total_assignment_exists_iff",
    "theorem:Bacon_Book_Environment_Equivalence.book_environment_conditions_iff_separated",
    "theorem:Bacon_Book_Full_Environment.book_full_environment.book_full_lambda_application",
    "theorem:Bacon_Book_Closed_Values.book_environment_conditions.book_closed_value_exists_iff_domains",
    "theorem:Bacon_Book_Leibniz_Equivalence.book_leibniz_equiv_on_domain",
    "theorem:Bacon_Book_Identity_Predicate.book_full_environment.book_identity_operation_exists",
    "theorem:Bacon_Book_Leibniz_Valuation.book_full_environment.book_leibniz_valuation_invariant",
    "theorem:Bacon_Book_Leibniz_Valuation.book_leibniz_valuation_from_negation",
    "theorem:Bacon_Book_Implication_Valuation.book_applicative_structure.book_implication_false_point_witnesses",
    "theorem:Bacon_Book_Implication_Valuation.book_applicative_structure.book_leibniz_valuation_from_implication",
    "theorem:Bacon_Book_Argument_Test.book_full_environment.book_argument_test_exists",
    "theorem:Bacon_Book_Head_Test.book_full_environment.book_head_test_exists",
    "theorem:Bacon_Book_Leibniz_Application.book_full_environment.book_leibniz_application_cong",
    "theorem:Bacon_Book_Leibniz_Assignments.book_full_environment.book_leibniz_denote_assignments",
    "theorem:Bacon_Book_Leibniz_Classes.book_leibniz_class_eq_iff",
    "theorem:Bacon_Book_Leibniz_Classes.book_leibniz_rep_reconstruct",
    "theorem:Bacon_Book_Quotient_Application.book_applicative_structure.book_leibniz_quotient_applicative_structure",
    "theorem:Bacon_Book_Quotient_Application.book_full_environment.book_leibniz_quotient_application_projection",
    "theorem:Bacon_Book_Quotient_Valuation.book_full_environment.book_leibniz_quotient_valuation_projection",
    "theorem:Bacon_Book_Quotient_Separation.book_full_environment.book_leibniz_quotient_separation",
    "theorem:Bacon_Book_Quotient_Environment.book_full_environment.book_leibniz_quotient_environment",
    "theorem:Bacon_Book_Quotient_Truth.book_full_environment.book_leibniz_quotient_denote_projection",
    "theorem:Bacon_Book_Quotient_Truth.book_full_environment.book_leibniz_quotient_validity_iff",
    "theorem:Bacon_Book_Full_Minimal_Model.book_full_minimal_model.book_minimal_assignment_exists",
    "theorem:Bacon_Book_Quotient_Logical_Clauses.book_full_environment.book_quotient_implication_clause",
    "theorem:Bacon_Book_Quotient_Logical_Clauses.book_full_environment.book_quotient_forall_clause",
    "theorem:Bacon_Book_Full_Minimal_Quotient.book_full_minimal_model.book_full_minimal_quotient_model",
    "theorem:Bacon_Book_Quotient_Theorem.book_full_minimal_model.book_proposition_15_5_full_minimal",
    "theorem:Bacon_Book_Minimal_Truth.book_full_minimal_model.book_imp_truth",
    "theorem:Bacon_Book_Minimal_Truth.book_full_minimal_model.book_all_truth",
    "theorem:Bacon_Book_Minimal_Truth.book_full_minimal_model.book_bottom_false",
    "theorem:Bacon_Book_Minimal_Truth.book_full_minimal_model.book_not_truth",
    "theorem:Bacon_Book_Minimal_Boolean_Truth.book_full_minimal_model.book_or_truth",
    "theorem:Bacon_Book_Minimal_Boolean_Truth.book_full_minimal_model.book_and_truth",
    "theorem:Bacon_Book_Minimal_Boolean_Truth.book_full_minimal_model.book_iff_truth",
    "theorem:Bacon_Book_Minimal_Boolean_Truth.book_full_minimal_model.book_top_true",
)
BOOK_HENKIN_SYNTAX_ROOTS = (
    "theorem:Bacon_Book_Henkin_Name_Stages.book_henkin_signature_mono",
    "theorem:Bacon_Book_Henkin_Name_Stages.book_henkin_signature_original_iff",
    "theorem:Bacon_Book_Henkin_Name_Stages.book_henkin_signature_witness_index",
    "theorem:Bacon_Book_Henkin_Name_Stages.book_henkin_signature_witness_fresh",
    "theorem:Bacon_Book_Henkin_Stage_Witnesses.book_henkin_stage_name_inj",
    "theorem:Bacon_Book_Henkin_Stage_Witnesses.book_henkin_signature_family",
    "theorem:Bacon_Book_Henkin_Stage_Witnesses.book_henkin_stage_axioms_closed_set",
    "theorem:Bacon_Book_Henkin_Full_Signature.book_henkin_full_names_eventual",
    "theorem:Bacon_Book_Henkin_Full_Signature.book_henkin_full_language_eventually",
    "theorem:Bacon_Book_Henkin_Full_Signature.book_henkin_full_closed_predicate_witness",
    "theorem:Bacon_Book_Henkin_Witness_Coverage.book_henkin_witness_coverage",
    "theorem:Bacon_Book_Henkin_Witness_Coverage.book_henkin_all_witness_axioms_closed_set",
)
BOOK_THEORY_PURE_ROOTS = (
    "theorem:Bacon_Book_Printed_Theory_Correspondence.book_printed_theory_to_theory",
    "theorem:Bacon_Book_Printed_Theory_Correspondence.book_theory_to_printed",
    "theorem:Bacon_Book_Printed_Theory_Correspondence.book_theory_iff_printed",
    "theorem:Bacon_Book_Printed_Theory_Correspondence.book_H_iff_printed",
    "theorem:Bacon_Book_Printed_Completeness.book_consistency_iff_printed",
    "theorem:Bacon_Book_Quantifier_Proof_Basics.book_theory_double_negation_schema",
    "theorem:Bacon_Book_Quantifier_Proof_Basics.book_theory_forall_eta_pair",
    "theorem:Bacon_Book_Closed_Quantifier_Duality.book_theory_closed_forall_dual",
    "theorem:Bacon_Book_Closed_Universal_Instances.book_closed_maximal_forall_instance",
    "theorem:Bacon_Book_Closed_Universal_Truth.book_closed_maximal_forall_iff",
    "theorem:Bacon_Book_Finite_Image_Cover.book_finite_image_cover",
    "theorem:Bacon_Book_Finite_Image_Cover.book_theory_consistent_signature_transport",
    "theorem:Bacon_Book_Finite_Witness_Family.book_theory_consistent_finite_witness_family",
    "theorem:Bacon_Book_Infinite_Witness_Family.book_theory_consistent_witness_family",
    "theorem:Bacon_Book_Henkin_Stage_Consistency.book_henkin_stage_consistent",
    "theorem:Bacon_Book_Henkin_Premise_Stages.book_henkin_premises_language",
    "theorem:Bacon_Book_Henkin_Premise_Stages.book_henkin_premises_consistent",
    "theorem:Bacon_Book_Henkin_Premise_Stages.book_henkin_premises_closed_set",
    "theorem:Bacon_Book_Henkin_Union.book_henkin_full_premises_language",
    "theorem:Bacon_Book_Henkin_Union.book_henkin_full_premises_consistent",
    "theorem:Bacon_Book_Henkin_Union.book_henkin_all_witness_axioms_in_premises",
    "theorem:Bacon_Book_Henkin_Union.book_henkin_full_premises_witness",
    "theorem:Bacon_Book_Closed_Witness_Completeness.book_closed_constant_witness_complete_from_conditionals",
    "theorem:Bacon_Book_Closed_Henkin_Extension.book_henkin_closed_premises_consistent",
    "theorem:Bacon_Book_Closed_Henkin_Extension.book_closed_henkin_maximal_exists",
    "theorem:Bacon_Book_Closed_Henkin_Extension.book_closed_henkin_original",
    "theorem:Bacon_Book_Closed_Henkin_Extension.book_closed_henkin_conditional_witness",
    "theorem:Bacon_Book_Closed_Henkin_Extension.book_closed_henkin_extension_exists",
    "theorem:Bacon_Book_Consistency_Unions.book_finite_directed_cover",
    "theorem:Bacon_Book_Consistency_Unions.book_theory_consistent_directed_Union",
    "theorem:Bacon_Book_Consistency_Unions.book_theory_consistent_chain_Union",
    "theorem:Bacon_Book_Existential_Conversion.book_exists_beta_contract",
    "theorem:Bacon_Book_Existential_Conversion.book_theory_exists_conversion_pair",
    "theorem:Bacon_Book_Fresh_Constant_Generalization.book_theory_fresh_constant_retraction",
    "theorem:Bacon_Book_Fresh_Constant_Generalization.book_theory_fresh_constant_generalization",
    "theorem:Bacon_Book_Constant_Renaming.book_constant_rename_language",
    "theorem:Bacon_Book_Constant_Renaming.book_constant_rename_subst",
    "theorem:Bacon_Book_Constant_Renaming.book_constant_rename_free_for",
    "theorem:Bacon_Book_Constant_Renaming.book_constant_rename_beta_step",
    "theorem:Bacon_Book_Constant_Renaming.book_constant_rename_eta_step",
    "theorem:Bacon_Book_Constant_Renaming.book_constant_rename_injective_signature",
    "theorem:Bacon_Book_Theory_Constant_Renaming.book_theory_constant_rename",
    "theorem:Bacon_Book_Constant_Renaming_Reflection.book_theory_constant_rename_iff",
    "theorem:Bacon_Book_Constant_Renaming_Reflection.book_theory_consistent_constant_rename_iff",
    "theorem:Bacon_Book_Constant_Renaming_Reflection.book_sum_image_has_fresh_name",
    "theorem:Bacon_Book_Negative_Predicate_Generalization.book_theory_negative_predicate_generalize",
    "theorem:Bacon_Book_Closed_Witness_Choice.book_theory_closed_witness_choice",
    "theorem:Bacon_Book_Closed_Maximal_Extension.book_closed_maximal_extension_exists",
    "theorem:Bacon_Book_Closed_Negation_Complete.book_theory_consistent_insert_consequence",
    "theorem:Bacon_Book_Closed_Negation_Complete.book_closed_maximal_derivable_member",
    "theorem:Bacon_Book_Closed_Negation_Complete.book_closed_maximal_decides",
    "theorem:Bacon_Book_Closed_Negation_Complete.book_closed_maximal_negation_iff",
    "theorem:Bacon_Book_Closed_Negation_Complete.book_closed_decision_extension_exists",
    "theorem:Bacon_Book_Fresh_Witness_Name.book_theory_fresh_witness_name_choice",
    "theorem:Bacon_Book_Conditional_Witness.book_witness_axiom_language",
    "theorem:Bacon_Book_Conditional_Witness.book_witness_axiom_closed",
    "theorem:Bacon_Book_Conditional_Witness.book_theory_consistent_conditional_witness",
    "theorem:Bacon_Book_Fresh_Conditional_Witness.book_theory_consistent_fresh_conditional_witness",
    "theorem:Bacon_Book_Theory_Consistency.book_theory_refutation_schema",
    "theorem:Bacon_Book_Theory_Consistency.book_theory_closed_refutation",
    "theorem:Bacon_Book_Theory_Consistency.book_theory_consistent_insert_not",
    "theorem:Bacon_Book_Theory_Consistency.book_theory_consistent_insert_not_universal_closure",
    "theorem:Bacon_Book_Theory_Consistency.book_theory_consistent_subset",
    "theorem:Bacon_Book_Theory_Consistency.book_theory_consistent_finite_iff",
    "theorem:Bacon_Book_Universal_Closure.book_theory_all_elim_variable",
    "theorem:Bacon_Book_Universal_Closure.book_universal_closure_language",
    "theorem:Bacon_Book_Universal_Closure.book_universal_closure_closed",
    "theorem:Bacon_Book_Universal_Closure.book_theory_universal_closure_iff",
    "theorem:Bacon_Book_Universal_Closure_Theories.book_theory_universal_closures_equivalent",
    "theorem:Bacon_Book_Universal_Closure_Theories.book_theory_universal_closures_closed_fragment",
    "theorem:Bacon_Book_Universal_Closure_Theories.book_theory_closed_fragment_equivalent",
    "theorem:Bacon_Book_Open_Propositional_Decision.book_theory_open_positive_bottom",
    "theorem:Bacon_Book_Open_Propositional_Decision.book_theory_open_negative_bottom",
    "theorem:Bacon_Book_Open_Propositional_Decision.book_theory_open_propositional_decision",
    "theorem:Bacon_Book_Open_Propositional_Decision.book_theory_all_open_decisions_bottom",
    "theorem:Bacon_Book_Propositional_Certificates.book_prop_certificate_embeds",
    "theorem:Bacon_Book_Propositional_Certificates.book_prop_certificate_deduction",
    "theorem:Bacon_Book_Negation_Conversion.book_theory_not_conversion_pair",
    "theorem:Bacon_Book_Negation_Conversion.book_theory_not_bottom",
    "theorem:Bacon_Book_Propositional_Explosion.book_theory_explosion_curried",
    "theorem:Bacon_Book_Propositional_Negation.book_prop_certificate_RAA",
    "theorem:Bacon_Book_Conjunction_Certificates.book_prop_certificate_conj_intro",
    "theorem:Bacon_Book_Conjunction_Certificates.book_prop_certificate_conj_left",
    "theorem:Bacon_Book_Conjunction_Certificates.book_prop_certificate_conj_right",
    "theorem:Bacon_Book_Conjunction_Currying.book_theory_conj_uncurry",
    "theorem:Bacon_Book_Conjunction_Currying.book_theory_conj_curry",
    "theorem:Bacon_Book_Closed_Deduction.book_theory_closed_deduction",
    "theorem:Bacon_Book_Closed_Deduction.book_theory_closed_deduction_iff",
    "theorem:Bacon_Book_Finite_Fresh_Variables.book_finite_fresh_variables",
    "theorem:Bacon_Book_Simultaneous_Substitution_Syntax.book_simult_subst_type",
    "theorem:Bacon_Book_Simultaneous_Substitution_Language.book_simult_subst_language",
    "theorem:Bacon_Book_Simultaneous_Substitution_Language.book_simult_subst_map_eq",
    "theorem:Bacon_Book_Simultaneous_Substitution_Language.book_simult_free_for_map_eq",
    "theorem:Bacon_Book_Simultaneous_Substitution_Singleton.book_simult_single_variable_free_for",
    "theorem:Bacon_Book_Simultaneous_Substitution_Singleton.book_simult_single_constant_free_for",
    "theorem:Bacon_Book_Simultaneous_Substitution_Singleton.book_theory_simult_single",
    "theorem:Bacon_Book_Substitution_Freshness.book_subst_marker_exists",
    "theorem:Bacon_Book_Simultaneous_Substitution_Peeling.book_simult_subst_peeling",
    "theorem:Bacon_Book_Simultaneous_Substitution_Peeling_Free_For.book_simult_subst_peeling_free_for",
    "theorem:Bacon_Book_Theory_Simultaneous_Substitution.book_theory_simultaneous_substitution",
    "theorem:Bacon_Book_Logic.book_least_theory_is_logic",
    "theorem:Bacon_Book_Logic.book_H_iff_theory",
    "theorem:Bacon_Book_Logic.book_H_language",
    "theorem:Bacon_Book_Theory_Conversion.book_theory_imp_trans",
    "theorem:Bacon_Book_Theory_Conversion.book_theory_conversion_pair",
    "theorem:Bacon_Book_Theory_Conversion.book_theory_raw_conversion_iff",
    "theorem:Bacon_Book_Theory_Conversion.book_theory_alpha_iff",
    "theorem:Bacon_Book_Theory_Variable_Substitution.book_theory_variable_substitution",
    "theorem:Bacon_Book_Theory_Variable_Substitution.book_theory_free_variable_closed",
    "theorem:Bacon_Book_Theory_Signature_Monotonicity.book_theory_signature_mono",
    "theorem:Bacon_Book_Theory_Retraction.book_theory_retraction",
    "theorem:Bacon_Book_Theory_Signature_Conservativity.book_theory_foreign_constants_eliminate",
    "theorem:Bacon_Book_Theory_Signature_Conservativity.book_theory_signature_conservativity",
    "theorem:Bacon_Book_Constant_Substitution_Syntax.book_const_subst_language",
    "theorem:Bacon_Book_Constant_Substitution_Abstraction.book_const_abstract_instantiate",
    "theorem:Bacon_Book_Constant_Substitution_Abstraction.book_const_abstract_free_for_iff",
    "theorem:Bacon_Book_Remove_Constant.book_theory_fresh_constant_variable",
    "theorem:Bacon_Book_Theory_Constant_Substitution.book_theory_constant_substitution",
    "theorem:Bacon_Book_Swap_Abbreviations.book_swap_closed_alpha",
    "theorem:Bacon_Book_Swap_Abbreviations.book_swap_not_alpha",
    "theorem:Bacon_Book_Minimal_Existential_Syntax.book_exists_const_language",
    "theorem:Bacon_Book_Minimal_Leibniz_Syntax.book_leibniz_const_language",
    "theorem:Bacon_Book_Theory_Derivation.book_theory_derivable_language",
    "theorem:Bacon_Book_Theory_Derivation.book_theory_derivable_finite_support",
    "theorem:Bacon_Book_Theory_Derivation.book_theory_derivable_iff_all_theories",
    "theorem:Bacon_Book_Theory_Intersections.book_higher_order_theory_iff_rules",
    "theorem:Bacon_Book_Theory_Intersections.book_common_theory_is_theory",
    "theorem:Bacon_Book_Open_Deduction_Boundary.book_theory_open_prop_bottom",
)
BOOK_BBK_SYNTAX_ROOTS = (
    "theorem:Bacon_Book_Named_Translation.book_named_translation_fv",
    "theorem:Bacon_Book_Named_Translation.book_named_translation_language_eventual",
    "theorem:Bacon_Book_Named_Translation.book_named_translation_conversion_eventual",
)
BOOK_BBK_CONSTRUCTION_ROOTS = (
    "theorem:Bacon_Book_BBK_Application.pbbk_model.pbbk_book_app_type",
    "theorem:Bacon_Book_BBK_Application.pbbk_model.pbbk_book_app_represents",
    "theorem:Bacon_Book_BBK_Environment.pbbk_model.pbbk_book_full_environment",
    "theorem:Bacon_Book_BBK_False_Value.pbbk_model.pbbk_book_assignment_exists",
    "theorem:Bacon_Book_BBK_Logical_Values.pbbk_model.pbbk_book_logical_value_type",
    "theorem:Bacon_Book_BBK_Logical_Values.pbbk_model.pbbk_book_logical_value_at",
    "theorem:Bacon_Book_BBK_False_Value.pbbk_model.pbbk_book_false_value",
    "theorem:Bacon_Book_BBK_Implication_Truth.pbbk_model.pbbk_book_implication_truth",
    "theorem:Bacon_Book_BBK_Universal_Truth.pbbk_model.pbbk_book_forall_truth",
    "theorem:Bacon_Book_BBK_Model.pbbk_model.pbbk_to_book_full_minimal_model",
)
BOOK_INHABITATION_ROOTS = (
    "theorem:Bacon_Book_Model_Inhabitation.book_H_nonderives_bottom",
    "theorem:Bacon_Book_Model_Inhabitation.book_full_minimal_model_exists",
    "theorem:Bacon_Book_Model_Inhabitation.book_standard_full_minimal_model_exists",
    "theorem:Bacon_Book_Model_Inhabitation.book_empty_theory_nonderives_bottom",
    "theorem:Bacon_Book_Model_Inhabitation.book_open_deduction_failure",
)
# These roots concern the beta/eta closed-term quotient, not the earlier
# conditional quotient of an already supplied book model. Keep syntax,
# constructed structure, and native-proof-based valuation checks separate.
BOOK_CONVERSION_SYNTAX_ROOTS = (
    "theorem:Bacon_Book_Primitive_Conjunction_Encoding.book_conj_target_tag_iff",
    "theorem:Bacon_Book_Primitive_Conjunction_Encoding.book_conj_encode_language",
    "theorem:Bacon_Book_Primitive_Conjunction_Decoding.book_conj_decode_encode",
    "theorem:Bacon_Book_Primitive_Conjunction_Decoding.book_conj_encode_decode",
    "theorem:Bacon_Book_Primitive_Conjunction_Decoding.book_conj_encode_language_iff",
    "theorem:Bacon_Book_Source_Reduction_Contexts.book_source_reduces_App_left",
    "theorem:Bacon_Book_Source_Reduction_Contexts.book_source_reduces_App_right",
    "theorem:Bacon_Book_Source_Reduction_Contexts.book_source_reduces_Lam",
    "theorem:Bacon_Book_Source_Reduction_Contexts.book_source_reduces_App",
    "theorem:Bacon_Book_Printed_Contextual_Beta_Simulation.book_printed_beta_contract_simulation",
    "theorem:Bacon_Book_Printed_Contextual_Beta_Simulation.book_printed_beta_step_simulation",
    "theorem:Bacon_Book_Source_Reduction_Conversion.book_source_step_printed_conversion",
    "theorem:Bacon_Book_Source_Reduction_Conversion.book_source_reduces_printed_conversion",
    "theorem:Bacon_Book_Source_Reduction_Conversion.book_exact_beta_step_printed_conversion",
    "theorem:Bacon_Book_Printed_Conversion_Correspondence.book_printed_conversion_named",
    "theorem:Bacon_Book_Printed_Conversion_Correspondence.book_named_conversion_printed",
    "theorem:Bacon_Book_Printed_Conversion_Correspondence.book_named_conversion_iff_printed",
    "theorem:Bacon_Book_Printed_Conversion_Correspondence.book_raw_conversion_iff_printed",
    "theorem:Bacon_Book_Variable_Substitution_Language.book_variable_subst_language",
    "theorem:Bacon_Book_Reduction_Language.book_beta_contract_language",
    "theorem:Bacon_Book_Reduction_Language.book_eta_contract_language",
    "theorem:Bacon_Book_Contextual_Reduction_Language.book_beta_step_language",
    "theorem:Bacon_Book_Contextual_Reduction_Language.book_eta_step_language",
    "theorem:Bacon_Book_Logical_Substitution_Syntax.book_logical_subst_language",
    "theorem:Bacon_Book_Alpha_Language.book_alpha_language_iff",
    "theorem:Bacon_Book_Printed_Free_For.book_printed_free_for_named",
    "theorem:Bacon_Book_Printed_Free_For.book_printed_free_for_constant",
    "theorem:Bacon_Book_Printed_Free_For.book_printed_free_for_logical",
    "theorem:Bacon_Book_Source_Reduction.book_source_reduces_language",
    "theorem:Bacon_Book_Variable_Relettering_Syntax.book_variable_reletter_language",
    "theorem:Bacon_Book_General_Lambda_Language.book_general_lambda_language.book_general_application_parts",
    "theorem:Bacon_Book_General_Lambda_Language.book_general_lambda_language.book_general_alpha_closed",
    "theorem:Bacon_Book_Full_General_Language.book_full_general_lambda_language",
    "theorem:Bacon_Book_Printed_Binder_Freshening.book_printed_free_for_bound_names",
    "theorem:Bacon_Book_Printed_Binder_Freshening.book_printed_binder_freshening",
    "theorem:Bacon_Book_Printed_Beta_Simulation.book_printed_beta_simulation",
    "theorem:Bacon_Book_Constant_Renaming_Conversion.book_constant_rename_raw_conversion",
    "theorem:Bacon_Book_Conversion_Classes.book_conversion_class_eq_iff",
    "theorem:Bacon_Book_Conversion_Classes.book_conversion_rep_class",
    "theorem:Bacon_Book_Conversion_Application.book_conversion_app_type",
    "theorem:Bacon_Book_Conversion_Application.book_conversion_app_classes",
    "theorem:Bacon_Book_Closed_Environment_Substitution.book_environment_subst_type",
    "theorem:Bacon_Book_Closed_Environment_Substitution.book_environment_subst_language",
    "theorem:Bacon_Book_Closed_Environment_Substitution.book_environment_subst_fv",
    "theorem:Bacon_Book_Closed_Environment_Substitution.book_environment_subst_fixed",
    "theorem:Bacon_Book_Closed_Environment_Substitution.book_environment_subst_locality",
    "theorem:Bacon_Book_Environment_Substitution_Beta_Syntax.book_environment_subst_bound_irrelevant",
    "theorem:Bacon_Book_Environment_Substitution_Beta_Syntax.book_environment_subst_beta_commute",
    "theorem:Bacon_Book_Environment_Substitution_Contractions.book_environment_subst_beta_free_for",
    "theorem:Bacon_Book_Environment_Substitution_Contractions.book_environment_subst_beta_contract",
    "theorem:Bacon_Book_Environment_Substitution_Contractions.book_environment_subst_eta_contract",
    "theorem:Bacon_Book_Environment_Substitution_Conversion.book_environment_subst_beta_step",
    "theorem:Bacon_Book_Environment_Substitution_Conversion.book_environment_subst_eta_step",
    "theorem:Bacon_Book_Environment_Substitution_Conversion.book_environment_subst_raw_conversion",
    "theorem:Bacon_Book_Henkin_Closed_Terms.book_henkin_full_closed_term_exists",
    "theorem:Bacon_Book_Conversion_Domain_Inhabitation.book_henkin_conversion_domain_nonempty",
    "theorem:Bacon_Book_Conversion_Logical_Values.book_conversion_logical_value_type",
    "theorem:Bacon_Book_Conversion_Logical_Values.book_conversion_implication_app_classes",
    "theorem:Bacon_Book_Conversion_Logical_Values.book_conversion_bottom_in_domain",
)
BOOK_CONVERSION_STRUCTURE_ROOTS = (
    "theorem:Bacon_Book_Conversion_Denotation.book_conversion_denote_type",
    "theorem:Bacon_Book_Conversion_Denotation.book_conversion_denote_var",
    "theorem:Bacon_Book_Conversion_Denotation.book_conversion_denote_closed",
    "theorem:Bacon_Book_Conversion_Denotation.book_conversion_denote_app",
    "theorem:Bacon_Book_Conversion_Denotation.book_conversion_denote_locality",
    "theorem:Bacon_Book_Conversion_Environment.book_conversion_denote_conversion",
    "theorem:Bacon_Book_Conversion_Environment.book_conversion_separated_environment",
    "theorem:Bacon_Book_Conversion_Environment.book_conversion_full_environment",
    "theorem:Bacon_Book_Conversion_Closed_Values.book_henkin_conversion_assignment_typed",
    "theorem:Bacon_Book_Conversion_Closed_Values.book_henkin_conversion_assignment_exists",
    "theorem:Bacon_Book_Conversion_Closed_Values.book_conversion_logical_denote",
    "theorem:Bacon_Book_Conversion_Closed_Values.book_henkin_conversion_logical_witness",
    "theorem:Bacon_Book_Conversion_Closed_Values.book_henkin_conversion_closed_witness",
    "theorem:Bacon_Book_Conversion_Closed_Values.book_henkin_conversion_closed_value",
    "theorem:Bacon_Book_Conversion_Closed_Values.book_henkin_conversion_logical_closed_value",
)
BOOK_CONVERSION_VALUATION_ROOTS = (
    "theorem:Bacon_Book_Conversion_Universal_Valuation.book_conversion_forall_truth",
    "theorem:Bacon_Book_Conversion_Valuation.book_conversion_valuation_class",
    "theorem:Bacon_Book_Conversion_Valuation.book_conversion_valuation_bottom",
    "theorem:Bacon_Book_Conversion_Valuation.book_conversion_valuation_implication",
    "theorem:Bacon_Book_Conversion_Logical_Values.book_conversion_implication_truth",
    "theorem:Bacon_Book_Conversion_Logical_Values.book_conversion_false_exists",
)
BOOK_CONVERSION_ROOTS = (
    *BOOK_CONVERSION_SYNTAX_ROOTS,
    *BOOK_CONVERSION_STRUCTURE_ROOTS,
    *BOOK_CONVERSION_VALUATION_ROOTS,
)
BOOK_CONVERSION_FOREIGN_PREDICATES = {
    "H_proves", "pH_proves", "paper_global_H", "paper_global_derivable",
    "paper_named_H", "paper_named_derivable",
    "pbbk_model", "pbbk_model_axioms", "bbk_model", "bbk_model_axioms",
    "paper_db_bbk_structure", "paper_db_bbk_structure_axioms",
    "paper_db_bbk_model", "paper_db_bbk_model_axioms",
    "paper_named_bbk_model", "paper_named_bbk_model_axioms",
    "bacon_general_model", "bacon_general_model_axioms",
    "book_full_minimal_model", "book_full_minimal_model_axioms",
    "book_formula_valid",
}
BOOK_CONVERSION_NATIVE_PROOF_PREDICATES = {
    "book_theory_derivable", "book_higher_order_theory",
    "book_H", "book_higher_order_logic", "book_theory_consistent",
    "book_prop_certificate", "book_closed_maximal_extension",
    "book_closed_constant_witness_complete",
}
BOOK_CONVERSION_ENVIRONMENT_PREDICATES = {
    "book_env_typed", "book_closed_value",
    "book_applicative_structure", "book_applicative_structure_axioms",
    "book_interpretation_structure", "book_interpretation_structure_axioms",
    "book_environment_conditions", "book_environment_conditions_axioms",
    "book_environment_separated", "book_environment_separated_axioms",
    "book_full_environment", "book_full_environment_axioms",
}

# These proofs must be independent of the old exact-capture conversion and
# theory judgments. Imports alone do not fail the check: reached proof bodies
# and their propositions do. The independently defined named_alpha relation
# is allowed as an induction premise, but alpha-inclusive source reduction
# must not supply a conversion step. Printed-theory roots may use their own
# book_printed_theory_derivable judgment, not the older theory calculus.
BOOK_PRINTED_INDEPENDENT_ROOTS = (
    "theorem:Bacon_Book_Printed_Conversion_Contexts.book_printed_conversion_context",
    "theorem:Bacon_Book_Printed_Conversion_Contexts.book_printed_conversion_Lam",
    "theorem:Bacon_Book_Printed_Conversion_Contexts.book_printed_conversion_App_left",
    "theorem:Bacon_Book_Printed_Conversion_Contexts.book_printed_conversion_App_right",
    "theorem:Bacon_Book_Printed_Conversion_Contexts.book_printed_conversion_App",
    "theorem:Bacon_Book_Printed_Binder_Conversion.book_printed_binder_literal_rename",
    "theorem:Bacon_Book_Printed_Alpha_Alignment.book_printed_subst_swap_conversion",
    "theorem:Bacon_Book_Printed_Alpha_Conversion.book_alpha_implies_printed_conversion",
    "theorem:Bacon_Book_Printed_Theory_Derivation.book_printed_theory_derivable_language",
    "theorem:Bacon_Book_Printed_Theory_Propositional_Basics.book_printed_theory_imp_trans",
    "theorem:Bacon_Book_Printed_Theory_Conversion.book_printed_theory_conversion_pair",
)
BOOK_PRINTED_INDEPENDENT_FORBIDDEN = (
    BOOK_CONVERSION_FOREIGN_PREDICATES
    | BOOK_CONVERSION_NATIVE_PROOF_PREDICATES
    | BOOK_CONVERSION_ENVIRONMENT_PREDICATES
    | {
        "named_beta_eta_in_language", "named_raw_beta_eta", "named_beta_contract",
        "book_source_reduces", "book_source_reduction_step",
        "H_signature_proves", "H_set_derivable", "H_consistent",
        "pH_set_derivable", "pH_consistent",
        "applicative_structure", "applicative_structure_axioms",
        "classicist_structure", "classicist_structure_axioms",
        "propositional_equivalence_structure", "propositional_equivalence_structure_axioms",
        "vector_equivalence_structure", "vector_equivalence_structure_axioms",
        "book_general_environment_conditions", "book_general_environment_conditions_axioms",
        "book_general_interpretation", "book_general_interpretation_axioms",
    }
)


def book_conversion_forbidden(root):
    """Predicates excluded from all reached theorem propositions for a root.

    Structure roots legitimately mention constructed environment predicates
    in conclusions and book_env_typed in assignment guards. Their absence
    as assumed interpretations still requires the source/premise audit.
    Valuation roots legitimately use native derivability and closed maximality,
    but must not depend on a pre-existing interpretation or logical model.
    Pure syntax roots exclude both categories. Locale *_axioms predicates
    are included explicitly so unfolding a locale does not bypass the check.
    """
    if root not in BOOK_CONVERSION_ROOTS:
        return set()
    forbidden = set(BOOK_CONVERSION_FOREIGN_PREDICATES)
    if root in BOOK_CONVERSION_SYNTAX_ROOTS or root in BOOK_CONVERSION_STRUCTURE_ROOTS:
        forbidden |= BOOK_CONVERSION_NATIVE_PROOF_PREDICATES
    if root in BOOK_CONVERSION_SYNTAX_ROOTS:
        forbidden.add("book_printed_theory_derivable")
    if root in BOOK_CONVERSION_SYNTAX_ROOTS or root in BOOK_CONVERSION_VALUATION_ROOTS:
        forbidden |= BOOK_CONVERSION_ENVIRONMENT_PREDICATES
    return forbidden


# The primitive-conjunction extension has five different proof boundaries.
# In particular, truth of the fixed background is a semantic calculation,
# whereas membership in that background during proof encoding is an assumption.
BOOK_CONJUNCTION_SYNTAX_ROOTS = (
    "theorem:Bacon_Book_Primitive_Disjunction_Encoding.book_disj_target_tag_iff",
    "theorem:Bacon_Book_Primitive_Disjunction_Encoding.book_disj_encode_language",
    "theorem:Bacon_Book_Primitive_Disjunction_Decoding.book_disj_decode_encode",
    "theorem:Bacon_Book_Primitive_Disjunction_Decoding.book_disj_encode_decode",
    "theorem:Bacon_Book_Primitive_Disjunction_Decoding.book_disj_decode_language",
    "theorem:Bacon_Book_Primitive_Disjunction_Decoding.book_disj_encode_language_iff",
    "theorem:Bacon_Book_Disjunction_Formula_Transport.book_disj_encode_conj",
    "theorem:Bacon_Book_Disjunction_Formula_Transport.book_disj_decode_conj",
    "theorem:Bacon_Book_Disjunction_Formula_Transport.book_disj_decode_tag_application",
    "theorem:Bacon_Book_Disjunction_Binding_Transport.book_disj_encode_subst",
    "theorem:Bacon_Book_Disjunction_Binding_Transport.book_disj_decode_subst",
    "theorem:Bacon_Book_Disjunction_Binding_Transport.book_disj_encode_printed_free_for",
    "theorem:Bacon_Book_Disjunction_Binding_Transport.book_disj_decode_printed_free_for",
    "theorem:Bacon_Book_Disjunction_Binding_Transport.book_disj_encode_named_free_for",
    "theorem:Bacon_Book_Disjunction_Binding_Transport.book_disj_decode_named_free_for",
    "theorem:Bacon_Book_Disjunction_Step_Transport.book_disj_encode_printed_beta_step",
    "theorem:Bacon_Book_Disjunction_Step_Transport.book_disj_decode_printed_beta_step",
    "theorem:Bacon_Book_Disjunction_Step_Transport.book_disj_encode_eta_step",
    "theorem:Bacon_Book_Disjunction_Step_Transport.book_disj_decode_eta_step",
    "theorem:Bacon_Book_Disjunction_Conversion_Transport.book_disj_encode_printed_conversion",
    "theorem:Bacon_Book_Disjunction_Conversion_Transport.book_disj_decode_printed_conversion",
    "theorem:Bacon_Book_Disjunction_Conversion_Transport.book_disj_printed_conversion_iff",
    "theorem:Bacon_Book_Primitive_Disjunction_Axiom_Theory.book_disj_axioms_language",
    "theorem:Bacon_Book_Primitive_Disjunction_Axiom_Theory.book_disj_encoded_premises_language",
    "theorem:Bacon_Book_Primitive_Conjunction_Encoding.book_conj_target_tag_iff",
    "theorem:Bacon_Book_Primitive_Conjunction_Encoding.book_conj_encode_language",
    "theorem:Bacon_Book_Primitive_Conjunction_Decoding.book_conj_decode_language",
    "theorem:Bacon_Book_Primitive_Conjunction_Decoding.book_conj_decode_encode",
    "theorem:Bacon_Book_Primitive_Conjunction_Decoding.book_conj_encode_decode",
    "theorem:Bacon_Book_Primitive_Conjunction_Decoding.book_conj_encode_language_iff",
    "theorem:Bacon_Book_Conjunction_Binding_Transport.book_conj_encode_subst",
    "theorem:Bacon_Book_Conjunction_Binding_Transport.book_conj_decode_subst",
    "theorem:Bacon_Book_Conjunction_Binding_Transport.book_conj_encode_printed_free_for",
    "theorem:Bacon_Book_Conjunction_Binding_Transport.book_conj_decode_printed_free_for",
    "theorem:Bacon_Book_Conjunction_Step_Transport.book_conj_encode_printed_beta",
    "theorem:Bacon_Book_Conjunction_Step_Transport.book_conj_decode_printed_beta",
    "theorem:Bacon_Book_Conjunction_Step_Transport.book_conj_encode_eta",
    "theorem:Bacon_Book_Conjunction_Step_Transport.book_conj_decode_eta",
    "theorem:Bacon_Book_Conjunction_Step_Transport.book_conj_encode_printed_beta_step",
    "theorem:Bacon_Book_Conjunction_Step_Transport.book_conj_decode_printed_beta_step",
    "theorem:Bacon_Book_Conjunction_Step_Transport.book_conj_encode_eta_step",
    "theorem:Bacon_Book_Conjunction_Step_Transport.book_conj_decode_eta_step",
    "theorem:Bacon_Book_Conjunction_Conversion_Transport.book_conj_encode_printed_conversion",
    "theorem:Bacon_Book_Conjunction_Conversion_Transport.book_conj_decode_printed_conversion",
    "theorem:Bacon_Book_Conjunction_Conversion_Transport.book_conj_printed_conversion_iff",
    "theorem:Bacon_Book_Conjunction_Raw_Conversion_Transport.book_conj_encode_raw_conversion",
    "theorem:Bacon_Book_Conjunction_Raw_Conversion_Transport.book_conj_decode_raw_conversion",
    "theorem:Bacon_Book_Primitive_Conjunction_Axiom_Theory.book_conj_axioms_language",
    "theorem:Bacon_Book_Conjunction_Constant_Substitution_Transport.book_conj_encode_named_free_for",
    "theorem:Bacon_Book_Conjunction_Constant_Substitution_Transport.book_conj_encode_const_subst",
    "theorem:Bacon_Book_Conjunction_Constant_Substitution_Transport.book_conj_encode_const_free_for",
    "theorem:Bacon_Book_Conjunction_Background_Retraction.book_conj_background_retract_axiom",
    "theorem:Bacon_Book_Conjunction_Background_Retraction.book_conj_background_retract_subset",
    "theorem:Bacon_Book_Conjunction_Theory_Clauses.book_conj_imp_operands",
)
BOOK_CONJUNCTION_INDEPENDENT_PROOF_ROOTS = (
    "theorem:Bacon_Book_Primitive_Disjunction_Theory_Derivation.book_disj_theory_UI_language",
    "theorem:Bacon_Book_Primitive_Disjunction_Theory_Derivation.book_disj_theory_derivable_language",
    "theorem:Bacon_Book_Primitive_Disjunction_Theory_Derivation.book_disj_theory_derivable_mono",
    "theorem:Bacon_Book_Primitive_Conjunction_Theory_Derivation.book_conj_theory_UI_language",
    "theorem:Bacon_Book_Primitive_Conjunction_Theory_Derivation.book_conj_theory_derivable_language",
    "theorem:Bacon_Book_Primitive_Conjunction_Theory_Derivation.book_conj_theory_derivable_mono",
    "theorem:Bacon_Book_Conjunction_Theory.book_conj_theory_derivable_cut",
    "theorem:Bacon_Book_Conjunction_Theory.book_conj_derivable_consequences_form_theory",
    "theorem:Bacon_Book_Conjunction_Theory.book_conj_theory_derivable_iff_all_theories",
    "theorem:Bacon_Book_Conjunction_Theory_Clauses.book_conj_higher_order_theory_iff_rules",
)
BOOK_CONJUNCTION_PROOF_BRIDGE_ROOTS = (
    "theorem:Bacon_Book_Disjunction_Background_Decoding.book_disj_decode_axiom",
    "theorem:Bacon_Book_Disjunction_Background_Decoding.book_disj_decode_background_premise",
    "theorem:Bacon_Book_Disjunction_Proof_Encoding.book_disj_theory_encode",
    "theorem:Bacon_Book_Disjunction_Proof_Decoding.book_disj_decode_conjunction_proof",
    "theorem:Bacon_Book_Disjunction_Proof_Correspondence.book_disj_theory_decode",
    "theorem:Bacon_Book_Disjunction_Proof_Correspondence.book_disj_theory_encoding_iff",
    "theorem:Bacon_Book_Disjunction_Proof_Correspondence.book_disj_consistency_iff_background",
    "theorem:Bacon_Book_Conjunction_Background_Decoding.book_conj_decode_axiom",
    "theorem:Bacon_Book_Conjunction_Background_Decoding.book_conj_decode_background_premise",
    "theorem:Bacon_Book_Conjunction_Proof_Encoding.book_conj_theory_encode",
    "theorem:Bacon_Book_Conjunction_Proof_Decoding.book_conj_decode_printed_proof",
    "theorem:Bacon_Book_Conjunction_Proof_Correspondence.book_conj_theory_decode",
    "theorem:Bacon_Book_Conjunction_Proof_Correspondence.book_conj_theory_encoding_iff",
    "theorem:Bacon_Book_Conjunction_Proof_Correspondence.book_conj_consistency_iff_printed_background",
    "theorem:Bacon_Book_Conjunction_Proof_Correspondence.book_conj_consistency_iff_background",
    "theorem:Bacon_Book_Conjunction_Background_Fresh_Constant.book_conj_background_fresh_constant_variable",
    "theorem:Bacon_Book_Conjunction_Variable_Substitution.book_conj_theory_variable_substitution",
    "theorem:Bacon_Book_Conjunction_Constant_Substitution.book_conj_theory_constant_substitution",
    "theorem:Bacon_Book_Conjunction_Simultaneous_Substitution_Singleton.book_conj_theory_simult_single",
    "theorem:Bacon_Book_Conjunction_Simultaneous_Substitution.book_conj_theory_simultaneous_substitution",
    "theorem:Bacon_Book_Conjunction_Logic.book_conj_least_theory_is_logic",
    "theorem:Bacon_Book_Conjunction_Logic.book_conj_H_iff_theory",
    "theorem:Bacon_Book_Conjunction_Logic.book_conj_H_language",
)
BOOK_CONJUNCTION_SEMANTIC_TRANSPORT_ROOTS = (
    "theorem:Bacon_Book_Disjunction_Axiom_Truth.book_conjunction_model.book_disjunction_axioms_truth",
    "theorem:Bacon_Book_Disjunction_Background_Truth.book_disj_background_truth_at",
    "theorem:Bacon_Book_Conjunction_Encoding_Environment.book_conj_encoded_full_environment",
    "theorem:Bacon_Book_Conjunction_Decoding_Environment.book_conj_decoded_full_environment",
    "theorem:Bacon_Book_Conjunction_Background_Truth.book_conj_background_truth_at",
    "theorem:Bacon_Book_Conjunction_Background_Truth.book_conj_background_value_exists",
    "theorem:Bacon_Book_Conjunction_Model_From_Background.book_conj_model_from_background_at",
    "theorem:Bacon_Book_Conjunction_Model_From_Background.book_conj_model_from_background",
    "theorem:Bacon_Book_Conjunction_Decoded_Model.book_conj_decoded_minimal_model",
    "theorem:Bacon_Book_Conjunction_Decoded_Model.book_conjunction_model.book_conj_apply_truth",
    "theorem:Bacon_Book_Conjunction_Decoded_Model.book_conjunction_model.book_conj_imp_truth",
    "theorem:Bacon_Book_Conjunction_Decoded_Background_Truth.book_conjunction_model.book_conj_decoded_axiom_valid",
    "theorem:Bacon_Book_Conjunction_Decoded_Background_Truth.book_conjunction_model.book_conj_decoded_background_valid",
)
BOOK_CONJUNCTION_COMPLETENESS_ROOTS = (
    "theorem:Bacon_Book_Conjunction_Model_Existence.book_conj_canonical_model_existence",
    "theorem:Bacon_Book_Conjunction_Theory_Soundness.book_conjunction_model.book_conj_theory_soundness",
    "theorem:Bacon_Book_Conjunction_Countermodel.book_conj_canonical_countermodel",
    "theorem:Bacon_Book_Conjunction_Completeness.book_conj_canonical_soundness",
    "theorem:Bacon_Book_Conjunction_Completeness.book_conj_canonical_completeness",
    "theorem:Bacon_Book_Conjunction_Completeness.book_conj_canonical_strong_completeness",
    "theorem:Bacon_Book_Conjunction_Logic_Completeness.book_conjunction_model.book_conj_H_soundness",
    "theorem:Bacon_Book_Conjunction_Logic_Completeness.book_conj_H_canonical_completeness",
)
BOOK_CONJUNCTION_ROOTS = (
    *BOOK_CONJUNCTION_SYNTAX_ROOTS,
    *BOOK_CONJUNCTION_INDEPENDENT_PROOF_ROOTS,
    *BOOK_CONJUNCTION_PROOF_BRIDGE_ROOTS,
    *BOOK_CONJUNCTION_SEMANTIC_TRANSPORT_ROOTS,
    *BOOK_CONJUNCTION_COMPLETENESS_ROOTS,
)
BOOK_CONJUNCTION_PROOF_PREDICATES = BOOK_CONVERSION_NATIVE_PROOF_PREDICATES | {
    "book_printed_theory_derivable", "book_printed_theory_consistent",
    "book_conj_theory_derivable", "book_conj_theory_consistent",
    "book_conj_higher_order_theory", "book_conj_higher_order_logic", "book_conj_H",
    "book_conj_theory_rules",
    "book_disj_theory_derivable", "book_disj_theory_consistent",
}
BOOK_CONJUNCTION_MODEL_PREDICATES = BOOK_CONVERSION_ENVIRONMENT_PREDICATES | {
    "book_full_minimal_model", "book_full_minimal_model_axioms",
    "book_conjunction_model", "book_conjunction_model_axioms",
    "book_general_environment_conditions", "book_general_environment_conditions_axioms",
    "book_general_interpretation", "book_general_interpretation_axioms",
    "book_formula_valid", "book_canonical_consequence", "book_conj_canonical_consequence",
}
BOOK_CONJUNCTION_FOREIGN_PREDICATES = (
    BOOK_CONVERSION_FOREIGN_PREDICATES
    - {"book_full_minimal_model", "book_full_minimal_model_axioms", "book_formula_valid"}
) | {
    "H_signature_proves", "H_set_derivable", "H_consistent",
    "pH_set_derivable", "pH_consistent", "paper_global_consistent", "paper_named_consistent",
    "C_proves", "CE_proves", "CEV_proves", "HE_proves", "HLE_proves",
    "applicative_structure", "applicative_structure_axioms",
    "classicist_structure", "classicist_structure_axioms",
    "propositional_equivalence_structure", "propositional_equivalence_structure_axioms",
    "vector_equivalence_structure", "vector_equivalence_structure_axioms",
}


def book_conjunction_forbidden(root, model_predicates=()):
    """Keep syntax, independent rules, fixed-background proofs and models apart.

    Additional *_model / *_model_axioms constants discovered in the graph are
    excluded from pure layers as well. Semantic layers permit book model
    interfaces, but not older H/Classicism/BBK model families. A model predicate
    in a constructed conclusion is legitimate; distinguishing that conclusion
    from an assumed model still requires inspecting the theorem statement.
    """
    if root not in BOOK_CONJUNCTION_ROOTS:
        return set()
    discovered_models = set(model_predicates)
    forbidden = BOOK_CONJUNCTION_FOREIGN_PREDICATES | {
        name for name in discovered_models if not name.startswith("book_")
    }
    if root in BOOK_CONJUNCTION_SYNTAX_ROOTS or root in BOOK_CONJUNCTION_SEMANTIC_TRANSPORT_ROOTS:
        forbidden |= BOOK_CONJUNCTION_PROOF_PREDICATES
    if root in BOOK_CONJUNCTION_INDEPENDENT_PROOF_ROOTS:
        allowed_native = (
            {"book_disj_theory_derivable"}
            if root.startswith("theorem:Bacon_Book_Primitive_Disjunction_Theory_Derivation.")
            else {"book_conj_theory_derivable", "book_conj_higher_order_theory", "book_conj_theory_rules"}
        )
        forbidden |= BOOK_CONJUNCTION_PROOF_PREDICATES - allowed_native
    if root in (
        BOOK_CONJUNCTION_SYNTAX_ROOTS
        + BOOK_CONJUNCTION_INDEPENDENT_PROOF_ROOTS
        + BOOK_CONJUNCTION_PROOF_BRIDGE_ROOTS
    ):
        forbidden |= BOOK_CONJUNCTION_MODEL_PREDICATES | discovered_models
    return forbidden


BOOK_THEORY_ROOTS = (
    "theorem:Bacon_Book_Printed_Completeness.book_full_minimal_model.book_printed_theory_soundness",
    "theorem:Bacon_Book_Printed_Completeness.book_printed_canonical_model_existence",
    "theorem:Bacon_Book_Printed_Completeness.book_printed_canonical_strong_completeness",
    "theorem:Bacon_Book_Printed_Completeness.book_printed_canonical_countermodel",
    "theorem:Bacon_Book_Canonical_Model_Existence.book_henkin_original_model_exists",
    "theorem:Bacon_Book_Canonical_Model_Existence.book_canonical_model_existence",
    "theorem:Bacon_Book_Canonical_Countermodel.book_canonical_countermodel_with_assignment",
    "theorem:Bacon_Book_Canonical_Countermodel.book_canonical_countermodel",
    "theorem:Bacon_Book_Canonical_Completeness.book_canonical_soundness",
    "theorem:Bacon_Book_Canonical_Completeness.book_canonical_strong_completeness",
    "theorem:Bacon_Book_Canonical_Completeness.book_H_canonical_completeness",
    "theorem:Bacon_Book_Conversion_Model.book_henkin_conversion_model",
    "theorem:Bacon_Book_Conversion_Truth_Projection.book_conversion_truth_projection",
    "theorem:Bacon_Book_Conversion_Truth_Projection.book_henkin_conversion_closed_valid_iff",
    "theorem:Bacon_Book_Conversion_Expanded_Model_Existence.book_henkin_conversion_original_valid",
    "theorem:Bacon_Book_Conversion_Expanded_Model_Existence.book_henkin_expanded_model_exists",
    "theorem:Bacon_Book_H_Soundness.book_full_minimal_model.book_H_soundness",
    *BOOK_THEORY_PURE_ROOTS,
    "theorem:Bacon_Book_Theory_Axiom_Soundness.book_full_minimal_model.book_PC3_valid",
    "theorem:Bacon_Book_Theory_Axiom_Soundness.book_full_minimal_model.book_UI_valid",
    "theorem:Bacon_Book_Minimal_Validity.book_full_minimal_model.book_Gen_valid",
    "theorem:Bacon_Book_Theory_Soundness.book_full_minimal_model.book_theory_soundness",
    "theorem:Bacon_Book_Theory_Soundness.book_full_minimal_model.book_model_truths_form_theory",
    "theorem:Bacon_Book_Model_Class_Theory.book_theorem_15_1_full_minimal",
    "theorem:Bacon_Book_Open_Deduction_Boundary.book_full_minimal_model.book_open_deduction_not_derivable",
    "theorem:Bacon_Book_Open_Deduction_Boundary.book_full_minimal_model.book_unrestricted_open_deduction_counterexample",
)
# Exact semantic groundwork must not borrow H/C derivations. Raw assignment,
# homomorphism and action laws also exclude all logical-model predicates;
# endpoint-aware morphisms permit precisely their named BBK model conditions.
RELATIONAL_CONSTANT_MAP_RAW_ROOTS = (
    "theorem:Bacon_Source_Relational_Constant_Map.paper_R_constant_map_type",
    "theorem:Bacon_Source_Relational_Constant_Map.paper_R_constant_map_fv",
    "theorem:Bacon_Source_Relational_Constant_Map_Binding.paper_R_constant_map_subst",
    "theorem:Bacon_Source_Relational_Constant_Map_Binding.paper_R_constant_map_free_for",
    "theorem:Bacon_Source_Relational_Constant_Map_Binding.paper_R_constant_map_raw_conversion",
)
RELATIONAL_HENKIN_SYNTAX_ROOTS = (
    "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_full_premises_closed",
    "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_finite_premises_stage_bound",
    "theorem:Bacon_Source_Relational_Henkin_Witness_Coverage.paper_R_henkin_full_witness_axiom",
    "theorem:Bacon_Source_Relational_Henkin_Name_Stages.paper_R_henkin_signature_original_iff",
    "theorem:Bacon_Source_Relational_Henkin_Name_Stages.paper_R_henkin_signature_witness_fresh",
    "theorem:Bacon_Source_Relational_Henkin_Stage_Signature.paper_R_henkin_stage_typed_names_inj_on",
    "theorem:Bacon_Source_Relational_Henkin_Stage_Signature.paper_R_henkin_signature_family",
    "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_mono",
    "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_closed",
    "theorem:Bacon_Source_Relational_Henkin_Full_Signature.paper_R_henkin_full_language_eventually",
    "theorem:Bacon_Source_Relational_Henkin_Full_Signature.paper_R_henkin_full_closed_predicate_witness",
)
RELATIONAL_HENKIN_PROOF_ROOTS = (
    "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_declared_constant",
    "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_identity_domain_nonempty",
    "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_stage_consistent_full_signature",
    "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_full_premises_consistent",
    "theorem:Bacon_Source_Relational_Closed_Witness_Completeness.paper_R_closed_witness_complete_from_conditionals",
    "theorem:Bacon_Source_Relational_Closed_Henkin_Theory.paper_R_closed_maximal_Henkin",
    "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists",
    "theorem:Bacon_Source_Relational_Local_Constant_Map.paper_R_named_derivable_constant_map",
    "theorem:Bacon_Source_Relational_Local_Constant_Map.paper_R_named_derivable_injective_constant_map_iff",
    "theorem:Bacon_Source_Relational_Constant_Map_Consistency.paper_R_named_consistent_injective_constant_map_iff",
    "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_original_consistent",
    "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_premises_consistent",
)
RELATIONAL_HENKIN_DATA_CONSTANTS = {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises"}
RELATIONAL_HENKIN_DATA_ROOT_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Henkin_Countable_Signature.paper_R_henkin_full_names_countable": {"paper_R_henkin_signature", "paper_R_henkin_full_signature", "ROriginal", "RWitness"},
    "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_full_premises_closed": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises"},
    "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_finite_premises_stage_bound": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_premises"},
    "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_stage_consistent_full_signature": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature"},
    "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_full_premises_consistent": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises"},
    "theorem:Bacon_Source_Relational_Henkin_Witness_Coverage.paper_R_henkin_full_witness_axiom": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises"},
    "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises"},
    "theorem:Bacon_Source_Relational_Henkin_Name_Stages.paper_R_henkin_signature_original_iff": {"paper_R_henkin_signature", "ROriginal", "RWitness"},
    "theorem:Bacon_Source_Relational_Henkin_Name_Stages.paper_R_henkin_signature_witness_fresh": {"paper_R_henkin_signature", "ROriginal", "RWitness"},
    "theorem:Bacon_Source_Relational_Henkin_Stage_Signature.paper_R_henkin_stage_typed_names_inj_on": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "ROriginal", "RWitness"},
    "theorem:Bacon_Source_Relational_Henkin_Stage_Signature.paper_R_henkin_signature_family": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "ROriginal", "RWitness"},
    "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_mono": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness"},
    "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_closed": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness"},
    "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_original_consistent": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness"},
    "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_premises_consistent": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness"},
    "theorem:Bacon_Source_Relational_Henkin_Full_Signature.paper_R_henkin_full_language_eventually": {"paper_R_henkin_signature", "paper_R_henkin_full_signature", "ROriginal", "RWitness"},
    "theorem:Bacon_Source_Relational_Henkin_Full_Signature.paper_R_henkin_full_closed_predicate_witness": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_full_signature", "ROriginal", "RWitness"},
}


RELATIONAL_CLOSED_HENKIN_PREDICATES = {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"}
RELATIONAL_CLOSED_HENKIN_ROOT_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Henkin_Existential_Membership.paper_R_closed_Henkin_exists_member": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Universal_Membership.paper_R_closed_Henkin_forall_member": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_exists_class": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_forall_class": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_forall_truth": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_exists_truth": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Model.paper_R_identity_bbk_model": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_neg_truth": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_conj_truth": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_disj_truth": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_valuation_identity": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_denote_identity_truth": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_not_member": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_and_member": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_or_member": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_not": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_and": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_or": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_class": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_rep": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_declared_constant": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_identity_domain_nonempty": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Closed_Witness_Completeness.paper_R_closed_witness_complete_from_conditionals": {"paper_R_closed_constant_witness_complete"},
    "theorem:Bacon_Source_Relational_Closed_Henkin_Theory.paper_R_closed_maximal_Henkin": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
}


def relational_closed_henkin_forbidden(root):
    return RELATIONAL_CLOSED_HENKIN_PREDICATES - RELATIONAL_CLOSED_HENKIN_ROOT_ALLOWLIST.get(root, set())


def relational_henkin_data_forbidden(root):
    return RELATIONAL_HENKIN_DATA_CONSTANTS - RELATIONAL_HENKIN_DATA_ROOT_ALLOWLIST.get(root, set())


RELATIONAL_TERM_ENV_RAW_ROOTS = (
    "theorem:Bacon_Source_Relational_Environment_Update_Syntax.paper_R_environment_subst_update_closed",
    "theorem:Bacon_Source_Relational_Environment_Beta_Syntax.paper_R_environment_subst_beta_commute",
    "theorem:Bacon_Source_Relational_Environment_Contractions.paper_R_environment_subst_beta_contract",
    "theorem:Bacon_Source_Relational_Environment_Contractions.paper_R_environment_subst_eta_contract",
    "theorem:Bacon_Source_Relational_Environment_Conversion.paper_R_environment_subst_raw_conversion",
    "theorem:Bacon_Source_Relational_Term_Type.paper_R_term_type_eq",
    "theorem:Bacon_Source_Relational_Environment_Substitution.paper_R_environment_subst_locality",
    "theorem:Bacon_Source_Relational_Environment_Substitution.paper_R_environment_subst_fv",
    "theorem:Bacon_Source_Relational_Environment_Substitution_Typing.paper_R_environment_subst_type",
    "theorem:Bacon_Source_Relational_Representative_Assignments.paper_R_representative_assignment_domain",
    "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_locality",
)
RELATIONAL_TERM_ENV_PROOF_ROOTS = (
    "theorem:Bacon_Source_Relational_Environment_Finite_Identity.paper_R_environment_subst_assignment_identity",
    "theorem:Bacon_Source_Relational_Arbitrary_Representatives.paper_R_identity_denote_arbitrary_representatives",
    "theorem:Bacon_Source_Relational_Environment_Update_Identity.paper_R_environment_subst_update_identity",
    "theorem:Bacon_Source_Relational_Quantifier_Duality.paper_R_named_H_quantifier_duality",
    "theorem:Bacon_Source_Relational_Henkin_Existential_Membership.paper_R_closed_Henkin_exists_member",
    "theorem:Bacon_Source_Relational_Henkin_Universal_Membership.paper_R_closed_Henkin_forall_member",
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_exists_class",
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_forall_class",
    "theorem:Bacon_Source_Relational_Identity_Fresh_Application.paper_R_identity_denote_fresh_application",
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_forall_truth",
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_exists_truth",
    "theorem:Bacon_Source_Relational_Identity_Conversion.paper_R_identity_denote_beta_eta",
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_neg_truth",
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_conj_truth",
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_disj_truth",
    "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_valuation_identity",
    "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_denote_identity_truth",
    "theorem:Bacon_Source_Relational_Identity_Application_Congruence.paper_R_identity_denote_application_cong",
    "theorem:Bacon_Source_Relational_Boolean_PC.paper_R_named_H_PC_template",
    "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_not_member",
    "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_and_member",
    "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_or_member",
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_not",
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_and",
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_or",
    "theorem:Bacon_Source_Relational_Representative_Assignments.paper_R_representative_assignment_typed",
    "theorem:Bacon_Source_Relational_Environment_Substitution_Typing.paper_R_representative_substitution_closed_terms",
    "theorem:Bacon_Source_Relational_Propositional_Identity_Derivations.paper_R_named_derivable_propositional_identity",
    "theorem:Bacon_Source_Relational_Propositional_Identity_Derivations.paper_R_closed_propositional_identity_membership",
    "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_class",
    "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_rep",
    "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_type",
    "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_var",
    "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_App",
)
RELATIONAL_TERM_ENV_CONSTANTS = {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote", "paper_R_constant_pullback_denote"}
RELATIONAL_TERM_ENV_ROOT_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Environment_Finite_Identity.paper_R_environment_subst_assignment_identity": {"paper_R_environment_subst", "paper_R_closed_term_assignment"},
    "theorem:Bacon_Source_Relational_Arbitrary_Representatives.paper_R_identity_denote_arbitrary_representatives": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Environment_Update_Syntax.paper_R_environment_subst_update_closed": {"paper_R_environment_subst"},
    "theorem:Bacon_Source_Relational_Environment_Update_Identity.paper_R_environment_subst_update_identity": {"paper_R_environment_subst", "paper_R_closed_term_assignment"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_exists_class": {"paper_R_identity_valuation"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_forall_class": {"paper_R_identity_valuation"},
    "theorem:Bacon_Source_Relational_Identity_Fresh_Application.paper_R_identity_denote_fresh_application": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_forall_truth": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_exists_truth": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Identity_Model.paper_R_identity_bbk_model": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_BBK_Constant_Pullback.paper_R_bbk_constant_pullback": {"paper_R_constant_pullback_denote"},
    "theorem:Bacon_Source_Relational_Environment_Beta_Syntax.paper_R_environment_subst_beta_commute": {"paper_R_environment_subst"},
    "theorem:Bacon_Source_Relational_Environment_Contractions.paper_R_environment_subst_beta_contract": {"paper_R_environment_subst"},
    "theorem:Bacon_Source_Relational_Environment_Contractions.paper_R_environment_subst_eta_contract": {"paper_R_environment_subst"},
    "theorem:Bacon_Source_Relational_Environment_Conversion.paper_R_environment_subst_raw_conversion": {"paper_R_environment_subst", "paper_R_closed_term_assignment"},
    "theorem:Bacon_Source_Relational_Identity_Conversion.paper_R_identity_denote_beta_eta": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_neg_truth": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_conj_truth": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_disj_truth": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_valuation_identity": {"paper_R_identity_valuation"},
    "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_denote_identity_truth": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Identity_Application_Congruence.paper_R_identity_denote_application_cong": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_not": {"paper_R_identity_valuation"},
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_and": {"paper_R_identity_valuation"},
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_or": {"paper_R_identity_valuation"},
    "theorem:Bacon_Source_Relational_Term_Type.paper_R_term_type_eq": {"paper_R_term_type"},
    "theorem:Bacon_Source_Relational_Environment_Substitution.paper_R_environment_subst_locality": {"paper_R_environment_subst"},
    "theorem:Bacon_Source_Relational_Environment_Substitution.paper_R_environment_subst_fv": {"paper_R_environment_subst"},
    "theorem:Bacon_Source_Relational_Environment_Substitution_Typing.paper_R_environment_subst_type": {"paper_R_environment_subst"},
    "theorem:Bacon_Source_Relational_Representative_Assignments.paper_R_representative_assignment_domain": {"paper_R_representative_assignment"},
    "theorem:Bacon_Source_Relational_Representative_Assignments.paper_R_representative_assignment_typed": {"paper_R_representative_assignment", "paper_R_closed_term_assignment"},
    "theorem:Bacon_Source_Relational_Environment_Substitution_Typing.paper_R_representative_substitution_closed_terms": {"paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment"},
    "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_class": {"paper_R_identity_valuation"},
    "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_rep": {"paper_R_identity_valuation"},
    "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_type": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_var": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_locality": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_identity_denote"},
    "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_App": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_denote"},
}


def relational_term_env_forbidden(root):
    return RELATIONAL_TERM_ENV_CONSTANTS - RELATIONAL_TERM_ENV_ROOT_ALLOWLIST.get(root, set())


RELATIONAL_COUNTING_RAW_ROOTS = (
    "theorem:Bacon_Source_Relational_Admitted_Terms_Countable.paper_R_admitted_terms_countable",
    "theorem:Bacon_Source_Relational_Henkin_Countable_Signature.paper_R_henkin_full_names_countable",
    "theorem:Bacon_Source_Relational_Identity_Countable_Domains.paper_R_identity_domains_countable",
)
RELATIONAL_COUNTING_ROOTS = RELATIONAL_COUNTING_RAW_ROOTS + (
    "theorem:Bacon_Source_Relational_Nat_Model_Existence.paper_R_BBK_nat_model_existence",
    "theorem:Bacon_Source_Relational_Nat_Countermodel.paper_R_nat_closed_countermodel",
    "theorem:Bacon_Source_Relational_Nat_Completeness.paper_R_nat_closed_strong_completeness",
    "theorem:Bacon_Source_Relational_Countable_Model_Existence.paper_R_BBK_countable_union_model_existence",
)
RELATIONAL_REP_CHOICE_CONSTANTS = {"paper_R_environment_paste", "paper_R_represents_class_assignment"}
RELATIONAL_REP_CHOICE_ROOT_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Environment_Finite_Identity.paper_R_environment_subst_assignment_identity": {"paper_R_environment_paste"},
    "theorem:Bacon_Source_Relational_Arbitrary_Representatives.paper_R_identity_denote_arbitrary_representatives": {"paper_R_environment_paste", "paper_R_represents_class_assignment"},
}
RELATIONAL_COUNT_CODE_CONSTANTS = {"paper_R_logical_count_tree", "paper_R_named_count_tree"}
RELATIONAL_COUNT_CODE_ROOT_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Nat_Model_Existence.paper_R_BBK_nat_model_existence": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
    "theorem:Bacon_Source_Relational_Nat_Countermodel.paper_R_nat_closed_countermodel": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
    "theorem:Bacon_Source_Relational_Nat_Completeness.paper_R_nat_closed_strong_completeness": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
    "theorem:Bacon_Source_Relational_Admitted_Terms_Countable.paper_R_admitted_terms_countable": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
    "theorem:Bacon_Source_Relational_Henkin_Countable_Signature.paper_R_henkin_full_names_countable": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
    "theorem:Bacon_Source_Relational_Identity_Countable_Domains.paper_R_identity_domains_countable": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
    "theorem:Bacon_Source_Relational_Countable_Model_Existence.paper_R_BBK_countable_union_model_existence": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
}
# Only these constants with the pHct_ prefix belong to the reused generic
# finite-tree/type-label apparatus. No imported theory is exempted.
RELATIONAL_COUNT_GENERIC_PHCT_CONSTANTS = {"pHct_Atom", "pHct_Unary", "pHct_Binary", "pHct_type_code"}


def relational_rep_count_data_forbidden(root):
    return ((RELATIONAL_REP_CHOICE_CONSTANTS - RELATIONAL_REP_CHOICE_ROOT_ALLOWLIST.get(root, set()))
            | (RELATIONAL_COUNT_CODE_CONSTANTS - RELATIONAL_COUNT_CODE_ROOT_ALLOWLIST.get(root, set())))


def relational_counting_coding_forbidden(root, constant_names):
    if root not in RELATIONAL_COUNTING_ROOTS:
        return set()
    nongeneric = {name for name in constant_names
                  if name.startswith("pHct_") and name not in RELATIONAL_COUNT_GENERIC_PHCT_CONSTANTS}
    return nongeneric | {"pH_closed_Henkin", "pH_countable_closed_Henkin",
                         "pHc_domain", "pHc_class", "pHc_rep", "pHc_type_of"}


RELATIONAL_RECODING_RAW_ROOTS = (
    "theorem:Bacon_Source_Relational_Recoding_Assignments.paper_R_recode_inverse_assignment_typed",
    "theorem:Bacon_Source_Relational_Recoding_Assignments.paper_R_recode_assignment_inverse_left",
    "theorem:Bacon_Source_Relational_Recoding_Assignments.paper_R_recode_assignment_inverse_right",
)
RELATIONAL_RECODING_MODEL_ROOTS = (
    "theorem:Bacon_Source_Relational_Recoding_Structure.paper_R_bbk_model.paper_R_recode_denote_application",
    "theorem:Bacon_Source_Relational_Recoding_Truth.paper_R_bbk_model.paper_R_recode_identity_truth",
    "theorem:Bacon_Source_Relational_Recoding_Quantifiers.paper_R_bbk_model.paper_R_recode_forall_truth",
    "theorem:Bacon_Source_Relational_Recoding_Quantifiers.paper_R_bbk_model.paper_R_recode_exists_truth",
    "theorem:Bacon_Source_Relational_Recoding_Model.paper_R_bbk_model.paper_R_recode_model",
    "theorem:Bacon_Source_Relational_Recoding_Validity.paper_R_bbk_model.paper_R_recode_valid_iff",
)
RELATIONAL_RECODING_DATA_CONSTANTS = {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote", "paper_R_recode_valuation"}
RELATIONAL_RECODING_DATA_ROOT_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Recoding_Assignments.paper_R_recode_inverse_assignment_typed": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse"},
    "theorem:Bacon_Source_Relational_Recoding_Assignments.paper_R_recode_assignment_inverse_left": {"paper_R_recode_assignment", "paper_R_recode_inverse"},
    "theorem:Bacon_Source_Relational_Recoding_Assignments.paper_R_recode_assignment_inverse_right": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse"},
    "theorem:Bacon_Source_Relational_Recoding_Structure.paper_R_bbk_model.paper_R_recode_denote_application": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote"},
    "theorem:Bacon_Source_Relational_Recoding_Truth.paper_R_bbk_model.paper_R_recode_identity_truth": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote", "paper_R_recode_valuation"},
    "theorem:Bacon_Source_Relational_Recoding_Quantifiers.paper_R_bbk_model.paper_R_recode_forall_truth": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote", "paper_R_recode_valuation"},
    "theorem:Bacon_Source_Relational_Recoding_Quantifiers.paper_R_bbk_model.paper_R_recode_exists_truth": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote", "paper_R_recode_valuation"},
    "theorem:Bacon_Source_Relational_Recoding_Model.paper_R_bbk_model.paper_R_recode_model": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote", "paper_R_recode_valuation"},
    "theorem:Bacon_Source_Relational_Recoding_Validity.paper_R_bbk_model.paper_R_recode_valid_iff": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote", "paper_R_recode_valuation"},
}


def relational_recoding_data_forbidden(root):
    return RELATIONAL_RECODING_DATA_CONSTANTS - RELATIONAL_RECODING_DATA_ROOT_ALLOWLIST.get(root, set())


# Pure cardinal syntax uses its own finite list/type/logical codes. No
# pHct helper, canonical F coding, or theoremhood is needed for these bounds.
RELATIONAL_CARDINAL_RAW_ROOTS = (
    "theorem:Bacon_Source_Relational_Admitted_Syntax_Cardinal.paper_R_admitted_syntax_cardinal_bound",
    "theorem:Bacon_Source_Relational_Henkin_Cardinal_Signature.paper_R_henkin_full_names_cardinal_bound",
    "theorem:Bacon_Source_Relational_Identity_Cardinal_Domains.paper_R_identity_domains_cardinal_bound",
)
RELATIONAL_CARDINAL_MODEL_ROOT = "theorem:Bacon_Source_Relational_Bounded_Model_Existence.paper_R_BBK_bounded_model_existence"
RELATIONAL_CARDINAL_CODE_CONSTANTS = {"paper_R_finite_syntax_code", "paper_R_logical_nat_code", "paper_R_type_nat_code"}
RELATIONAL_CARDINAL_AUX_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Admitted_Syntax_Cardinal.paper_R_admitted_syntax_cardinal_bound": set(),
    "theorem:Bacon_Source_Relational_Henkin_Cardinal_Signature.paper_R_henkin_full_names_cardinal_bound": {"ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_signature"},
    "theorem:Bacon_Source_Relational_Identity_Cardinal_Domains.paper_R_identity_domains_cardinal_bound": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_term_type"},
}

# The first endpoint is raw beta syntax; the second uses local native H.
# Only the last two may use the p.12 C predicate, never Equivalence.
RELATIONAL_C_PREPARATION_ROOTS = (
    "theorem:Bacon_Source_Relational_Vector_Proof_Syntax.paper_R_named_lam_vec_self_beta",
    "theorem:Bacon_Source_Relational_Vector_Identity_Recovery.paper_R_named_identity_from_lam_vec",
    "theorem:Bacon_Source_Relational_Closed_LE_Generators.paper_R_local_H_in_classicism",
    "theorem:Bacon_Source_Relational_Closed_LE_Generators.paper_R_classicism_LE_closed_generator",
)
RELATIONAL_C_PREPARATION_C_ROOTS = RELATIONAL_C_PREPARATION_ROOTS[2:]


# Appendix A.2 base cases only: no MP induction, Equivalence rule,
# open abstraction congruence, model, consistency or Henkin premise.
RELATIONAL_A2_BASE_ROOTS = (
    "theorem:Bacon_Source_Relational_Classicism_A2_H.paper_R_classicism_A2_H",
    "theorem:Bacon_Source_Relational_Closed_Identity_Vector.paper_R_closed_identity_vector_transport",
    "theorem:Bacon_Source_Relational_Classicism_A2_Closed_Identity.paper_R_classicism_A2_closed_identity",
)
RELATIONAL_A2_BASE_C_ROOTS = (
    RELATIONAL_A2_BASE_ROOTS[0], RELATIONAL_A2_BASE_ROOTS[2],
)
RELATIONAL_A2_TOP_CONSTANTS = {"paper_R_named_top"}
RELATIONAL_A2_BASE_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Classicism_A2_H.paper_R_classicism_A2_H": {"paper_R_named_top"},
    "theorem:Bacon_Source_Relational_Closed_Identity_Vector.paper_R_closed_identity_vector_transport": {"paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst"},
    "theorem:Bacon_Source_Relational_Classicism_A2_Closed_Identity.paper_R_classicism_A2_closed_identity": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst"},
}


# Native A.2 MP/local/LE induction, H-only universal laws, and finite
# naming charts are separate proof levels. Gen/Inst of full A.2 remain outside.
RELATIONAL_A2_CONTINUATION_ROOTS = (
    "theorem:Bacon_Source_Relational_Conversion_Congruence.paper_R_raw_beta_eta_lam_vec",
    "theorem:Bacon_Source_Relational_Classicism_A2_MP.paper_R_classicism_A2_MP",
    "theorem:Bacon_Source_Relational_Classicism_A2_Local.paper_R_classicism_A2_local_H",
    "theorem:Bacon_Source_Relational_Classicism_A2_LE.paper_R_classicism_A2_LE",
    "theorem:Bacon_Source_Relational_Universal_Proof_Basics.paper_R_named_H_all_top",
    "theorem:Bacon_Source_Relational_Forall_Disjunction_Proof.paper_R_named_H_forall_or_distribution",
    "theorem:Bacon_Source_Relational_Naming_Charts.paper_R_naming_chart_exists",
    "theorem:Bacon_Source_Relational_Naming_Charts.paper_R_naming_chart_for_term",
)
RELATIONAL_A2_CONTINUATION_C_ROOTS = RELATIONAL_A2_CONTINUATION_ROOTS[1:4]
RELATIONAL_A2_CONTINUATION_H_ROOTS = RELATIONAL_A2_CONTINUATION_ROOTS[4:6]
RELATIONAL_NAMING_DATA_CONSTANTS = {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart"}
RELATIONAL_A2_CONTINUATION_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Conversion_Congruence.paper_R_raw_beta_eta_lam_vec": set(),
    "theorem:Bacon_Source_Relational_Classicism_A2_MP.paper_R_classicism_A2_MP": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste"},
    "theorem:Bacon_Source_Relational_Classicism_A2_Local.paper_R_classicism_A2_local_H": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste"},
    "theorem:Bacon_Source_Relational_Classicism_A2_LE.paper_R_classicism_A2_LE": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste"},
    "theorem:Bacon_Source_Relational_Universal_Proof_Basics.paper_R_named_H_all_top": {"paper_R_named_top"},
    "theorem:Bacon_Source_Relational_Forall_Disjunction_Proof.paper_R_named_H_forall_or_distribution": set(),
    "theorem:Bacon_Source_Relational_Naming_Charts.paper_R_naming_chart_exists": {"paper_R_naming_chart"},
    "theorem:Bacon_Source_Relational_Naming_Charts.paper_R_naming_chart_for_term": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart"},
}


# The full five-constructor A.2 theorem is a native C proof, not an
# Equivalence-presentation or semantic premise. Naming remains raw finite
# support syntax and partial assignments, with no model or theoremhood.
RELATIONAL_A2_COMPLETE_ROOTS = (
    "theorem:Bacon_Source_Relational_Gen_Distribution_Proof.paper_R_named_H_Gen_distribution",
    "theorem:Bacon_Source_Relational_Inst_Gen_Certificate.paper_R_named_H_Inst_Gen_equivalence",
    "theorem:Bacon_Source_Relational_Classicism_A2.paper_R_classicism_A2",
    "theorem:Bacon_Source_Relational_Naming_Replacement.paper_R_naming_replace_language",
    "theorem:Bacon_Source_Relational_Naming_Replacement.paper_R_naming_replace_chart_fv",
    "theorem:Bacon_Source_Relational_Naming_Assignments.paper_R_naming_override_typed",
    "theorem:Bacon_Source_Relational_Naming_Assignments.paper_R_naming_override_agrees",
    "theorem:Bacon_Source_Relational_Naming_Assignments.paper_R_naming_override_adequate",
)
RELATIONAL_A2_COMPLETE_C_ROOTS = (RELATIONAL_A2_COMPLETE_ROOTS[2],)
RELATIONAL_A2_COMPLETE_H_ROOTS = RELATIONAL_A2_COMPLETE_ROOTS[:2]
RELATIONAL_NAMING_REPLACEMENT_CONSTANTS = {"paper_R_naming_replace", "paper_R_naming_override"}
RELATIONAL_A2_COMPLETE_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Gen_Distribution_Proof.paper_R_named_H_Gen_distribution": set(),
    "theorem:Bacon_Source_Relational_Inst_Gen_Certificate.paper_R_named_H_Inst_Gen_equivalence": set(),
    "theorem:Bacon_Source_Relational_Classicism_A2.paper_R_classicism_A2": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste"},
    "theorem:Bacon_Source_Relational_Naming_Replacement.paper_R_naming_replace_language": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace"},
    "theorem:Bacon_Source_Relational_Naming_Replacement.paper_R_naming_replace_chart_fv": {"paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace"},
    "theorem:Bacon_Source_Relational_Naming_Assignments.paper_R_naming_override_typed": {"paper_R_naming_chart", "paper_R_naming_override"},
    "theorem:Bacon_Source_Relational_Naming_Assignments.paper_R_naming_override_agrees": {"paper_R_naming_chart", "paper_R_naming_override"},
    "theorem:Bacon_Source_Relational_Naming_Assignments.paper_R_naming_override_adequate": {"paper_R_naming_support", "paper_R_naming_replace", "paper_R_naming_override"},
}


# A.3 is proved before the Equivalence-presentation converse. Only
# the final iff may reference that independent recursive judgment.
RELATIONAL_A3_ROOTS = (
    "theorem:Bacon_Source_Relational_Classicism_A3.paper_R_classicism_A3",
    "theorem:Bacon_Source_Relational_Classicism_A3.paper_R_classicism_propositional_equivalence",
    "theorem:Bacon_Source_Relational_Classicism_Equivalence_Iff.paper_R_classicism_equivalence_iff",
)
RELATIONAL_A3_EQUIVALENCE_ROOTS = (RELATIONAL_A3_ROOTS[2],)
RELATIONAL_SUBSTITUTION_MODEL_ROOTS = (
    "theorem:Bacon_Source_Relational_Substitution_Denotation.paper_R_bbk_model.paper_R_substitution_denote",
)
RELATIONAL_A3_SELECTOR_CONSTANTS = {"paper_R_A3_selector", "paper_R_A3_vector_context"}
RELATIONAL_A3_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Classicism_A3.paper_R_classicism_A3": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste", "paper_R_A3_selector", "paper_R_A3_vector_context"},
    "theorem:Bacon_Source_Relational_Classicism_A3.paper_R_classicism_propositional_equivalence": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste", "paper_R_A3_selector", "paper_R_A3_vector_context"},
    "theorem:Bacon_Source_Relational_Classicism_Equivalence_Iff.paper_R_classicism_equivalence_iff": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste", "paper_R_A3_selector", "paper_R_A3_vector_context"},
}


# Derived fresh-variable zeta and one-coordinate semantic chart equality
# have disjoint boundaries: native C/A3 proof versus supplied R model.
RELATIONAL_ZETA_ROOTS = (
    "theorem:Bacon_Source_Relational_Classicism_Zeta.paper_R_classicism_zeta",
)
RELATIONAL_NAMING_COORDINATE_MODEL_ROOTS = (
    "theorem:Bacon_Source_Relational_Naming_Coordinate_Denotation.paper_R_bbk_model.paper_R_naming_chart_coordinate_denote",
)
RELATIONAL_ZETA_COORDINATE_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Classicism_Zeta.paper_R_classicism_zeta": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste", "paper_R_A3_selector", "paper_R_A3_vector_context"},
    "theorem:Bacon_Source_Relational_Naming_Coordinate_Denotation.paper_R_bbk_model.paper_R_naming_chart_coordinate_denote": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override"},
}


# Full finite-chart independence is semantic. Generic Necessitation
# requires an independent H-theory plus PE closure; C supplies both only
# through proved constructors/A3. The six new definitions are isolated
# from every older root, including raw charts and existing C proofs.
RELATIONAL_CHART_NECESSITATION_ROOTS = (
    "theorem:Bacon_Source_Relational_Naming_Chart_Independence.paper_R_bbk_model.paper_R_naming_chart_denote_independent",
    "theorem:Bacon_Source_Relational_Naming_Larger_Support.paper_R_bbk_model.paper_R_naming_larger_support_denote",
    "theorem:Bacon_Source_Relational_Naming_Larger_Support.paper_R_bbk_model.paper_R_naming_chart_denote_locality",
    "theorem:Bacon_Source_Relational_H_Theory_Necessitation.paper_R_H_theory_necessitation",
    "theorem:Bacon_Source_Relational_Classicism_H_Theory.paper_R_classicism_necessitation",
)
RELATIONAL_CHART_MODEL_ROOTS = RELATIONAL_CHART_NECESSITATION_ROOTS[:3]
RELATIONAL_GENERIC_NECESSITATION_ROOTS = (RELATIONAL_CHART_NECESSITATION_ROOTS[3],)
RELATIONAL_C_NECESSITATION_ROOTS = (RELATIONAL_CHART_NECESSITATION_ROOTS[4],)
RELATIONAL_CHART_NECESSITATION_CONSTANTS = {"paper_R_naming_mix", "paper_R_naming_chart_denote", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box"}
RELATIONAL_CHART_NECESSITATION_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Naming_Chart_Independence.paper_R_bbk_model.paper_R_naming_chart_denote_independent": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_mix", "paper_R_naming_chart_denote"},
    "theorem:Bacon_Source_Relational_Naming_Larger_Support.paper_R_bbk_model.paper_R_naming_larger_support_denote": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote"},
    "theorem:Bacon_Source_Relational_Naming_Larger_Support.paper_R_bbk_model.paper_R_naming_chart_denote_locality": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote"},
    "theorem:Bacon_Source_Relational_H_Theory_Necessitation.paper_R_H_theory_necessitation": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box"},
    "theorem:Bacon_Source_Relational_Classicism_H_Theory.paper_R_classicism_necessitation": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box", "paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste", "paper_R_A3_selector", "paper_R_A3_vector_context"},
}


# Export inspection confirms that even the direct empty-support old-term
# equation retains the original R-model locale premise. None of these
# endpoints is a full expanded-model constructor.
RELATIONAL_CHOSEN_NAMING_ROOTS = (
    "theorem:Bacon_Source_Relational_Naming_Interpretation.paper_R_bbk_model.paper_R_naming_denote_type",
    "theorem:Bacon_Source_Relational_Naming_Interpretation.paper_R_bbk_model.paper_R_naming_denote_old",
    "theorem:Bacon_Source_Relational_Naming_Interpretation.paper_R_bbk_model.paper_R_naming_denote_value_constant",
)
RELATIONAL_CHOSEN_NAMING_CONSTANTS = {"paper_R_naming_chosen_chart", "paper_R_naming_denote"}
RELATIONAL_CHOSEN_NAMING_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Naming_Interpretation.paper_R_bbk_model.paper_R_naming_denote_type": {"paper_R_naming_support", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_signature", "paper_R_naming_chart"},
    "theorem:Bacon_Source_Relational_Naming_Interpretation.paper_R_bbk_model.paper_R_naming_denote_old": {"paper_R_naming_support", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote"},
    "theorem:Bacon_Source_Relational_Naming_Interpretation.paper_R_bbk_model.paper_R_naming_denote_value_constant": {"paper_R_naming_support", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_signature", "paper_R_naming_chart"},
}


# Finite heterogeneous charts are pure syntax. The naming structural
# laws use a supplied R model; identity stability uses only an independent
# H-theory with PE, necessitating Ref before introducing the local identity.
RELATIONAL_NAMING_STRUCTURE_STABILITY_ROOTS = (
    "theorem:Bacon_Source_Relational_Naming_Finite_Family.paper_R_naming_family_chart_exists",
    "theorem:Bacon_Source_Relational_Naming_Structure.paper_R_bbk_model.paper_R_naming_denote_locality",
    "theorem:Bacon_Source_Relational_Naming_Structure.paper_R_bbk_model.paper_R_naming_denote_application_cong",
    "theorem:Bacon_Source_Relational_Identity_Stability.paper_R_H_theory_identity_stability",
)
RELATIONAL_NAMING_STRUCTURE_MODEL_ROOTS = RELATIONAL_NAMING_STRUCTURE_STABILITY_ROOTS[1:3]
RELATIONAL_IDENTITY_STABILITY_ROOTS = (RELATIONAL_NAMING_STRUCTURE_STABILITY_ROOTS[3],)
RELATIONAL_NAMING_FAMILY_CONSTANTS = {"paper_R_naming_family_support", "paper_R_naming_family_vars"}
RELATIONAL_NAMING_STRUCTURE_STABILITY_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Naming_Finite_Family.paper_R_naming_family_chart_exists": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_family_support", "paper_R_naming_family_vars"},
    "theorem:Bacon_Source_Relational_Naming_Structure.paper_R_bbk_model.paper_R_naming_denote_locality": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote"},
    "theorem:Bacon_Source_Relational_Naming_Structure.paper_R_bbk_model.paper_R_naming_denote_application_cong": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix", "paper_R_naming_family_support", "paper_R_naming_family_vars"},
    "theorem:Bacon_Source_Relational_Identity_Stability.paper_R_H_theory_identity_stability": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box"},
}


# Naming truth uses only the supplied original R model. The finite
# modal argument is pure native H over an independent PE-closed theory.
# Only the two separating-consistency conclusions combine that proof
# machinery with an R model, validating positive T/Delta, never the negation.
RELATIONAL_NAMING_MODAL_SEPARATION_ROOTS = (
    "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_neg_truth",
    "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_conj_truth",
    "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_disj_truth",
    "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_identity_truth",
    "theorem:Bacon_Source_Relational_Naming_Quantifier_Truth.paper_R_bbk_model.paper_R_naming_forall_truth",
    "theorem:Bacon_Source_Relational_Naming_Quantifier_Truth.paper_R_bbk_model.paper_R_naming_exists_truth",
    "theorem:Bacon_Source_Relational_H_Theory_Normal_K.paper_R_H_theory_normal_K",
    "theorem:Bacon_Source_Relational_H_Theory_Modal_PE.paper_R_H_theory_modal_PE",
    "theorem:Bacon_Source_Relational_H_Theory_Boxed_Consequences.paper_R_H_theory_necessitate_local_consequence",
    "theorem:Bacon_Source_Relational_Separating_Consistency.paper_R_bbk_model.paper_R_separating_negation_consistent",
    "theorem:Bacon_Source_Relational_Separating_Consistency.paper_R_bbk_model.paper_R_identity_diagram_separating_consistent",
)
RELATIONAL_NAMING_TRUTH_MODEL_ROOTS = RELATIONAL_NAMING_MODAL_SEPARATION_ROOTS[:6]
RELATIONAL_MODAL_H_THEORY_ROOTS = RELATIONAL_NAMING_MODAL_SEPARATION_ROOTS[6:9]
RELATIONAL_SEPARATING_MODEL_ROOTS = RELATIONAL_NAMING_MODAL_SEPARATION_ROOTS[9:]
RELATIONAL_IMPLICATION_LIST_CONSTANTS = {"paper_R_imp_list"}
RELATIONAL_NAMING_MODAL_SEPARATION_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_neg_truth": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix"},
    "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_conj_truth": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix"},
    "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_disj_truth": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix"},
    "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_identity_truth": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix"},
    "theorem:Bacon_Source_Relational_Naming_Quantifier_Truth.paper_R_bbk_model.paper_R_naming_forall_truth": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix"},
    "theorem:Bacon_Source_Relational_Naming_Quantifier_Truth.paper_R_bbk_model.paper_R_naming_exists_truth": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix"},
    "theorem:Bacon_Source_Relational_H_Theory_Normal_K.paper_R_H_theory_normal_K": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box"},
    "theorem:Bacon_Source_Relational_H_Theory_Modal_PE.paper_R_H_theory_modal_PE": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box"},
    "theorem:Bacon_Source_Relational_H_Theory_Boxed_Consequences.paper_R_H_theory_necessitate_local_consequence": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box", "paper_R_imp_list"},
    "theorem:Bacon_Source_Relational_Separating_Consistency.paper_R_bbk_model.paper_R_separating_negation_consistent": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box", "paper_R_imp_list", "paper_R_named_consistent"},
    "theorem:Bacon_Source_Relational_Separating_Consistency.paper_R_bbk_model.paper_R_identity_diagram_separating_consistent": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box", "paper_R_imp_list", "paper_R_named_consistent"},
}


# Open-theory existence requires actual global H-theory closure.
# Naming constructs all 14 clauses from only the original R model.
# The positive diagram is defined from true closed equalities, not supplied.
RELATIONAL_CLOSURE_NAMING_DIAGRAM_ROOTS = (
    "theorem:Bacon_Source_Relational_H_Theory_Universal_Closure.paper_R_H_theory_closed_universal_instance",
    "theorem:Bacon_Source_Relational_H_Theory_Model_Existence.paper_R_H_theory_model_existence",
    "theorem:Bacon_Source_Relational_H_Theory_Bounded_Model.paper_R_H_theory_bounded_model_existence",
    "theorem:Bacon_Source_Relational_Naming_Conversion.paper_R_bbk_model.paper_R_naming_denote_conversion",
    "theorem:Bacon_Source_Relational_Naming_Model.paper_R_bbk_model.paper_R_naming_model",
    "theorem:Bacon_Source_Relational_Positive_Diagram.paper_R_bbk_model.paper_R_positive_diagram_valid",
    "theorem:Bacon_Source_Relational_Positive_Diagram_Consistency.paper_R_bbk_model.paper_R_positive_diagram_separating_consistent",
)
RELATIONAL_H_THEORY_MODEL_ROOTS = RELATIONAL_CLOSURE_NAMING_DIAGRAM_ROOTS[1:3]
RELATIONAL_CLOSURE_DIAGRAM_CONSTANTS = {"paper_R_all_vec", "paper_R_positive_diagram", "paper_R_sentence_fragment"}
RELATIONAL_CLOSURE_NAMING_DIAGRAM_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_H_Theory_Universal_Closure.paper_R_H_theory_closed_universal_instance": {"paper_R_H_theory", "paper_R_all_vec", "paper_R_named_top"},
    "theorem:Bacon_Source_Relational_Naming_Conversion.paper_R_bbk_model.paper_R_naming_denote_conversion": {"paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support"},
    "theorem:Bacon_Source_Relational_Naming_Model.paper_R_bbk_model.paper_R_naming_model": {"paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support"},
    "theorem:Bacon_Source_Relational_Positive_Diagram.paper_R_bbk_model.paper_R_positive_diagram_valid": {"paper_R_positive_diagram"},
    "theorem:Bacon_Source_Relational_Positive_Diagram_Consistency.paper_R_bbk_model.paper_R_positive_diagram_separating_consistent": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_imp_list", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_positive_diagram"},
}


# Footnote 73: independent parameter closure, a supplied diagram target,
# and actual target existence are distinct stages. Namespace/record wrappers
# cannot leak into earlier proofs. The final two endpoints construct a model
# AND a denotation-preserving map, not a truth-preserving map.
RELATIONAL_N73_ROOTS = (
    "theorem:Bacon_Source_Relational_Naming_Validity.paper_R_bbk_model.paper_R_naming_valid_iff",
    "theorem:Bacon_Source_Relational_H_Theory_Closed_Extension_Model.paper_R_H_theory_closed_extension_model",
    "theorem:Bacon_Source_Relational_Diagram_Open_Denotation.paper_R_diagram_target.paper_R_diagram_map_open_denote",
    "theorem:Bacon_Source_Relational_Diagram_Homomorphism.paper_R_diagram_target.paper_R_diagram_reduct_model",
    "theorem:Bacon_Source_Relational_Diagram_Homomorphism.paper_R_diagram_target.paper_R_diagram_reduct_homomorphism",
    "theorem:Bacon_Source_Relational_H_Theory_Substitution.paper_R_H_theory_substitution",
    "theorem:Bacon_Source_Relational_Theoretical_Naming_Independence.paper_R_theoretical_naming_independent",
    "theorem:Bacon_Source_Relational_Parameter_Theory.paper_R_parameter_theory_old_iff",
    "theorem:Bacon_Source_Relational_Parameter_H_Theory.paper_R_H_theory_parameter",
    "theorem:Bacon_Source_Relational_Parameter_Propositional_Closure.paper_R_parameter_theory_PE_closed",
    "theorem:Bacon_Source_Relational_Parameter_Validity.paper_R_bbk_model.paper_R_parameter_theory_valid",
    "theorem:Bacon_Source_Relational_Naming_Signature_Cardinal.paper_R_naming_signature_cardinal_bound",
    "theorem:Bacon_Source_Relational_Positive_Diagram_Separating_Model.paper_R_bbk_model.paper_R_positive_diagram_separating_model",
    "theorem:Bacon_Source_Relational_Naming_Separation.paper_R_bbk_model.paper_R_naming_proposition_separation",
    "theorem:Bacon_Source_Relational_Naming_Bounded_Separation.paper_R_bbk_model.paper_R_naming_bounded_proposition_separation",
)
RELATIONAL_N73_CONSTRUCTION_ROOTS = (
    RELATIONAL_N73_ROOTS[1], *RELATIONAL_N73_ROOTS[12:],
)
RELATIONAL_N73_SEMANTIC_ROOTS = (
    *RELATIONAL_N73_ROOTS[:5], RELATIONAL_N73_ROOTS[10], *RELATIONAL_N73_ROOTS[12:],
)
RELATIONAL_N73_H_PROOF_ROOTS = RELATIONAL_N73_ROOTS[5:10]
RELATIONAL_N73_HOMOMORPHISM_ROOTS = (
    RELATIONAL_N73_ROOTS[4], RELATIONAL_N73_ROOTS[13], RELATIONAL_N73_ROOTS[14],
)
RELATIONAL_N73_NAMESPACE_CONSTANTS = {"paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_parameter_theory"}
RELATIONAL_N73_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Naming_Validity.paper_R_bbk_model.paper_R_naming_valid_iff": {"paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support"},
    "theorem:Bacon_Source_Relational_H_Theory_Closed_Extension_Model.paper_R_H_theory_closed_extension_model": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_named_consistent", "paper_R_named_top", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Diagram_Open_Denotation.paper_R_diagram_target.paper_R_diagram_map_open_denote": {"paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_positive_diagram"},
    "theorem:Bacon_Source_Relational_Diagram_Homomorphism.paper_R_diagram_target.paper_R_diagram_reduct_model": {"paper_R_constant_pullback_denote", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_naming_signature"},
    "theorem:Bacon_Source_Relational_Diagram_Homomorphism.paper_R_diagram_target.paper_R_diagram_reduct_homomorphism": {"paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_positive_diagram"},
    "theorem:Bacon_Source_Relational_H_Theory_Substitution.paper_R_H_theory_substitution": {"paper_R_H_theory", "paper_R_named_top"},
    "theorem:Bacon_Source_Relational_Theoretical_Naming_Independence.paper_R_theoretical_naming_independent": {"paper_R_H_theory", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_mix", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support"},
    "theorem:Bacon_Source_Relational_Parameter_Theory.paper_R_parameter_theory_old_iff": {"paper_R_H_theory", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory"},
    "theorem:Bacon_Source_Relational_Parameter_H_Theory.paper_R_H_theory_parameter": {"paper_R_H_theory", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory"},
    "theorem:Bacon_Source_Relational_Parameter_Propositional_Closure.paper_R_parameter_theory_PE_closed": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory"},
    "theorem:Bacon_Source_Relational_Parameter_Validity.paper_R_bbk_model.paper_R_parameter_theory_valid": {"paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory"},
    "theorem:Bacon_Source_Relational_Naming_Signature_Cardinal.paper_R_naming_signature_cardinal_bound": {"paper_R_naming_signature"},
    "theorem:Bacon_Source_Relational_Positive_Diagram_Separating_Model.paper_R_bbk_model.paper_R_positive_diagram_separating_model": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_positive_diagram", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Naming_Separation.paper_R_bbk_model.paper_R_naming_proposition_separation": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Naming_Bounded_Separation.paper_R_bbk_model.paper_R_naming_bounded_proposition_separation": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
}


# Theorem 3.12: pure syntax/proof, supplied-category semantics, actual
# bounded construction, and final completeness retain distinct boundaries.
# Equivalence appears only in the three selected-category iff proofs through
# the previously checked forward soundness inclusion, never in native MF
# or Intensionality. All these roots remain pure HOL, not HOL-ZF.
RELATIONAL_T312_ROOTS = (
    "theorem:Bacon_Source_Relational_Normalization_Formula_Validity.paper_R_bbk_normalize_formula_valid_iff",
    "theorem:Bacon_Source_Relational_Normalization_Morphisms.paper_R_bbk_data_morphism_normalize_target",
    "theorem:Bacon_Source_Relational_Bounded_Theory_Models.paper_R_bounded_theory_models_category",
    "theorem:Bacon_Source_Relational_Bounded_Theory_Separation.paper_R_bounded_theory_separating_arrow",
    "theorem:Bacon_Source_Relational_Bounded_Theory_Quasi_Fregean.paper_R_bounded_theory_quasi_fregean",
    "theorem:Bacon_Source_Relational_Box_Truth.paper_R_bbk_model.paper_R_named_box_truth",
    "theorem:Bacon_Source_Relational_Tautology_Profile.paper_R_tautology_profile",
    "theorem:Bacon_Source_Relational_Quasi_Fregean_Box.paper_R_quasi_fregean_box_truth",
    "theorem:Bacon_Source_Relational_Intensionality_Proof.paper_R_classicism_abstraction_intensionality",
    "theorem:Bacon_Source_Relational_Bounded_Theory_Inhabited.paper_R_bounded_theory_models_nonempty",
    "theorem:Bacon_Source_Relational_Bounded_Theory_Countermodel.paper_R_bounded_theory_countermodel",
    "theorem:Bacon_Source_Relational_Bounded_Theory_Common.paper_R_bounded_models_common_theory",
    "theorem:Bacon_Source_Relational_Modalized_Functionality.paper_R_classicism_modalized_functionality",
    "theorem:Bacon_Source_Relational_Quasi_Functional_From_Modal_Functionality.paper_R_quasi_functional_from_modal_functionality",
    "theorem:Bacon_Source_Relational_Classicism_Theory_Minimality.paper_R_classicism_in_H_PE_zeta",
    "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_bounded_classicism_representation",
    "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_classicism_selected_category_iff",
    "theorem:Bacon_Source_Relational_Bounded_PE_Zeta_Category.paper_R_bounded_PE_zeta_category_represents",
    "theorem:Bacon_Source_Relational_Pure_Classicism_Completeness.paper_R_pure_classicism_selected_category_iff",
    "theorem:Bacon_Source_Relational_Arbitrary_Signature_Classicism_Completeness.paper_R_arbitrary_signature_classicism_selected_category_iff",
)
RELATIONAL_T312_H_ROOTS = (
    RELATIONAL_T312_ROOTS[3],
    RELATIONAL_T312_ROOTS[4],
    RELATIONAL_T312_ROOTS[8],
    RELATIONAL_T312_ROOTS[9],
    RELATIONAL_T312_ROOTS[10],
    RELATIONAL_T312_ROOTS[11],
    RELATIONAL_T312_ROOTS[12],
    RELATIONAL_T312_ROOTS[14],
    RELATIONAL_T312_ROOTS[15],
    RELATIONAL_T312_ROOTS[16],
    RELATIONAL_T312_ROOTS[17],
    RELATIONAL_T312_ROOTS[18],
    RELATIONAL_T312_ROOTS[19],
)
RELATIONAL_T312_C_ROOTS = (
    RELATIONAL_T312_ROOTS[8],
    RELATIONAL_T312_ROOTS[12],
    RELATIONAL_T312_ROOTS[14],
    RELATIONAL_T312_ROOTS[15],
    RELATIONAL_T312_ROOTS[16],
    RELATIONAL_T312_ROOTS[17],
    RELATIONAL_T312_ROOTS[18],
    RELATIONAL_T312_ROOTS[19],
)
RELATIONAL_T312_EQUIVALENCE_ROOTS = (
    RELATIONAL_T312_ROOTS[16],
    RELATIONAL_T312_ROOTS[18],
    RELATIONAL_T312_ROOTS[19],
)
RELATIONAL_T312_NAMESPACE_CONSTANTS = {
    "paper_R_bounded_theory_models", "paper_R_bounded_theory_arrows", "paper_R_zeta_closed",
}
RELATIONAL_T312_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Normalization_Formula_Validity.paper_R_bbk_normalize_formula_valid_iff": set(),
    "theorem:Bacon_Source_Relational_Normalization_Morphisms.paper_R_bbk_data_morphism_normalize_target": set(),
    "theorem:Bacon_Source_Relational_Bounded_Theory_Models.paper_R_bounded_theory_models_category": {"paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models"},
    "theorem:Bacon_Source_Relational_Bounded_Theory_Separation.paper_R_bounded_theory_separating_arrow": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Bounded_Theory_Quasi_Fregean.paper_R_bounded_theory_quasi_fregean": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Box_Truth.paper_R_bbk_model.paper_R_named_box_truth": {"paper_R_named_box", "paper_R_named_box_const"},
    "theorem:Bacon_Source_Relational_Tautology_Profile.paper_R_tautology_profile": set(),
    "theorem:Bacon_Source_Relational_Quasi_Fregean_Box.paper_R_quasi_fregean_box_truth": {"paper_R_named_box", "paper_R_named_box_const"},
    "theorem:Bacon_Source_Relational_Intensionality_Proof.paper_R_classicism_abstraction_intensionality": {"paper_R_H_theory", "paper_R_all_vec", "paper_R_named_box", "paper_R_named_box_const"},
    "theorem:Bacon_Source_Relational_Bounded_Theory_Inhabited.paper_R_bounded_theory_models_nonempty": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_consistent", "paper_R_named_top", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Bounded_Theory_Countermodel.paper_R_bounded_theory_countermodel": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_consistent", "paper_R_named_top", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Bounded_Theory_Common.paper_R_bounded_models_common_theory": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_consistent", "paper_R_named_top", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Modalized_Functionality.paper_R_classicism_modalized_functionality": {"paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_all_vec", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_top"},
    "theorem:Bacon_Source_Relational_Quasi_Functional_From_Modal_Functionality.paper_R_quasi_functional_from_modal_functionality": {"paper_R_named_box", "paper_R_named_box_const"},
    "theorem:Bacon_Source_Relational_Classicism_Theory_Minimality.paper_R_classicism_in_H_PE_zeta": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_top", "paper_R_zeta_closed"},
    "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_bounded_classicism_representation": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_classicism_selected_category_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Bounded_PE_Zeta_Category.paper_R_bounded_PE_zeta_category_represents": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature", "paper_R_zeta_closed"},
    "theorem:Bacon_Source_Relational_Pure_Classicism_Completeness.paper_R_pure_classicism_selected_category_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Arbitrary_Signature_Classicism_Completeness.paper_R_arbitrary_signature_classicism_selected_category_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
}
RELATIONAL_T312_MODEL_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Normalization_Formula_Validity.paper_R_bbk_normalize_formula_valid_iff": {"paper_R_bbk_data_valid", "paper_R_bbk_model", "paper_R_bbk_model_axioms"},
    "theorem:Bacon_Source_Relational_Normalization_Morphisms.paper_R_bbk_data_morphism_normalize_target": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism"},
    "theorem:Bacon_Source_Relational_Bounded_Theory_Models.paper_R_bounded_theory_models_category": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Bounded_Theory_Separation.paper_R_bounded_theory_separating_arrow": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Bounded_Theory_Quasi_Fregean.paper_R_bounded_theory_quasi_fregean": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Box_Truth.paper_R_bbk_model.paper_R_named_box_truth": {"paper_R_bbk_model", "paper_R_bbk_model_axioms"},
    "theorem:Bacon_Source_Relational_Tautology_Profile.paper_R_tautology_profile": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Quasi_Fregean_Box.paper_R_quasi_fregean_box_truth": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Intensionality_Proof.paper_R_classicism_abstraction_intensionality": set(),
    "theorem:Bacon_Source_Relational_Bounded_Theory_Inhabited.paper_R_bounded_theory_models_nonempty": {"paper_R_bbk_data_valid", "paper_R_bbk_model", "paper_R_bbk_model_axioms"},
    "theorem:Bacon_Source_Relational_Bounded_Theory_Countermodel.paper_R_bounded_theory_countermodel": {"paper_R_bbk_data_valid", "paper_R_bbk_model", "paper_R_bbk_model_axioms"},
    "theorem:Bacon_Source_Relational_Bounded_Theory_Common.paper_R_bounded_models_common_theory": {"paper_R_bbk_data_valid", "paper_R_bbk_model", "paper_R_bbk_model_axioms"},
    "theorem:Bacon_Source_Relational_Modalized_Functionality.paper_R_classicism_modalized_functionality": set(),
    "theorem:Bacon_Source_Relational_Quasi_Functional_From_Modal_Functionality.paper_R_quasi_functional_from_modal_functionality": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Classicism_Theory_Minimality.paper_R_classicism_in_H_PE_zeta": set(),
    "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_bounded_classicism_representation": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_classicism_selected_category_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Bounded_PE_Zeta_Category.paper_R_bounded_PE_zeta_category_represents": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Pure_Classicism_Completeness.paper_R_pure_classicism_selected_category_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Arbitrary_Signature_Classicism_Completeness.paper_R_arbitrary_signature_classicism_selected_category_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
}


# Small separating hulls provide an actual bounded arrow code for
# Proposition 3.22. The new HOL-ZF constructors are distinct from all
# earlier represented-input and generic model-deduction tiers.
HULL_ACTION_PIPELINE_ROOTS = (
    "theorem:Bacon_Source_Relational_Separating_Hull_Category.paper_R_separating_hull.paper_R_hull_subcategory",
    "theorem:Bacon_Source_Relational_Separating_Hull_Category.paper_R_separating_hull.paper_R_hull_quasi_fregean",
    "theorem:Bacon_Source_Relational_Hull_Cardinal_Stages.paper_R_separating_hull_arrows_cardinal_bound",
    "theorem:Bacon_Source_Relational_Hull_Cardinal_Stages.paper_R_separating_hull_objects_cardinal_bound",
    "theorem:Bacon_Source_Relational_Classical_Separating_Hull.paper_R_classicism_hull.paper_R_classicism_hull_intensional",
    "theorem:Bacon_Source_Relational_Rooted_Separating_Hull.paper_R_classicism_hull.paper_R_classicism_rooted_hull_category",
    "theorem:Bacon_Source_Relational_Classical_Hull_Cardinal.paper_R_classicism_hull.paper_R_classicism_rooted_cardinal_bounds",
    "theorem:Bacon_Source_Relational_Classicism_Counterexample.paper_R_bounded_classicism_counterexample",
    "theorem:Bacon_Source_ZF_Natural_Bounds.paper_ZF_nat_values_infinite",
    "theorem:Bacon_Source_ZF_Natural_Bounds.paper_ZF_cardinal_bounded_encoding",
    "theorem:Bacon_Source_ZF_Hull_Representation.paper_ZF_classicism_hull_action_representation",
    "theorem:Bacon_Source_ZF_Action_Countermodel.paper_ZF_action_countermodel",
    "theorem:Bacon_Source_ZF_Action_Completeness.paper_ZF_classicism_action_iff",
    "theorem:Bacon_Source_ZF_Pure_Action_Completeness.paper_ZF_pure_classicism_action_iff",
    "theorem:Bacon_Source_ZF_Pure_Action_Completeness.paper_ZF_countable_classicism_action_iff",
)
PURE_HULL_ROOTS = HULL_ACTION_PIPELINE_ROOTS[:8]
ZF_HULL_ROOTS = HULL_ACTION_PIPELINE_ROOTS[8:]
ZF_HULL_CONSTRUCTION_ROOTS = HULL_ACTION_PIPELINE_ROOTS[10:]
HULL_NATIVE_C_ROOTS = (*HULL_ACTION_PIPELINE_ROOTS[4:8], *ZF_HULL_CONSTRUCTION_ROOTS)
HULL_ACTION_NAMESPACE_CONSTANTS = {"paper_R_arrow_endpoints", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_ZF_record_action_valid"}
HULL_ACTION_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Separating_Hull_Category.paper_R_separating_hull.paper_R_hull_subcategory": {"paper_R_arrow_endpoints", "paper_R_chosen_separator", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices"},
    "theorem:Bacon_Source_Relational_Separating_Hull_Category.paper_R_separating_hull.paper_R_hull_quasi_fregean": {"paper_R_arrow_endpoints", "paper_R_chosen_separator", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices"},
    "theorem:Bacon_Source_Relational_Hull_Cardinal_Stages.paper_R_separating_hull_arrows_cardinal_bound": {"paper_R_arrow_endpoints", "paper_R_chosen_separator", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices"},
    "theorem:Bacon_Source_Relational_Hull_Cardinal_Stages.paper_R_separating_hull_objects_cardinal_bound": {"paper_R_arrow_endpoints", "paper_R_chosen_separator", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices"},
    "theorem:Bacon_Source_Relational_Classical_Separating_Hull.paper_R_classicism_hull.paper_R_classicism_hull_intensional": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Rooted_Separating_Hull.paper_R_classicism_hull.paper_R_classicism_rooted_hull_category": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Classical_Hull_Cardinal.paper_R_classicism_hull.paper_R_classicism_rooted_cardinal_bounds": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Classicism_Counterexample.paper_R_bounded_classicism_counterexample": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_consistent", "paper_R_named_top", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_ZF_Natural_Bounds.paper_ZF_nat_values_infinite": set(),
    "theorem:Bacon_Source_ZF_Natural_Bounds.paper_ZF_cardinal_bounded_encoding": set(),
    "theorem:Bacon_Source_ZF_Hull_Representation.paper_ZF_classicism_hull_action_representation": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_ZF_Action_Countermodel.paper_ZF_action_countermodel": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_ZF_Action_Completeness.paper_ZF_classicism_action_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature", "paper_ZF_record_action_valid"},
    "theorem:Bacon_Source_ZF_Pure_Action_Completeness.paper_ZF_pure_classicism_action_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature", "paper_ZF_record_action_valid"},
    "theorem:Bacon_Source_ZF_Pure_Action_Completeness.paper_ZF_countable_classicism_action_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature", "paper_ZF_record_action_valid"},
}
HULL_ACTION_MODEL_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Separating_Hull_Category.paper_R_separating_hull.paper_R_hull_subcategory": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Separating_Hull_Category.paper_R_separating_hull.paper_R_hull_quasi_fregean": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Hull_Cardinal_Stages.paper_R_separating_hull_arrows_cardinal_bound": set(),
    "theorem:Bacon_Source_Relational_Hull_Cardinal_Stages.paper_R_separating_hull_objects_cardinal_bound": set(),
    "theorem:Bacon_Source_Relational_Classical_Separating_Hull.paper_R_classicism_hull.paper_R_classicism_hull_intensional": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Rooted_Separating_Hull.paper_R_classicism_hull.paper_R_classicism_rooted_hull_category": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Classical_Hull_Cardinal.paper_R_classicism_hull.paper_R_classicism_rooted_cardinal_bounds": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    "theorem:Bacon_Source_Relational_Classicism_Counterexample.paper_R_bounded_classicism_counterexample": {"paper_R_bbk_data_valid", "paper_R_bbk_model", "paper_R_bbk_model_axioms"},
    "theorem:Bacon_Source_ZF_Natural_Bounds.paper_ZF_nat_values_infinite": set(),
    "theorem:Bacon_Source_ZF_Natural_Bounds.paper_ZF_cardinal_bounded_encoding": set(),
    "theorem:Bacon_Source_ZF_Hull_Representation.paper_ZF_classicism_hull_action_representation": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory", "paper_ZF_action_model", "paper_ZF_action_premodel"},
    "theorem:Bacon_Source_ZF_Action_Countermodel.paper_ZF_action_countermodel": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory", "paper_ZF_action_model", "paper_ZF_action_premodel"},
    "theorem:Bacon_Source_ZF_Action_Completeness.paper_ZF_classicism_action_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory", "paper_ZF_action_model", "paper_ZF_action_premodel"},
    "theorem:Bacon_Source_ZF_Pure_Action_Completeness.paper_ZF_pure_classicism_action_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory", "paper_ZF_action_model", "paper_ZF_action_premodel"},
    "theorem:Bacon_Source_ZF_Pure_Action_Completeness.paper_ZF_countable_classicism_action_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory", "paper_ZF_action_model", "paper_ZF_action_premodel"},
}


# Typed name maps and finite single-formula compression. These are new,
# exact permissions; older roots do not inherit the compression namespace.
SIGNATURE_ACTION_TRANSPORT_ROOTS = (
    "theorem:Bacon_Source_Relational_Typed_Constant_Map.paper_R_typed_constant_map_language",
    "theorem:Bacon_Source_Relational_Typed_Constant_Map_Conversion.paper_R_typed_constant_map_raw_conversion",
    "theorem:Bacon_Source_Relational_H_Typed_Constant_Map.paper_R_named_H_typed_constant_map",
    "theorem:Bacon_Source_Relational_Classicism_Typed_Constant_Map.paper_R_classicism_typed_constant_map",
    "theorem:Bacon_Source_Relational_Signature_Compression_Section.paper_R_compression_formula_roundtrip",
    "theorem:Bacon_Source_Relational_Signature_Compression_Proof.paper_R_finite_formula_compression",
    "theorem:Bacon_Source_ZF_Action_Constant_Pullback.paper_ZF_action_eval_typed_constants",
    "theorem:Bacon_Source_ZF_Action_Constant_Pullback.paper_ZF_action_model_typed_constant_pullback",
    "theorem:Bacon_Source_ZF_Action_Validity_On.paper_ZF_record_action_valid_as_valid_on",
    "theorem:Bacon_Source_ZF_Arbitrary_Signature_Action_Countermodel.paper_ZF_arbitrary_signature_action_countermodel",
    "theorem:Bacon_Source_ZF_Arbitrary_Signature_Action_Completeness.paper_ZF_arbitrary_signature_action_iff",
)
PURE_SIGNATURE_TRANSPORT_ROOTS = SIGNATURE_ACTION_TRANSPORT_ROOTS[:6]
ZF_SIGNATURE_TRANSPORT_ROOTS = SIGNATURE_ACTION_TRANSPORT_ROOTS[6:]
SIGNATURE_TRANSPORT_C_ROOTS = (
    SIGNATURE_ACTION_TRANSPORT_ROOTS[3], SIGNATURE_ACTION_TRANSPORT_ROOTS[5],
    *SIGNATURE_ACTION_TRANSPORT_ROOTS[9:],
)
SIGNATURE_TRANSPORT_NAMESPACE_CONSTANTS = {"paper_R_compress_name", "paper_R_compressed_signature", "paper_R_compression_section", "paper_R_typed_constant_map", "paper_ZF_action_valid_on"}
SIGNATURE_TRANSPORT_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Typed_Constant_Map.paper_R_typed_constant_map_language": {"paper_R_typed_constant_map"},
    "theorem:Bacon_Source_Relational_Typed_Constant_Map_Conversion.paper_R_typed_constant_map_raw_conversion": {"paper_R_typed_constant_map"},
    "theorem:Bacon_Source_Relational_H_Typed_Constant_Map.paper_R_named_H_typed_constant_map": {"paper_R_typed_constant_map"},
    "theorem:Bacon_Source_Relational_Classicism_Typed_Constant_Map.paper_R_classicism_typed_constant_map": {"paper_R_typed_constant_map"},
    "theorem:Bacon_Source_Relational_Signature_Compression_Section.paper_R_compression_formula_roundtrip": {"paper_R_compress_name", "paper_R_compression_section", "paper_R_typed_constant_map"},
    "theorem:Bacon_Source_Relational_Signature_Compression_Proof.paper_R_finite_formula_compression": {"paper_R_compress_name", "paper_R_compressed_signature", "paper_R_compression_section", "paper_R_typed_constant_map"},
    "theorem:Bacon_Source_ZF_Action_Constant_Pullback.paper_ZF_action_eval_typed_constants": {"paper_R_typed_constant_map"},
    "theorem:Bacon_Source_ZF_Action_Constant_Pullback.paper_ZF_action_model_typed_constant_pullback": {"paper_R_typed_constant_map"},
    "theorem:Bacon_Source_ZF_Action_Validity_On.paper_ZF_record_action_valid_as_valid_on": {"paper_ZF_action_valid_on", "paper_ZF_record_action_valid"},
    "theorem:Bacon_Source_ZF_Arbitrary_Signature_Action_Countermodel.paper_ZF_arbitrary_signature_action_countermodel": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_compress_name", "paper_R_compressed_signature", "paper_R_compression_section", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_typed_constant_map", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_ZF_Arbitrary_Signature_Action_Completeness.paper_ZF_arbitrary_signature_action_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_compress_name", "paper_R_compressed_signature", "paper_R_compression_section", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_typed_constant_map", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature", "paper_ZF_action_valid_on"},
}
SIGNATURE_TRANSPORT_MODEL_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Typed_Constant_Map.paper_R_typed_constant_map_language": set(),
    "theorem:Bacon_Source_Relational_Typed_Constant_Map_Conversion.paper_R_typed_constant_map_raw_conversion": set(),
    "theorem:Bacon_Source_Relational_H_Typed_Constant_Map.paper_R_named_H_typed_constant_map": set(),
    "theorem:Bacon_Source_Relational_Classicism_Typed_Constant_Map.paper_R_classicism_typed_constant_map": set(),
    "theorem:Bacon_Source_Relational_Signature_Compression_Section.paper_R_compression_formula_roundtrip": set(),
    "theorem:Bacon_Source_Relational_Signature_Compression_Proof.paper_R_finite_formula_compression": set(),
    "theorem:Bacon_Source_ZF_Action_Constant_Pullback.paper_ZF_action_eval_typed_constants": set(),
    "theorem:Bacon_Source_ZF_Action_Constant_Pullback.paper_ZF_action_model_typed_constant_pullback": {"paper_ZF_action_model", "paper_ZF_action_premodel"},
    "theorem:Bacon_Source_ZF_Action_Validity_On.paper_ZF_record_action_valid_as_valid_on": {"paper_ZF_action_model", "paper_ZF_action_premodel"},
    "theorem:Bacon_Source_ZF_Arbitrary_Signature_Action_Countermodel.paper_ZF_arbitrary_signature_action_countermodel": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory", "paper_ZF_action_model", "paper_ZF_action_premodel"},
    "theorem:Bacon_Source_ZF_Arbitrary_Signature_Action_Completeness.paper_ZF_arbitrary_signature_action_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory", "paper_ZF_action_model", "paper_ZF_action_premodel"},
}
SIGNATURE_TRANSPORT_PROOF_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Typed_Constant_Map.paper_R_typed_constant_map_language": set(),
    "theorem:Bacon_Source_Relational_Typed_Constant_Map_Conversion.paper_R_typed_constant_map_raw_conversion": set(),
    "theorem:Bacon_Source_Relational_H_Typed_Constant_Map.paper_R_named_H_typed_constant_map": {"paper_R_named_H"},
    "theorem:Bacon_Source_Relational_Classicism_Typed_Constant_Map.paper_R_classicism_typed_constant_map": {"paper_R_classicism_proves", "paper_R_named_H"},
    "theorem:Bacon_Source_Relational_Signature_Compression_Section.paper_R_compression_formula_roundtrip": set(),
    "theorem:Bacon_Source_Relational_Signature_Compression_Proof.paper_R_finite_formula_compression": {"paper_R_classicism_proves", "paper_R_named_H"},
    "theorem:Bacon_Source_ZF_Action_Constant_Pullback.paper_ZF_action_eval_typed_constants": set(),
    "theorem:Bacon_Source_ZF_Action_Constant_Pullback.paper_ZF_action_model_typed_constant_pullback": set(),
    "theorem:Bacon_Source_ZF_Action_Validity_On.paper_ZF_record_action_valid_as_valid_on": set(),
    "theorem:Bacon_Source_ZF_Arbitrary_Signature_Action_Countermodel.paper_ZF_arbitrary_signature_action_countermodel": {"paper_R_classicism_proves", "paper_R_named_H", "paper_R_named_derivable"},
    "theorem:Bacon_Source_ZF_Arbitrary_Signature_Action_Completeness.paper_ZF_arbitrary_signature_action_iff": {"paper_R_classicism_proves", "paper_R_named_H", "paper_R_named_derivable"},
}


def signature_transport_forbidden(root, model_predicates):
    new_data = SIGNATURE_TRANSPORT_NAMESPACE_CONSTANTS - SIGNATURE_TRANSPORT_DATA_ALLOWLIST.get(root, set())
    if root not in SIGNATURE_ACTION_TRANSPORT_ROOTS:
        return new_data
    models = SIGNATURE_TRANSPORT_MODEL_ALLOWLIST[root]
    return (new_data | (ZF_PROOF_PREDICATES - SIGNATURE_TRANSPORT_PROOF_ALLOWLIST[root])
            | (set(model_predicates) - models) | ZF_FOREIGN_MODEL_PREDICATES
            | (ZF_INDEPENDENT_R_MODEL_PREDICATES - models)
            | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})


def signature_transport_counting_forbidden(root, constant_names):
    if root not in SIGNATURE_ACTION_TRANSPORT_ROOTS:
        return set()
    return {name for name in constant_names if name.startswith(("pHct_", "pHc_"))} | {
        "pH_closed_Henkin", "pH_countable_closed_Henkin",
        "paper_R_logical_count_tree", "paper_R_named_count_tree",
    }


# Literal Figure 3 certificates and positive modal T/4. No reverse
# six-axiom presentation, semantic model, or general Equivalence premise.
FIGURE3_MODAL_ROOTS = (
    "theorem:Bacon_Source_Relational_Figure3_Syntax.paper_R_figure3_axiom_closed",
    "theorem:Bacon_Source_Relational_Figure3_Language.paper_R_figure3_axiom_language",
    "theorem:Bacon_Source_Relational_Figure3_Certificates.paper_R_classicism_figure3_member",
    "theorem:Bacon_Source_Relational_Modal_T.paper_R_named_H_modal_T",
    "theorem:Bacon_Source_Relational_Modal_Four.paper_R_classicism_modal_4",
)
FIGURE3_MODAL_C_ROOTS = (FIGURE3_MODAL_ROOTS[2], FIGURE3_MODAL_ROOTS[4])
FIGURE3_NAMESPACE_CONSTANTS = {"RCommAnd", "RCommOr", "RDissolveAndOr", "RDissolveOrAnd", "RDistAndOr", "RDistOrAnd", "paper_R_figure3_axiom", "paper_R_figure3_axioms", "paper_R_figure3_bodies", "paper_R_figure3_laws", "paper_R_figure3_prefix", "paper_R_figure3_template", "paper_R_figure3_variables"}
FIGURE3_MODAL_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Figure3_Syntax.paper_R_figure3_axiom_closed": {"RCommAnd", "RCommOr", "RDissolveAndOr", "RDissolveOrAnd", "RDistAndOr", "RDistOrAnd", "paper_R_figure3_axiom", "paper_R_figure3_bodies", "paper_R_figure3_prefix"},
    "theorem:Bacon_Source_Relational_Figure3_Language.paper_R_figure3_axiom_language": {"RCommAnd", "RCommOr", "RDissolveAndOr", "RDissolveOrAnd", "RDistAndOr", "RDistOrAnd", "paper_R_figure3_axiom", "paper_R_figure3_bodies", "paper_R_figure3_prefix", "paper_R_figure3_variables"},
    "theorem:Bacon_Source_Relational_Figure3_Certificates.paper_R_classicism_figure3_member": {"RCommAnd", "RCommOr", "RDissolveAndOr", "RDissolveOrAnd", "RDistAndOr", "RDistOrAnd", "paper_R_figure3_axiom", "paper_R_figure3_axioms", "paper_R_figure3_bodies", "paper_R_figure3_laws", "paper_R_figure3_prefix", "paper_R_figure3_template", "paper_R_figure3_variables"},
    "theorem:Bacon_Source_Relational_Modal_T.paper_R_named_H_modal_T": {"paper_R_named_box", "paper_R_named_box_const"},
    "theorem:Bacon_Source_Relational_Modal_Four.paper_R_classicism_modal_4": {"paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_top"},
}
FIGURE3_MODAL_PROOF_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Figure3_Syntax.paper_R_figure3_axiom_closed": set(),
    "theorem:Bacon_Source_Relational_Figure3_Language.paper_R_figure3_axiom_language": set(),
    "theorem:Bacon_Source_Relational_Figure3_Certificates.paper_R_classicism_figure3_member": {"paper_R_classicism_proves", "paper_R_named_H"},
    "theorem:Bacon_Source_Relational_Modal_T.paper_R_named_H_modal_T": {"paper_R_named_H", "paper_R_named_derivable"},
    "theorem:Bacon_Source_Relational_Modal_Four.paper_R_classicism_modal_4": {"paper_R_classicism_proves", "paper_R_named_H", "paper_R_named_derivable"},
}


def figure3_modal_forbidden(root, model_predicates):
    new_data = FIGURE3_NAMESPACE_CONSTANTS - FIGURE3_MODAL_DATA_ALLOWLIST.get(root, set())
    if root not in FIGURE3_MODAL_ROOTS:
        return new_data
    return (new_data | (ZF_PROOF_PREDICATES - FIGURE3_MODAL_PROOF_ALLOWLIST[root])
            | set(model_predicates) | ZF_FOREIGN_MODEL_PREDICATES
            | ZF_INDEPENDENT_R_MODEL_PREDICATES
            | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})


# Book Definitions 17.1--17.4 and the explicit implication typing
# diagnostic: pure set/category structure, not a logical model tier.
BOOK_MODAL_STRUCTURE_ROOTS = (
    "theorem:Bacon_Book_Preorder_Powerset.book_preorder.book_preorder_powerset_action",
    "theorem:Bacon_Book_Preorder_Powerset.book_preorder_powerset_bijection",
    "theorem:Bacon_Book_Preorder_Powerset.book_preorder_powerset_transport_correspondence",
    "theorem:Bacon_Book_Modal_Implication_Typing.book_printed_implication_future_iff",
    "theorem:Bacon_Book_Modal_Implication_Typing.book_printed_implication_two_world_failure",
    "theorem:Bacon_Book_Modal_Implication_Naturality.book_preorder.book_future_implication_naturality",
    "theorem:Bacon_Book_Modal_Implication_Typing.book_printed_implication_restriction",
    "theorem:Bacon_Book_Modalized_Set.book_preorder.book_modalized_set_iff_action",
    "theorem:Bacon_Book_Modalized_Map.book_modalized_map_iff_action_map",
)
BOOK_MODAL_STRUCTURE_CONSTANTS = {"book_future_implication_set", "book_modalized_map", "book_modalized_set", "book_modalized_set_axioms", "book_pointed_preorder", "book_pointed_preorder_axioms", "book_preorder", "book_preorder_arrows", "book_preorder_compose", "book_preorder_future", "book_preorder_identity", "book_preorder_powerset", "book_preorder_powerset_decode", "book_preorder_powerset_encode", "book_preorder_powerset_transport", "book_preorder_truncate", "book_printed_implication_set"}
BOOK_MODAL_STRUCTURE_DATA_ALLOWLIST = {
    "theorem:Bacon_Book_Preorder_Powerset.book_preorder.book_preorder_powerset_action": {"book_preorder", "book_preorder_arrows", "book_preorder_compose", "book_preorder_future", "book_preorder_identity", "book_preorder_powerset", "book_preorder_powerset_transport", "book_preorder_truncate"},
    "theorem:Bacon_Book_Preorder_Powerset.book_preorder_powerset_bijection": {"book_preorder_arrows", "book_preorder_future", "book_preorder_powerset", "book_preorder_powerset_decode", "book_preorder_powerset_encode"},
    "theorem:Bacon_Book_Preorder_Powerset.book_preorder_powerset_transport_correspondence": {"book_preorder_arrows", "book_preorder_compose", "book_preorder_future", "book_preorder_powerset", "book_preorder_powerset_encode", "book_preorder_powerset_transport", "book_preorder_truncate"},
    "theorem:Bacon_Book_Modal_Implication_Typing.book_printed_implication_future_iff": {"book_preorder_future", "book_preorder_powerset", "book_printed_implication_set"},
    "theorem:Bacon_Book_Modal_Implication_Typing.book_printed_implication_two_world_failure": {"book_pointed_preorder", "book_pointed_preorder_axioms", "book_preorder", "book_preorder_future", "book_preorder_powerset", "book_printed_implication_set"},
    "theorem:Bacon_Book_Modal_Implication_Naturality.book_preorder.book_future_implication_naturality": {"book_future_implication_set", "book_preorder", "book_preorder_future", "book_preorder_powerset", "book_preorder_truncate"},
    "theorem:Bacon_Book_Modal_Implication_Typing.book_printed_implication_restriction": {"book_future_implication_set", "book_printed_implication_set"},
    "theorem:Bacon_Book_Modalized_Set.book_preorder.book_modalized_set_iff_action": {"book_modalized_set", "book_modalized_set_axioms", "book_preorder", "book_preorder_arrows", "book_preorder_compose", "book_preorder_identity"},
    "theorem:Bacon_Book_Modalized_Map.book_modalized_map_iff_action_map": {"book_modalized_map", "book_preorder_arrows"},
}


def book_modal_structure_forbidden(root, model_predicates):
    new_data = BOOK_MODAL_STRUCTURE_CONSTANTS - BOOK_MODAL_STRUCTURE_DATA_ALLOWLIST.get(root, set())
    if root not in BOOK_MODAL_STRUCTURE_ROOTS:
        return new_data
    return (new_data | ZF_PROOF_PREDICATES | set(model_predicates)
            | ZF_FOREIGN_MODEL_PREDICATES | ZF_INDEPENDENT_R_MODEL_PREDICATES
            | {"paper_R_equivalence_proves", "paper_R_classicism_proves",
               "paper_R_named_H", "paper_R_named_derivable", "named_beta_eta_in_language"})


# Book Definition 17.9 / Exercise 17.4: full future homomorphism spaces,
# raw codecs and a genuine failure of truncation surjectivity.
BOOK_EXPONENTIAL_ROOTS = (
    "theorem:Bacon_Book_Modalized_Exponential_Homomorphisms.book_preorder.book_modalized_exponential_iff_future_map",
    "theorem:Bacon_Book_Modalized_Exponential_Codec.book_modalized_exponential_bijection",
    "theorem:Bacon_Book_Modalized_Exponential_Transport.book_modalized_exponential_transport_correspondence",
    "theorem:Bacon_Book_Modalized_Exponential_Transport.book_modalized_exponential_is_modalized_set",
    "theorem:Bacon_Book_Modalized_Exponential_Nonextension.book_ex17_4_transport_not_surjective",
    "theorem:Bacon_Book_Modalized_Evaluation.book_modalized_evaluation_source",
    "theorem:Bacon_Book_Modalized_Evaluation.book_modalized_evaluation_map",
)
BOOK_EXPONENTIAL_CONSTANTS = {"book_ex17_4_counterpart", "book_ex17_4_domain", "book_ex17_4_future_map", "book_ex17_4_le", "book_modalized_evaluate", "book_modalized_exponential", "book_modalized_exponential_decode", "book_modalized_exponential_encode", "book_modalized_exponential_pairs", "book_modalized_exponential_transport"}
BOOK_EXPONENTIAL_DATA_ALLOWLIST = {
    "theorem:Bacon_Book_Modalized_Exponential_Homomorphisms.book_preorder.book_modalized_exponential_iff_future_map": {"book_modalized_exponential", "book_modalized_exponential_pairs", "book_modalized_map", "book_preorder", "book_preorder_future"},
    "theorem:Bacon_Book_Modalized_Exponential_Codec.book_modalized_exponential_bijection": {"book_modalized_exponential", "book_modalized_exponential_decode", "book_modalized_exponential_encode", "book_modalized_exponential_pairs", "book_preorder_arrows", "book_preorder_compose"},
    "theorem:Bacon_Book_Modalized_Exponential_Transport.book_modalized_exponential_transport_correspondence": {"book_modalized_exponential_encode", "book_modalized_exponential_pairs", "book_modalized_exponential_transport", "book_preorder_arrows", "book_preorder_compose"},
    "theorem:Bacon_Book_Modalized_Exponential_Transport.book_modalized_exponential_is_modalized_set": {"book_modalized_exponential", "book_modalized_exponential_decode", "book_modalized_exponential_encode", "book_modalized_exponential_pairs", "book_modalized_exponential_transport", "book_modalized_set", "book_modalized_set_axioms", "book_preorder", "book_preorder_arrows", "book_preorder_compose", "book_preorder_identity"},
    "theorem:Bacon_Book_Modalized_Exponential_Nonextension.book_ex17_4_transport_not_surjective": {"book_ex17_4_counterpart", "book_ex17_4_domain", "book_ex17_4_future_map", "book_ex17_4_le", "book_modalized_exponential", "book_modalized_exponential_pairs", "book_modalized_exponential_transport"},
    "theorem:Bacon_Book_Modalized_Evaluation.book_modalized_evaluation_source": {"book_modalized_exponential", "book_modalized_exponential_decode", "book_modalized_exponential_encode", "book_modalized_exponential_pairs", "book_modalized_exponential_transport", "book_modalized_set", "book_modalized_set_axioms", "book_preorder", "book_preorder_arrows", "book_preorder_compose", "book_preorder_identity"},
    "theorem:Bacon_Book_Modalized_Evaluation.book_modalized_evaluation_map": {"book_modalized_evaluate", "book_modalized_exponential", "book_modalized_exponential_pairs", "book_modalized_exponential_transport", "book_modalized_map", "book_modalized_set", "book_modalized_set_axioms", "book_preorder"},
}


def book_exponential_forbidden(root, model_predicates):
    new_data = BOOK_EXPONENTIAL_CONSTANTS - BOOK_EXPONENTIAL_DATA_ALLOWLIST.get(root, set())
    if root not in BOOK_EXPONENTIAL_ROOTS:
        return new_data
    return (new_data | ZF_PROOF_PREDICATES | set(model_predicates)
            | ZF_FOREIGN_MODEL_PREDICATES | ZF_INDEPENDENT_R_MODEL_PREDICATES
            | {"paper_R_equivalence_proves", "paper_R_classicism_proves",
               "paper_R_named_H", "paper_R_named_derivable", "named_beta_eta_in_language"})


def hull_action_pipeline_forbidden(root, model_predicates):
    new_data = HULL_ACTION_NAMESPACE_CONSTANTS - HULL_ACTION_DATA_ALLOWLIST.get(root, set())
    if root not in HULL_ACTION_PIPELINE_ROOTS:
        return new_data
    proofs = ({"paper_R_named_H", "paper_R_named_derivable", "paper_R_classicism_proves"}
              if root in HULL_NATIVE_C_ROOTS else set())
    permitted_models = HULL_ACTION_MODEL_ALLOWLIST[root]
    return (new_data | (ZF_PROOF_PREDICATES - proofs) | (set(model_predicates) - permitted_models)
            | ZF_FOREIGN_MODEL_PREDICATES | (ZF_INDEPENDENT_R_MODEL_PREDICATES - permitted_models)
            | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})


def hull_action_counting_forbidden(root, constant_names):
    if root not in HULL_ACTION_PIPELINE_ROOTS:
        return set()
    return {name for name in constant_names if name.startswith(("pHct_", "pHc_"))} | {
        "pH_closed_Henkin", "pH_countable_closed_Henkin",
        "paper_R_logical_count_tree", "paper_R_named_count_tree",
    }


def relational_t312_forbidden(root, model_predicates):
    new_data = RELATIONAL_T312_NAMESPACE_CONSTANTS - RELATIONAL_T312_DATA_ALLOWLIST.get(root, set())
    if root not in RELATIONAL_T312_ROOTS:
        return new_data
    proofs = set()
    if root in RELATIONAL_T312_H_ROOTS:
        proofs |= {"paper_R_named_H", "paper_R_named_derivable"}
    if root in RELATIONAL_T312_C_ROOTS:
        proofs.add("paper_R_classicism_proves")
    if root in RELATIONAL_T312_EQUIVALENCE_ROOTS:
        proofs.add("paper_R_equivalence_proves")
    models = RELATIONAL_T312_MODEL_ALLOWLIST[root]
    return (new_data | (ZF_PROOF_PREDICATES - proofs) | (set(model_predicates) - models)
            | ZF_FOREIGN_MODEL_PREDICATES | (ZF_INDEPENDENT_R_MODEL_PREDICATES - models)
            | {"named_beta_eta_in_language"})


def relational_t312_counting_forbidden(root, constant_names):
    if root not in RELATIONAL_T312_ROOTS:
        return set()
    return {name for name in constant_names if name.startswith(("pHct_", "pHc_"))} | {
        "pH_closed_Henkin", "pH_countable_closed_Henkin",
        "paper_R_logical_count_tree", "paper_R_named_count_tree",
    }


def relational_n73_forbidden(root, model_predicates):
    new_data = RELATIONAL_N73_NAMESPACE_CONSTANTS - RELATIONAL_N73_DATA_ALLOWLIST.get(root, set())
    if root not in RELATIONAL_N73_ROOTS:
        return new_data
    proofs = set()
    if root in RELATIONAL_N73_H_PROOF_ROOTS:
        proofs.add("paper_R_named_H")
    elif root in RELATIONAL_N73_CONSTRUCTION_ROOTS:
        proofs |= {"paper_R_named_H", "paper_R_named_derivable"}
    model = ({"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
             if root in RELATIONAL_N73_SEMANTIC_ROOTS else set())
    relations = ({"paper_R_bbk_homomorphism"} if root in RELATIONAL_N73_HOMOMORPHISM_ROOTS else set())
    return (new_data | (ZF_PROOF_PREDICATES - proofs) | (set(model_predicates) - model - relations)
            | ZF_FOREIGN_MODEL_PREDICATES | (ZF_INDEPENDENT_R_MODEL_PREDICATES - model - relations)
            | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})


def relational_n73_counting_forbidden(root, constant_names):
    if root not in RELATIONAL_N73_ROOTS:
        return set()
    return {name for name in constant_names if name.startswith(("pHct_", "pHc_"))} | {
        "pH_closed_Henkin", "pH_countable_closed_Henkin",
        "paper_R_logical_count_tree", "paper_R_named_count_tree",
    }


def relational_closure_naming_diagram_forbidden(root, model_predicates):
    new_data = RELATIONAL_CLOSURE_DIAGRAM_CONSTANTS - RELATIONAL_CLOSURE_NAMING_DIAGRAM_DATA_ALLOWLIST.get(root, set())
    if root not in RELATIONAL_CLOSURE_NAMING_DIAGRAM_ROOTS:
        return new_data
    if root in RELATIONAL_H_THEORY_MODEL_ROOTS:
        return new_data | {"named_beta_eta_in_language"}  # Model/proof boundary enforced separately.
    proofs = set()
    if root == RELATIONAL_CLOSURE_NAMING_DIAGRAM_ROOTS[0]:
        proofs.add("paper_R_named_H")
    elif root == RELATIONAL_CLOSURE_NAMING_DIAGRAM_ROOTS[6]:
        proofs |= {"paper_R_named_H", "paper_R_named_derivable"}
    model = ({"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
             if root in RELATIONAL_CLOSURE_NAMING_DIAGRAM_ROOTS[3:] else set())
    return (new_data | (ZF_PROOF_PREDICATES - proofs) | (set(model_predicates) - model)
            | ZF_FOREIGN_MODEL_PREDICATES | (ZF_INDEPENDENT_R_MODEL_PREDICATES - model)
            | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})


def relational_naming_modal_separation_forbidden(root, model_predicates):
    new_data = RELATIONAL_IMPLICATION_LIST_CONSTANTS - RELATIONAL_NAMING_MODAL_SEPARATION_DATA_ALLOWLIST.get(root, set())
    if root not in RELATIONAL_NAMING_MODAL_SEPARATION_ROOTS:
        return new_data
    proofs = ({"paper_R_named_H", "paper_R_named_derivable"}
              if root in RELATIONAL_MODAL_H_THEORY_ROOTS or root in RELATIONAL_SEPARATING_MODEL_ROOTS else set())
    model = ({"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
             if root in RELATIONAL_NAMING_TRUTH_MODEL_ROOTS or root in RELATIONAL_SEPARATING_MODEL_ROOTS else set())
    return (new_data | (ZF_PROOF_PREDICATES - proofs) | (set(model_predicates) - model)
            | ZF_FOREIGN_MODEL_PREDICATES | (ZF_INDEPENDENT_R_MODEL_PREDICATES - model)
            | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})


def relational_naming_structure_stability_forbidden(root, model_predicates):
    new_data = RELATIONAL_NAMING_FAMILY_CONSTANTS - RELATIONAL_NAMING_STRUCTURE_STABILITY_DATA_ALLOWLIST.get(root, set())
    if root not in RELATIONAL_NAMING_STRUCTURE_STABILITY_ROOTS:
        return new_data
    if root in RELATIONAL_NAMING_STRUCTURE_MODEL_ROOTS:
        model = {"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
        return (new_data | ZF_PROOF_PREDICATES | (set(model_predicates) - model)
                | ZF_FOREIGN_MODEL_PREDICATES | (ZF_INDEPENDENT_R_MODEL_PREDICATES - model)
                | {"named_beta_eta_in_language"})
    allowed = ({"paper_R_named_H", "paper_R_named_derivable"}
               if root in RELATIONAL_IDENTITY_STABILITY_ROOTS else set())
    return (new_data | (ZF_PROOF_PREDICATES - allowed) | set(model_predicates)
            | ZF_FOREIGN_MODEL_PREDICATES | ZF_INDEPENDENT_R_MODEL_PREDICATES
            | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})


def relational_chosen_naming_forbidden(root, model_predicates):
    new_data = RELATIONAL_CHOSEN_NAMING_CONSTANTS - RELATIONAL_CHOSEN_NAMING_DATA_ALLOWLIST.get(root, set())
    if root not in RELATIONAL_CHOSEN_NAMING_ROOTS:
        return new_data
    model = {"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
    return (new_data | ZF_PROOF_PREDICATES | (set(model_predicates) - model)
            | ZF_FOREIGN_MODEL_PREDICATES | (ZF_INDEPENDENT_R_MODEL_PREDICATES - model)
            | {"named_beta_eta_in_language"})


def relational_chart_necessitation_forbidden(root, model_predicates):
    new_data = RELATIONAL_CHART_NECESSITATION_CONSTANTS - RELATIONAL_CHART_NECESSITATION_DATA_ALLOWLIST.get(root, set())
    if root in RELATIONAL_CHART_MODEL_ROOTS:
        model = {"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
        return (new_data | ZF_PROOF_PREDICATES | (set(model_predicates) - model)
                | ZF_FOREIGN_MODEL_PREDICATES | (ZF_INDEPENDENT_R_MODEL_PREDICATES - model)
                | {"named_beta_eta_in_language"})
    if root in RELATIONAL_GENERIC_NECESSITATION_ROOTS or root in RELATIONAL_C_NECESSITATION_ROOTS:
        allowed = {"paper_R_named_H"}
        if root in RELATIONAL_C_NECESSITATION_ROOTS:
            allowed |= {"paper_R_named_derivable", "paper_R_classicism_proves"}
        return (new_data | (ZF_PROOF_PREDICATES - allowed) | set(model_predicates)
                | ZF_FOREIGN_MODEL_PREDICATES | ZF_INDEPENDENT_R_MODEL_PREDICATES
                | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})
    return new_data


def relational_zeta_coordinate_forbidden(root, model_predicates):
    if root in RELATIONAL_ZETA_ROOTS:
        allowed = {"paper_R_named_H", "paper_R_named_derivable", "paper_R_classicism_proves"}
        return ((ZF_PROOF_PREDICATES - allowed) | set(model_predicates)
                | ZF_FOREIGN_MODEL_PREDICATES | ZF_INDEPENDENT_R_MODEL_PREDICATES
                | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})
    if root in RELATIONAL_NAMING_COORDINATE_MODEL_ROOTS:
        model = {"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
        return (ZF_PROOF_PREDICATES | (set(model_predicates) - model)
                | ZF_FOREIGN_MODEL_PREDICATES | (ZF_INDEPENDENT_R_MODEL_PREDICATES - model)
                | {"named_beta_eta_in_language"})
    return set()


def relational_a3_forbidden(root, model_predicates):
    selectors = RELATIONAL_A3_SELECTOR_CONSTANTS - RELATIONAL_A3_DATA_ALLOWLIST.get(root, set())
    if root in RELATIONAL_A3_ROOTS:
        allowed = {"paper_R_named_H", "paper_R_named_derivable", "paper_R_classicism_proves"}
        if root in RELATIONAL_A3_EQUIVALENCE_ROOTS:
            allowed.add("paper_R_equivalence_proves")
        return (selectors | (ZF_PROOF_PREDICATES - allowed) | set(model_predicates)
                | ZF_FOREIGN_MODEL_PREDICATES | ZF_INDEPENDENT_R_MODEL_PREDICATES
                | {"named_beta_eta_in_language"})
    if root in RELATIONAL_SUBSTITUTION_MODEL_ROOTS:
        model = {"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
        return (selectors | ZF_PROOF_PREDICATES | (set(model_predicates) - model)
                | ZF_FOREIGN_MODEL_PREDICATES | (ZF_INDEPENDENT_R_MODEL_PREDICATES - model)
                | {"named_beta_eta_in_language"})
    return selectors


def relational_a2_complete_forbidden(root, model_predicates):
    naming_blocked = RELATIONAL_NAMING_REPLACEMENT_CONSTANTS - RELATIONAL_A2_COMPLETE_DATA_ALLOWLIST.get(root, set())
    if root not in RELATIONAL_A2_COMPLETE_ROOTS:
        return naming_blocked
    allowed = set()
    if root in RELATIONAL_A2_COMPLETE_C_ROOTS or root in RELATIONAL_A2_COMPLETE_H_ROOTS:
        allowed |= {"paper_R_named_H", "paper_R_named_derivable"}
    if root in RELATIONAL_A2_COMPLETE_C_ROOTS:
        allowed.add("paper_R_classicism_proves")
    return (naming_blocked | (ZF_PROOF_PREDICATES - allowed) | set(model_predicates)
            | ZF_FOREIGN_MODEL_PREDICATES | ZF_INDEPENDENT_R_MODEL_PREDICATES
            | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})


def relational_a2_continuation_forbidden(root, model_predicates):
    naming_blocked = RELATIONAL_NAMING_DATA_CONSTANTS - RELATIONAL_A2_CONTINUATION_DATA_ALLOWLIST.get(root, set())
    if root not in RELATIONAL_A2_CONTINUATION_ROOTS:
        return naming_blocked
    allowed = set()
    if root in RELATIONAL_A2_CONTINUATION_C_ROOTS or root in RELATIONAL_A2_CONTINUATION_H_ROOTS:
        allowed |= {"paper_R_named_H", "paper_R_named_derivable"}
    if root in RELATIONAL_A2_CONTINUATION_C_ROOTS:
        allowed.add("paper_R_classicism_proves")
    return (naming_blocked | (ZF_PROOF_PREDICATES - allowed) | set(model_predicates)
            | ZF_FOREIGN_MODEL_PREDICATES | ZF_INDEPENDENT_R_MODEL_PREDICATES
            | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})


def relational_a2_base_forbidden(root, model_predicates):
    top_blocked = RELATIONAL_A2_TOP_CONSTANTS - RELATIONAL_A2_BASE_DATA_ALLOWLIST.get(root, set())
    if root not in RELATIONAL_A2_BASE_ROOTS:
        return top_blocked
    allowed = {"paper_R_named_H", "paper_R_named_derivable"}
    if root in RELATIONAL_A2_BASE_C_ROOTS:
        allowed.add("paper_R_classicism_proves")
    return (top_blocked | (ZF_PROOF_PREDICATES - allowed) | set(model_predicates)
            | ZF_FOREIGN_MODEL_PREDICATES | ZF_INDEPENDENT_R_MODEL_PREDICATES
            | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})


def relational_cardinal_data_forbidden(root):
    if root in RELATIONAL_CARDINAL_RAW_ROOTS:
        return set()
    return set(RELATIONAL_CARDINAL_CODE_CONSTANTS)


def relational_cardinal_coding_forbidden(root, constant_names):
    if (root not in RELATIONAL_CARDINAL_RAW_ROOTS and root != RELATIONAL_CARDINAL_MODEL_ROOT
            and root != RELATIONAL_H_THEORY_MODEL_ROOTS[1]):
        return set()
    return {name for name in constant_names if name.startswith(("pHct_", "pHc_"))} | {
        "pH_closed_Henkin", "pH_countable_closed_Henkin",
        "paper_R_logical_count_tree", "paper_R_named_count_tree",
    }


def relational_c_preparation_forbidden(root, model_predicates):
    if root not in RELATIONAL_C_PREPARATION_ROOTS:
        return set()
    allowed = set()
    if root != RELATIONAL_C_PREPARATION_ROOTS[0]:
        allowed |= {"paper_R_named_H", "paper_R_named_derivable"}
    if root in RELATIONAL_C_PREPARATION_C_ROOTS:
        allowed.add("paper_R_classicism_proves")
    return ((ZF_PROOF_PREDICATES - allowed) | set(model_predicates)
            | ZF_FOREIGN_MODEL_PREDICATES | ZF_INDEPENDENT_R_MODEL_PREDICATES
            | {"paper_R_equivalence_proves", "named_beta_eta_in_language"})


CLASSICISM_SEMANTIC_RAW_ROOTS = (
    *RELATIONAL_CARDINAL_RAW_ROOTS,
    *RELATIONAL_RECODING_RAW_ROOTS,
    *RELATIONAL_COUNTING_RAW_ROOTS,
    *RELATIONAL_TERM_ENV_RAW_ROOTS,
    *RELATIONAL_HENKIN_SYNTAX_ROOTS,
    *RELATIONAL_CONSTANT_MAP_RAW_ROOTS,
    "theorem:Bacon_Source_Relational_Signature_Conversion.paper_R_retract_type",
    "theorem:Bacon_Source_Relational_Signature_Conservativity.paper_R_raw_retraction_support",
    "theorem:Bacon_Source_Relational_Signature_Conservativity.paper_R_conversion_to_signature",
    "theorem:Bacon_Source_Relational_Signature_Conservativity.paper_R_signature_conversion_iff",
    "theorem:Bacon_Source_Rooted_Category.paper_rooted_category.paper_root_arrows_nonempty",
    "theorem:Bacon_Source_Rooted_Category.paper_rooted_category.paper_root_arrows_compose",
    "theorem:Bacon_Source_Rooted_Category.paper_root_arrows_need_not_be_unique",
    "theorem:Bacon_Source_Reachable_Subcategory.paper_category.paper_reachable_outgoing_equal",
    "theorem:Bacon_Source_Reachable_Category.paper_category.paper_reachable_category",
    "theorem:Bacon_Source_Reachable_Category.paper_category.paper_reachable_rooted_category",
    "theorem:Bacon_Source_Reachable_Category.paper_action.paper_reachable_action",
    "theorem:Bacon_Source_Relational_Profile_Restriction.paper_R_truth_profile_outgoing_cong",
    "theorem:Bacon_Source_Relational_Profile_Restriction.paper_R_app_profile_outgoing_cong",
    "theorem:Bacon_Source_Relational_Profile_Restriction.paper_R_intension_outgoing_cong",
    "theorem:Bacon_Source_Relational_Intensional_Restriction.paper_R_quasi_fregean_outgoing_restrict",
    "theorem:Bacon_Source_Relational_Intensional_Restriction.paper_R_quasi_functional_outgoing_restrict",
    "theorem:Bacon_Source_Relational_Intensional_Restriction.paper_R_intensional_outgoing_restrict",
    "theorem:Bacon_Source_Relational_Binder_Vectors.paper_R_named_lam_vec_language",
    "theorem:Bacon_Source_Relational_Vector_Assignments.paper_R_update_vector_typed",
    "theorem:Bacon_Source_Relational_Vector_Assignments.paper_R_update_vector_adequate_iff",
    "theorem:Bacon_Source_Relational_Vector_Assignments.paper_R_update_vector_repeated",
    "theorem:Bacon_Source_Relational_Logical_Language.paper_R_named_paper_imp_language",
    "theorem:Bacon_Source_Relational_Logical_Language.paper_R_named_paper_iff_language",
    "theorem:Bacon_Source_Relational_Assignment_Extension.paper_R_complete_assignment_typed",
    "theorem:Bacon_Source_Relational_Intensional_Forward.paper_R_intensional_implies_quasi_functional",
    "theorem:Bacon_Source_Relational_Homomorphism.paper_R_bbk_homomorphism_identity",
    "theorem:Bacon_Source_Relational_Homomorphism.paper_R_bbk_homomorphism_compose",
    "theorem:Bacon_Source_Relational_Model_Normalization.paper_R_bbk_normalize_idempotent",
    "theorem:Bacon_Source_Relational_Model_Normalization.paper_R_bbk_canonical_data_ext",
    "theorem:Bacon_Source_Relational_Intension.paper_R_intension_zeroary_eq_iff",
    "theorem:Bacon_Source_Relational_Intension.paper_R_intensional_implies_quasi_fregean",
    "theorem:Bacon_Source_Exponential_Domain.paper_exponential_fiber_ext",
    "theorem:Bacon_Source_Exponential_Transport.paper_exponential_actions.paper_exponential_transport_type",
    "theorem:Bacon_Source_Exponential_Action.paper_exponential_action_from_actions",
    "theorem:Bacon_Source_Image_Action.paper_action_image_subaction",
    "theorem:Bacon_Source_Image_Action_Inverse.paper_action_image_inverse_map",
    "theorem:Bacon_Source_BBK_Application_Profile_Action.paper_bbk_quasi_functional_on_separates",
    "theorem:Bacon_Source_Relational_Types.paper_R_relational_iff_vector",
    "theorem:Bacon_Source_Relational_Syntax.paper_R_has_type_embedding",
    "theorem:Bacon_Source_Relational_Syntax.paper_R_language_embedding",
    "theorem:Bacon_Source_Relational_Syntax.paper_F_function_reflexivity_not_R",
    "theorem:Bacon_Source_Relational_Conversion.paper_R_raw_beta_eta_embedding",
    "theorem:Bacon_Source_Typed_Map_Normalization.paper_typed_map_normalized_eq_iff",
    "theorem:Bacon_Source_Typed_Map_Normalization.paper_typed_map_normalize_homomorphism",
    "theorem:Bacon_Source_Typed_Map_Normalization.paper_typed_map_normalize_compose",
    "theorem:Bacon_Source_Typed_Arrows.paper_typed_arrow_ext",
    "theorem:Bacon_Source_Typed_Arrows.paper_typed_identity_arrow",
    "theorem:Bacon_Source_Typed_Arrows.paper_typed_compose_arrow",
    "theorem:Bacon_Source_Typed_Map_Category.paper_typed_map_category",
    "theorem:Bacon_Source_Subcategory.paper_category.paper_category_restrict_arrows",
    "theorem:Bacon_Source_BBK_Model_Normalization.paper_bbk_normalize_idempotent",
    "theorem:Bacon_Source_BBK_Model_Normalization.paper_bbk_normalize_cong",
    "theorem:Bacon_Source_BBK_Normalized_Category.paper_bbk_canonical_data_ext",
    "theorem:Bacon_Source_BBK_Selected_Truth_Profile.paper_bbk_truth_profile_on_naturality",
    "theorem:Bacon_Source_BBK_Selected_Truth_Profile.paper_bbk_truth_profile_full_is_selected",
    "theorem:Bacon_Source_BBK_Selected_Truth_Profile.paper_bbk_quasi_fregean_on_separates",
    "theorem:Bacon_Source_Homomorphism_Assignments.paper_hom_assignment_adequate_iff",
    "theorem:Bacon_Source_Homomorphism_Assignments.paper_hom_assignment_typed",
    "theorem:Bacon_Source_Homomorphism_Assignments.paper_hom_assignment_identity",
    "theorem:Bacon_Source_Homomorphism_Assignments.paper_hom_assignment_compose",
    "theorem:Bacon_Source_Homomorphism_Assignments.paper_hom_assignment_cong",
    "theorem:Bacon_Source_BBK_Homomorphism.paper_bbk_homomorphism_identity",
    "theorem:Bacon_Source_BBK_Homomorphism.paper_bbk_homomorphism_compose",
    "theorem:Bacon_Source_BBK_Homomorphism.paper_bbk_homomorphism_cong",
    "theorem:Bacon_Source_Category.paper_category.paper_composite_arrow",
    "theorem:Bacon_Source_Category.paper_category.paper_identity_inj_on",
    "theorem:Bacon_Source_Category.paper_empty_category",
    "theorem:Bacon_Source_Action.paper_action.paper_transport_image",
    "theorem:Bacon_Source_Action.paper_action.paper_transport_three",
    "theorem:Bacon_Source_Action.paper_category.paper_empty_action",
    "theorem:Bacon_Source_Powerset_Action.paper_powerset_transport_type",
    "theorem:Bacon_Source_Powerset_Action.paper_category.paper_powerset_transport_identity",
    "theorem:Bacon_Source_Powerset_Action.paper_category.paper_powerset_transport_compose",
    "theorem:Bacon_Source_Powerset_Action.paper_category.paper_powerset_action",
)
CLASSICISM_SEMANTIC_MODEL_ROOTS = (
    "theorem:Bacon_Source_BBK_Application_Profile.paper_bbk_app_profile_on_coherent",
    "theorem:Bacon_Source_BBK_Application_Profile_Action.paper_bbk_app_profile_on_exponential",
    "theorem:Bacon_Source_BBK_Application_Profile_Action.paper_bbk_app_profile_on_naturality",
    "theorem:Bacon_Source_BBK_Application_Profile_Action.paper_bbk_profile_exponential_action",
    "theorem:Bacon_Source_BBK_Profile_Subactions.paper_bbk_truth_profile_subaction",
    "theorem:Bacon_Source_BBK_Profile_Subactions.paper_bbk_app_profile_subaction",
    "theorem:Bacon_Source_BBK_Vector_Application.paper_bbk_apply_vector_type",
    "theorem:Bacon_Source_BBK_Vector_Application.paper_bbk_map_vector_args_type",
    "theorem:Bacon_Source_BBK_Vector_Application.paper_bbk_apply_vector_morphism",
    "theorem:Bacon_Source_Typed_Map_Normalization.paper_typed_map_normalize_homomorphism_from_model",
    "theorem:Bacon_Source_BBK_Model_Data.paper_bbk_data_morphism_compose",
    "theorem:Bacon_Source_BBK_Arrows.paper_bbk_data_morphism_normalize",
    "theorem:Bacon_Source_BBK_Arrows.paper_bbk_identity_arrow",
    "theorem:Bacon_Source_BBK_Arrows.paper_bbk_compose_arrow",
    "theorem:Bacon_Source_BBK_Arrows.paper_bbk_arrow_ext",
    "theorem:Bacon_Source_BBK_Category.paper_bbk_record_category",
    "theorem:Bacon_Source_BBK_Category.paper_bbk_type_action",
    "theorem:Bacon_Source_BBK_Model_Normalization.paper_bbk_normalize_truth",
    "theorem:Bacon_Source_BBK_Normalization_Validity.paper_bbk_normalize_valid",
    "theorem:Bacon_Source_BBK_Normalized_Category.paper_bbk_normalized_objects_valid",
    "theorem:Bacon_Source_BBK_Normalized_Category.paper_bbk_normalized_category",
    "theorem:Bacon_Source_BBK_Subcategory.paper_bbk_subcategory_category",
    "theorem:Bacon_Source_BBK_Subcategory.paper_bbk_selected_type_action",
    "theorem:Bacon_Source_BBK_Category_Interface.paper_bbk_normalized_full_subcategory",
    "theorem:Bacon_Source_BBK_Category_Interface.paper_bbk_selected_truth_profile_naturality",
    "theorem:Bacon_Source_BBK_Application.paper_bbk_application_graph_exists",
    "theorem:Bacon_Source_BBK_Application.paper_bbk_application_graph_unique",
    "theorem:Bacon_Source_BBK_Application.paper_bbk_application_type",
    "theorem:Bacon_Source_BBK_Application.paper_bbk_application_denote",
    "theorem:Bacon_Source_BBK_Application_Morphism.paper_bbk_application_graph_morphism",
    "theorem:Bacon_Source_BBK_Application_Morphism.paper_bbk_application_morphism",
    "theorem:Bacon_Source_BBK_Model_Morphism.paper_bbk_model_morphism_identity",
    "theorem:Bacon_Source_BBK_Model_Morphism.paper_bbk_model_morphism_compose",
)
CLASSICISM_SEMANTIC_R_ROOTS = (
    "theorem:Bacon_Source_Relational_Binary_Logical_Application.paper_R_bbk_model.paper_R_binary_logical_application_truth",
    "theorem:Bacon_Source_Relational_Binary_Logical_Application.paper_R_binary_logical_application_morphism",
    "theorem:Bacon_Source_Relational_Boolean_Profiles.paper_R_bbk_model.paper_R_conjunction_application_truth",
    "theorem:Bacon_Source_Relational_Boolean_Profiles.paper_R_bbk_model.paper_R_disjunction_application_truth",
    "theorem:Bacon_Source_Relational_Boolean_Profiles.paper_R_conjunction_truth_profile",
    "theorem:Bacon_Source_Relational_Boolean_Profiles.paper_R_disjunction_truth_profile",
    "theorem:Bacon_Source_Relational_Identity_Profile.paper_R_bbk_model.paper_R_identity_application_truth",
    "theorem:Bacon_Source_Relational_Identity_Profile.paper_R_identity_truth_profile",
    "theorem:Bacon_Source_Relational_Quantifier_Profile.paper_R_bbk_model.paper_R_quantifier_value_truth",
    "theorem:Bacon_Source_Relational_Quantifier_Profile.paper_R_quantifier_profile_value",
    "theorem:Bacon_Source_Relational_Negation_Profile.paper_R_bbk_model.paper_R_negation_application_truth",
    "theorem:Bacon_Source_Relational_Negation_Profile.paper_R_negation_truth_profile",
    "theorem:Bacon_Source_Relational_Reachable_Subcategory.paper_R_bbk_reachable_subcategory",
    "theorem:Bacon_Source_Relational_Reachable_Subcategory.paper_R_bbk_reachable_outgoing_iff",
    "theorem:Bacon_Source_Relational_Reachable_Intensional.paper_R_bbk_reachable_intensional_rooted",
    "theorem:Bacon_Source_Relational_Abstraction_Application.paper_R_bbk_model.paper_R_abstraction_application_denote",
    "theorem:Bacon_Source_Relational_Vector_Abstraction_Denotation.paper_R_bbk_model.paper_R_lam_vec_application_denote",
    "theorem:Bacon_Source_Relational_Intensional_Abstraction.paper_R_common_truth_abstraction_intensions",
    "theorem:Bacon_Source_Relational_Intensional_Abstraction.paper_R_intensional_abstraction_denotation",
    "theorem:Bacon_Source_Relational_Common_Equivalence.paper_R_common_Equivalence",
    "theorem:Bacon_Source_Relational_Common_Quantifier_Rules.paper_R_common_Gen",
    "theorem:Bacon_Source_Relational_Common_Quantifier_Rules.paper_R_common_Inst",
    "theorem:Bacon_Source_Relational_Quasi_Fregean_Denotation.paper_R_quasi_fregean_denotation",
    "theorem:Bacon_Source_Relational_Common_Theory.paper_R_common_identity_iff",
    "theorem:Bacon_Source_Relational_Quasi_Functional_Denotation.paper_R_quasi_functional_denotation",
    "theorem:Bacon_Source_Relational_Common_Functionality.paper_R_common_Functionality",
    "theorem:Bacon_Source_Relational_Binary_Lambda_Denotation.paper_R_bbk_model.paper_R_binary_lambda_evaluate",
    "theorem:Bacon_Source_Relational_Logical_Truth.paper_R_bbk_model.paper_R_named_paper_imp_truth",
    "theorem:Bacon_Source_Relational_Logical_Truth.paper_R_bbk_model.paper_R_named_paper_iff_truth",
    "theorem:Bacon_Source_Relational_Binder_Truth.paper_R_bbk_model.paper_R_forall_binder_truth",
    "theorem:Bacon_Source_Relational_Binder_Truth.paper_R_bbk_model.paper_R_exists_binder_truth",
    "theorem:Bacon_Source_Relational_Assignment_Denotation.paper_R_bbk_model.paper_R_completed_assignment_denote",
    "theorem:Bacon_Source_Relational_Common_Propositional_Equivalence.paper_R_common_Propositional_Equivalence",
    "theorem:Bacon_Source_Relational_Conversion_Truth.paper_R_bbk_model.paper_R_conversion_biconditional_valid",
    "theorem:Bacon_Source_Relational_Propositional_Truth.paper_R_bbk_model.paper_R_named_PC_truth",
    "theorem:Bacon_Source_Relational_Basic_Axiom_Validity.paper_R_bbk_model.paper_R_UI_valid",
    "theorem:Bacon_Source_Relational_Basic_Axiom_Validity.paper_R_bbk_model.paper_R_EG_valid",
    "theorem:Bacon_Source_Relational_Basic_Axiom_Validity.paper_R_bbk_model.paper_R_Ref_valid",
    "theorem:Bacon_Source_Relational_Basic_Axiom_Validity.paper_R_bbk_model.paper_R_LL_valid",
    "theorem:Bacon_Source_Relational_Validity_Rules.paper_R_bbk_model.paper_R_valid_MP",
    "theorem:Bacon_Source_Relational_Validity_Rules.paper_R_bbk_model.paper_R_valid_Gen",
    "theorem:Bacon_Source_Relational_Validity_Rules.paper_R_bbk_model.paper_R_valid_Inst",
    "theorem:Bacon_Source_Relational_Common_H.paper_R_common_MP",
    "theorem:Bacon_Source_Relational_Application_Profile.paper_R_app_profile_on_coherent",
    "theorem:Bacon_Source_Relational_Application_Profile_Action.paper_R_app_profile_on_exponential",
    "theorem:Bacon_Source_Relational_Application_Profile_Action.paper_R_app_profile_on_naturality",
    "theorem:Bacon_Source_Relational_Profile_Subactions.paper_R_app_profile_subaction",
    "theorem:Bacon_Source_Relational_Intension_Tail.paper_R_transported_tail_application",
    "theorem:Bacon_Source_Relational_Intension_Tail.paper_R_intension_transported_tail",
    "theorem:Bacon_Source_Relational_Intensional_Reverse.paper_R_quasi_conditions_imply_intensional",
    "theorem:Bacon_Source_Relational_Intensional_Reverse.paper_R_intensional_iff_quasi_conditions",
    "theorem:Bacon_Source_Relational_Model_Morphism.paper_R_bbk_model_morphism_compose",
    "theorem:Bacon_Source_Relational_Application.paper_R_bbk_model.paper_R_application_graph_exists",
    "theorem:Bacon_Source_Relational_Application.paper_R_bbk_model.paper_R_application_graph_unique",
    "theorem:Bacon_Source_Relational_Application.paper_R_bbk_model.paper_R_application_denote",
    "theorem:Bacon_Source_Relational_Arrows.paper_R_bbk_data_morphism_normalize",
    "theorem:Bacon_Source_Relational_Category.paper_R_bbk_record_category",
    "theorem:Bacon_Source_Relational_Category.paper_R_bbk_type_action",
    "theorem:Bacon_Source_Relational_Model_Normalization.paper_R_bbk_normalize_truth",
    "theorem:Bacon_Source_Relational_Normalization_Validity.paper_R_bbk_normalize_valid",
    "theorem:Bacon_Source_Relational_Application_Morphism.paper_R_application_morphism",
    "theorem:Bacon_Source_Relational_Vector_Application.paper_R_apply_vector_type",
    "theorem:Bacon_Source_Relational_Vector_Application.paper_R_apply_vector_morphism",
    "theorem:Bacon_Source_Relational_Subcategory.paper_R_bbk_subcategory_category",
    "theorem:Bacon_Source_Relational_Category_Interface.paper_R_bbk_normalized_full_subcategory",
    "theorem:Bacon_Source_Relational_Truth_Profile.paper_R_bbk_selected_truth_profile_naturality",
    "theorem:Bacon_Source_Relational_Truth_Profile.paper_R_bbk_truth_profile_subaction",
    "theorem:Bacon_Source_Relational_BBK_Interface.paper_R_bbk_model.paper_R_assignment_undefined_outside",
    "theorem:Bacon_Source_Relational_BBK_Interface.paper_R_bbk_model.paper_R_predicate_domain_nonempty",
)
CLASSICISM_SEMANTIC_REDUCT_ROOTS = (
    "theorem:Bacon_Source_Relational_Model_Restriction.paper_R_model_restriction",
)
# New native R-H consistency groundwork has no semantic or full-F premise.
# Definitions of consistency/maximality must not become backward shortcuts
# in old semantic, representation, code, or unrelated proof certificates.
RELATIONAL_CONSISTENCY_PREDICATES = {
    "paper_R_named_consistent",
    "paper_R_sentence",
    "paper_R_closed_theory",
    "paper_R_closed_maximal_extension",
}
RELATIONAL_H_CORE_ROOTS = (
    "theorem:Bacon_Source_Relational_Deduction.paper_R_named_derivable_deduction",
    "theorem:Bacon_Source_Relational_Deduction.paper_R_named_derivable_deduction_iff",
    "theorem:Bacon_Source_Relational_Explosion.paper_R_named_derivable_explosion",
    "theorem:Bacon_Source_Relational_Explosion.paper_R_named_derivable_reductio",
    "theorem:Bacon_Source_Relational_Consistency.paper_R_named_consistent_finite_character",
    "theorem:Bacon_Source_Relational_Consistency.paper_R_named_consistent_insert_not",
    "theorem:Bacon_Source_Relational_Consequence_Closure.paper_R_named_derivable_cut",
    "theorem:Bacon_Source_Relational_Consequence_Closure.paper_R_named_consistent_insert_derivable",
    "theorem:Bacon_Source_Relational_Consequence_Closure.paper_R_named_consistent_decision_extension",
    "theorem:Bacon_Source_Relational_Lindenbaum.paper_R_named_consistent_chain_Union",
    "theorem:Bacon_Source_Relational_Lindenbaum.paper_R_closed_maximal_extension_exists",
    "theorem:Bacon_Source_Relational_Maximal_Theory.paper_R_closed_maximal_consequence",
    "theorem:Bacon_Source_Relational_Maximal_Theory.paper_R_closed_maximal_membership_iff",
    "theorem:Bacon_Source_Relational_Maximal_Theory.paper_R_closed_maximal_exactly_one",
    "theorem:Bacon_Source_Relational_Existence.paper_R_named_type_existence",
)
RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Henkin_Existential_Membership.paper_R_closed_Henkin_exists_member": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Universal_Membership.paper_R_closed_Henkin_forall_member": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_exists_class": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_forall_class": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_forall_truth": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_exists_truth": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Model.paper_R_identity_bbk_model": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_neg_truth": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_conj_truth": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_disj_truth": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_valuation_identity": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_denote_identity_truth": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_not_member": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_and_member": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_or_member": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_not": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_and": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_or": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_class": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_rep": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_declared_constant": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_identity_domain_nonempty": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_full_premises_closed": {"paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_stage_consistent_full_signature": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_full_premises_consistent": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Closed_Witness_Completeness.paper_R_closed_witness_complete_from_conditionals": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension"},
    "theorem:Bacon_Source_Relational_Closed_Henkin_Theory.paper_R_closed_maximal_Henkin": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension"},
    "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension"},
    "theorem:Bacon_Source_Relational_Constant_Map_Consistency.paper_R_named_consistent_injective_constant_map_iff": {"paper_R_named_consistent"},
    "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_closed": {"paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_original_consistent": {"paper_R_named_consistent"},
    "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_premises_consistent": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Witness_Family_Syntax.paper_R_witness_family_closed_theory": {"paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Finite_Witness_Family.paper_R_named_consistent_finite_witness_family": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Witness_Family_Consistency.paper_R_named_consistent_witness_family": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Witness_Syntax.paper_R_witness_sentence": {"paper_R_sentence"},
    "theorem:Bacon_Source_Relational_Witness_Consistency.paper_R_named_consistent_fresh_witness": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
    "theorem:Bacon_Source_Relational_Local_Signature_Conservativity.paper_R_named_consistent_signature_transport": {"paper_R_named_consistent"},
    "theorem:Bacon_Source_Relational_Consistency.paper_R_named_consistent_finite_character": {"paper_R_named_consistent"},
    "theorem:Bacon_Source_Relational_Consistency.paper_R_named_consistent_insert_not": {"paper_R_named_consistent"},
    "theorem:Bacon_Source_Relational_Consequence_Closure.paper_R_named_consistent_insert_derivable": {"paper_R_named_consistent"},
    "theorem:Bacon_Source_Relational_Consequence_Closure.paper_R_named_consistent_decision_extension": {"paper_R_named_consistent"},
    "theorem:Bacon_Source_Relational_Lindenbaum.paper_R_named_consistent_chain_Union": {"paper_R_named_consistent"},
    "theorem:Bacon_Source_Relational_Lindenbaum.paper_R_closed_maximal_extension_exists": set(RELATIONAL_CONSISTENCY_PREDICATES),
    "theorem:Bacon_Source_Relational_Maximal_Theory.paper_R_closed_maximal_consequence": set(RELATIONAL_CONSISTENCY_PREDICATES),
    "theorem:Bacon_Source_Relational_Maximal_Theory.paper_R_closed_maximal_membership_iff": set(RELATIONAL_CONSISTENCY_PREDICATES),
    "theorem:Bacon_Source_Relational_Maximal_Theory.paper_R_closed_maximal_exactly_one": set(RELATIONAL_CONSISTENCY_PREDICATES),
}


def relational_consistency_forbidden(root):
    return RELATIONAL_CONSISTENCY_PREDICATES - RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST.get(root, set())


# These predicates package universally quantified transformed proofs.
# The three theorem-retraction roots may use only the H proxy. Exact
# local-retraction and witness/stage/extension roots listed below may
# also use the local proxy. Identity roots receive neither allowance.
RELATIONAL_H_RETRACTION_PROXY_PREDICATES = {"paper_R_H_retraction_support", "paper_R_local_retraction_support"}
RELATIONAL_H_RETRACTION_ROOTS = (
    "theorem:Bacon_Source_Relational_H_Retraction.paper_R_named_H_retraction_support",
    "theorem:Bacon_Source_Relational_H_Signature_Conservativity.paper_R_named_H_foreign_constants_eliminate",
    "theorem:Bacon_Source_Relational_H_Signature_Conservativity.paper_R_named_H_signature_iff",
)


RELATIONAL_H_LOCAL_RETRACTION_ROOTS = (
    "theorem:Bacon_Source_Relational_Local_Retraction.paper_R_named_derivable_retraction_support",
    "theorem:Bacon_Source_Relational_Local_Signature_Conservativity.paper_R_named_derivable_foreign_constants_eliminate",
    "theorem:Bacon_Source_Relational_Local_Signature_Conservativity.paper_R_named_derivable_signature_iff",
    "theorem:Bacon_Source_Relational_Local_Signature_Conservativity.paper_R_named_consistent_signature_transport",
)
RELATIONAL_H_IDENTITY_ROOTS = (
    "theorem:Bacon_Source_Relational_Conversion_Identity_Steps.paper_R_named_H_beta_identity",
    "theorem:Bacon_Source_Relational_Conversion_Identity_Steps.paper_R_named_H_eta_identity",
    "theorem:Bacon_Source_Relational_Conversion_Identity.paper_R_named_H_raw_conversion_identity",
    "theorem:Bacon_Source_Relational_Application_Congruence.paper_R_named_identity_App_argument",
    "theorem:Bacon_Source_Relational_Application_Congruence.paper_R_named_identity_App_head",
    "theorem:Bacon_Source_Relational_Application_Congruence.paper_R_named_identity_App",
    "theorem:Bacon_Source_Relational_Identity_Proof_Basics.paper_R_named_derivable_beta_iff",
    "theorem:Bacon_Source_Relational_Identity_Derivations.paper_R_named_identity_refl",
    "theorem:Bacon_Source_Relational_Identity_Derivations.paper_R_named_identity_sym",
    "theorem:Bacon_Source_Relational_Identity_Derivations.paper_R_named_identity_trans",
)
RELATIONAL_RETRACTION_PROXY_ROOT_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_stage_consistent_full_signature": set(RELATIONAL_H_RETRACTION_PROXY_PREDICATES),
    "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_full_premises_consistent": set(RELATIONAL_H_RETRACTION_PROXY_PREDICATES),
    "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists": set(RELATIONAL_H_RETRACTION_PROXY_PREDICATES),
    "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_premises_consistent": set(RELATIONAL_H_RETRACTION_PROXY_PREDICATES),
    "theorem:Bacon_Source_Relational_Finite_Witness_Family.paper_R_named_consistent_finite_witness_family": set(RELATIONAL_H_RETRACTION_PROXY_PREDICATES),
    "theorem:Bacon_Source_Relational_Witness_Family_Consistency.paper_R_named_consistent_witness_family": set(RELATIONAL_H_RETRACTION_PROXY_PREDICATES),
    "theorem:Bacon_Source_Relational_Witness_Consistency.paper_R_named_consistent_fresh_witness": set(RELATIONAL_H_RETRACTION_PROXY_PREDICATES),
    **{root: {"paper_R_H_retraction_support"} for root in RELATIONAL_H_RETRACTION_ROOTS},
    **{root: set(RELATIONAL_H_RETRACTION_PROXY_PREDICATES) for root in RELATIONAL_H_LOCAL_RETRACTION_ROOTS},
}


def relational_retraction_proxy_forbidden(root):
    return RELATIONAL_H_RETRACTION_PROXY_PREDICATES - RELATIONAL_RETRACTION_PROXY_ROOT_ALLOWLIST.get(root, set())


# Witness constructors and derivable-identity classes are new proof data,
# not model assumptions. Keep them isolated from older certificates.
RELATIONAL_H_WITNESS_ROOTS = (
    "theorem:Bacon_Source_Relational_Witness_Family_Syntax.paper_R_witness_family_closed_theory",
    "theorem:Bacon_Source_Relational_Finite_Witness_Family.paper_R_named_consistent_finite_witness_family",
    "theorem:Bacon_Source_Relational_Witness_Family_Consistency.paper_R_named_consistent_witness_family",
    "theorem:Bacon_Source_Relational_Local_Exchange.paper_R_named_derivable_empty_iff",
    "theorem:Bacon_Source_Relational_Local_Inst.paper_R_named_derivable_Inst",
    "theorem:Bacon_Source_Relational_Witness_Syntax.paper_R_witness_sentence",
    "theorem:Bacon_Source_Relational_Witness_Syntax.paper_R_witness_retract",
    "theorem:Bacon_Source_Relational_Witness_Propositional.paper_R_named_derivable_not_intro",
    "theorem:Bacon_Source_Relational_Witness_Consistency.paper_R_named_consistent_fresh_witness",
)
RELATIONAL_H_IDENTITY_CLASS_ROOTS = (
    "theorem:Bacon_Source_Relational_Identity_Representatives.paper_R_identity_class_rep",
    "theorem:Bacon_Source_Relational_Identity_Application.paper_R_identity_application_domain",
    "theorem:Bacon_Source_Relational_Identity_Application.paper_R_identity_application_classes",
    "theorem:Bacon_Source_Relational_Identity_Application.paper_R_identity_application_representatives",
    "theorem:Bacon_Source_Relational_Identity_Class_Relation.paper_R_identity_relation_equiv",
    "theorem:Bacon_Source_Relational_Identity_Classes.paper_R_identity_class_eq_iff",
    "theorem:Bacon_Source_Relational_Identity_Classes.paper_R_identity_value_nonempty",
    "theorem:Bacon_Source_Relational_Identity_Classes.paper_R_identity_domains_disjoint",
)
RELATIONAL_WITNESS_SYNTAX_CONSTANTS = {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"}
RELATIONAL_IDENTITY_CLASS_PREDICATES = {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"}
RELATIONAL_WITNESS_SYNTAX_ROOT_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_full_premises_closed": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_finite_premises_stage_bound": {"paper_R_witness_axiom", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_stage_consistent_full_signature": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_full_premises_consistent": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Henkin_Witness_Coverage.paper_R_henkin_full_witness_axiom": {"paper_R_witness_axiom", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Closed_Witness_Completeness.paper_R_closed_witness_complete_from_conditionals": {"paper_R_witness_axiom"},
    "theorem:Bacon_Source_Relational_Closed_Henkin_Theory.paper_R_closed_maximal_Henkin": {"paper_R_witness_axiom"},
    "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Henkin_Stage_Signature.paper_R_henkin_signature_family": {"paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_mono": {"paper_R_witness_axiom", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_closed": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_original_consistent": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_premises_consistent": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Witness_Family_Syntax.paper_R_witness_family_closed_theory": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Finite_Witness_Family.paper_R_named_consistent_finite_witness_family": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Witness_Family_Consistency.paper_R_named_consistent_witness_family": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
    "theorem:Bacon_Source_Relational_Witness_Syntax.paper_R_witness_sentence": {"paper_R_add_constant", "paper_R_witness_axiom"},
    "theorem:Bacon_Source_Relational_Witness_Syntax.paper_R_witness_retract": {"paper_R_add_constant", "paper_R_witness_axiom"},
    "theorem:Bacon_Source_Relational_Witness_Consistency.paper_R_named_consistent_fresh_witness": {"paper_R_add_constant", "paper_R_witness_axiom"},
}
RELATIONAL_IDENTITY_CLASS_ROOT_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_Environment_Finite_Identity.paper_R_environment_subst_assignment_identity": {"paper_R_closed_terms"},
    "theorem:Bacon_Source_Relational_Arbitrary_Representatives.paper_R_identity_denote_arbitrary_representatives": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Identity_Countable_Domains.paper_R_identity_domains_countable": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain"},
    "theorem:Bacon_Source_Relational_Environment_Update_Identity.paper_R_environment_subst_update_identity": {"paper_R_closed_terms"},
    "theorem:Bacon_Source_Relational_Henkin_Existential_Membership.paper_R_closed_Henkin_exists_member": {"paper_R_closed_terms"},
    "theorem:Bacon_Source_Relational_Henkin_Universal_Membership.paper_R_closed_Henkin_forall_member": {"paper_R_closed_terms"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_exists_class": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_forall_class": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
    "theorem:Bacon_Source_Relational_Identity_Fresh_Application.paper_R_identity_denote_fresh_application": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_forall_truth": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
    "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_exists_truth": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
    "theorem:Bacon_Source_Relational_Identity_Model.paper_R_identity_bbk_model": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
    "theorem:Bacon_Source_Relational_Environment_Conversion.paper_R_environment_subst_raw_conversion": {"paper_R_closed_terms"},
    "theorem:Bacon_Source_Relational_Identity_Conversion.paper_R_identity_denote_beta_eta": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_neg_truth": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_conj_truth": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_disj_truth": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_valuation_identity": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class"},
    "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_denote_identity_truth": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Identity_Application_Congruence.paper_R_identity_denote_application_cong": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
    "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_not_member": {"paper_R_closed_terms"},
    "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_and_member": {"paper_R_closed_terms"},
    "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_or_member": {"paper_R_closed_terms"},
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_not": {"paper_R_closed_terms", "paper_R_identity_class"},
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_and": {"paper_R_closed_terms", "paper_R_identity_class"},
    "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_or": {"paper_R_closed_terms", "paper_R_identity_class"},
    "theorem:Bacon_Source_Relational_Representative_Assignments.paper_R_representative_assignment_domain": {"paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Representative_Assignments.paper_R_representative_assignment_typed": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Environment_Substitution_Typing.paper_R_representative_substitution_closed_terms": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Propositional_Identity_Derivations.paper_R_closed_propositional_identity_membership": {"paper_R_closed_terms"},
    "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_class": {"paper_R_closed_terms", "paper_R_identity_class"},
    "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_rep": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_type": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_var": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_locality": {"paper_R_identity_class", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_App": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
    "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_identity_domain_nonempty": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain"},
    "theorem:Bacon_Source_Relational_Identity_Representatives.paper_R_identity_class_rep": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
    "theorem:Bacon_Source_Relational_Identity_Application.paper_R_identity_application_domain": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
    "theorem:Bacon_Source_Relational_Identity_Application.paper_R_identity_application_classes": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
    "theorem:Bacon_Source_Relational_Identity_Application.paper_R_identity_application_representatives": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
    "theorem:Bacon_Source_Relational_Identity_Class_Relation.paper_R_identity_relation_equiv": {"paper_R_closed_terms", "paper_R_identity_relation"},
    "theorem:Bacon_Source_Relational_Identity_Classes.paper_R_identity_class_eq_iff": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class"},
    "theorem:Bacon_Source_Relational_Identity_Classes.paper_R_identity_value_nonempty": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain"},
    "theorem:Bacon_Source_Relational_Identity_Classes.paper_R_identity_domains_disjoint": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain"},
}


def relational_witness_class_forbidden(root):
    return ((RELATIONAL_WITNESS_SYNTAX_CONSTANTS - RELATIONAL_WITNESS_SYNTAX_ROOT_ALLOWLIST.get(root, set()))
            | (RELATIONAL_IDENTITY_CLASS_PREDICATES - RELATIONAL_IDENTITY_CLASS_ROOT_ALLOWLIST.get(root, set())))


RELATIONAL_H_CONSTANT_MAP_ROOTS = (
    "theorem:Bacon_Source_Relational_H_Constant_Map.paper_R_named_H_constant_map",
)
RELATIONAL_H_PROOF_ROOTS = (
    *RELATIONAL_TERM_ENV_PROOF_ROOTS,
    *RELATIONAL_HENKIN_PROOF_ROOTS,
    *RELATIONAL_H_CONSTANT_MAP_ROOTS,
    *RELATIONAL_H_WITNESS_ROOTS,
    *RELATIONAL_H_IDENTITY_CLASS_ROOTS,
    *RELATIONAL_H_LOCAL_RETRACTION_ROOTS,
    *RELATIONAL_H_IDENTITY_ROOTS,
    *RELATIONAL_H_RETRACTION_ROOTS,
    *RELATIONAL_H_CORE_ROOTS,
    "theorem:Bacon_Source_Relational_H.paper_R_named_H_language",
    "theorem:Bacon_Source_Relational_H_Embedding.paper_R_named_H_embedding",
    "theorem:Bacon_Source_Relational_Local_Consequence.paper_R_named_derivable_finite_support",
)
CLASSICISM_SEMANTIC_R_SOUNDNESS_ROOTS = (
    "theorem:Bacon_Source_Relational_Local_Validity.paper_R_bbk_model.paper_R_named_derivable_valid",
    "theorem:Bacon_Source_Relational_H_Soundness.paper_R_bbk_model.paper_R_named_H_soundness",
    "theorem:Bacon_Source_Relational_Common_H.paper_R_common_contains_H",
    "theorem:Bacon_Source_Relational_Local_Soundness.paper_R_bbk_model.paper_R_named_derivable_soundness",
    "theorem:Bacon_Source_Relational_Local_Soundness.paper_R_bbk_model.paper_R_named_derivable_finite_semantic_support",
)
RELATIONAL_C_PROOF_ROOTS = (
    "theorem:Bacon_Source_Relational_Equivalence_Presentation.paper_R_equivalence_proves_language",
    "theorem:Bacon_Source_Relational_Equivalence_Presentation.paper_R_equivalence_propositional",
    "theorem:Bacon_Source_Relational_Classicism_Presentation.paper_R_classicism_proves_language",
    "theorem:Bacon_Source_Relational_Classicism_Presentation.paper_R_classicism_into_equivalence",
)
CLASSICISM_SEMANTIC_R_C_SOUNDNESS_ROOTS = (
    "theorem:Bacon_Source_Relational_Equivalence_Soundness.paper_R_equivalence_category_soundness",
    "theorem:Bacon_Source_Relational_Classicism_Soundness.paper_R_classicism_category_soundness",
)
# The direct five-constructor C proof must not import the separate
# Equivalence-rule presentation or an unproved converse to that presentation.
CLASSICISM_SEMANTIC_R_DIRECT_C_ROOTS = (
    "theorem:Bacon_Source_Relational_Classicism_BBK_Soundness.paper_R_bbk_model.paper_R_classicism_BBK_soundness",
)
CLASSICISM_SEMANTIC_ROOTS = (
    CLASSICISM_SEMANTIC_RAW_ROOTS + CLASSICISM_SEMANTIC_MODEL_ROOTS
    + CLASSICISM_SEMANTIC_R_ROOTS + CLASSICISM_SEMANTIC_REDUCT_ROOTS
    + CLASSICISM_SEMANTIC_R_SOUNDNESS_ROOTS
    + CLASSICISM_SEMANTIC_R_C_SOUNDNESS_ROOTS + CLASSICISM_SEMANTIC_R_DIRECT_C_ROOTS
)


def classicism_semantic_forbidden(root, model_predicates):
    if root in RELATIONAL_H_PROOF_ROOTS or root in RELATIONAL_C_PROOF_ROOTS:
        # Independent R syntax/local-proof facts exclude semantic shortcuts.
        # The explicit one-way embedding alone permits full-F theoremhood.
        forbidden = set(model_predicates) | {"C_proves", "CE_proves", "CEV_proves"}
        if (root in RELATIONAL_H_CORE_ROOTS or root in RELATIONAL_H_RETRACTION_ROOTS
                or root in RELATIONAL_H_LOCAL_RETRACTION_ROOTS or root in RELATIONAL_H_IDENTITY_ROOTS
                or root in RELATIONAL_H_WITNESS_ROOTS or root in RELATIONAL_H_IDENTITY_CLASS_ROOTS
                or root in RELATIONAL_H_CONSTANT_MAP_ROOTS or root in RELATIONAL_HENKIN_PROOF_ROOTS
                or root in RELATIONAL_TERM_ENV_PROOF_ROOTS):
            forbidden |= (ZF_PROOF_PREDICATES - {"paper_R_named_H", "paper_R_named_derivable"}
                          - RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST.get(root, set())
                          - RELATIONAL_RETRACTION_PROXY_ROOT_ALLOWLIST.get(root, set())
                          - RELATIONAL_WITNESS_SYNTAX_ROOT_ALLOWLIST.get(root, set())
                          - RELATIONAL_IDENTITY_CLASS_ROOT_ALLOWLIST.get(root, set())
                          - RELATIONAL_HENKIN_DATA_ROOT_ALLOWLIST.get(root, set())
                          - RELATIONAL_CLOSED_HENKIN_ROOT_ALLOWLIST.get(root, set())
                          - RELATIONAL_TERM_ENV_ROOT_ALLOWLIST.get(root, set())
                          - RELATIONAL_REP_CHOICE_ROOT_ALLOWLIST.get(root, set()))
            forbidden |= ZF_FOREIGN_MODEL_PREDICATES | ZF_INDEPENDENT_R_MODEL_PREDICATES
        if not root.endswith(".paper_R_named_H_embedding"):
            forbidden |= {"paper_named_H", "paper_named_derivable", "paper_global_H", "pH_proves", "H_proves"}
        return forbidden
    if root not in CLASSICISM_SEMANTIC_ROOTS:
        return set()
    forbidden = BOOK_CONJUNCTION_PROOF_PREDICATES | {
        "H_proves", "H_derivable", "H_set_derivable", "H_signature_proves",
        "pH_proves", "pH_set_derivable", "pH_consistent", "paper_global_H",
        "paper_global_derivable", "paper_global_consistent", "paper_named_H",
        "paper_named_derivable", "paper_named_consistent", "C_proves",
        "CE_proves", "CEV_proves", "HE_proves", "HLE_proves",
    }
    if (root not in CLASSICISM_SEMANTIC_R_SOUNDNESS_ROOTS
            and root not in CLASSICISM_SEMANTIC_R_C_SOUNDNESS_ROOTS
            and root not in CLASSICISM_SEMANTIC_R_DIRECT_C_ROOTS):
        forbidden |= {"paper_R_named_H", "paper_R_named_derivable"}
    allowed_models = set()
    if root in CLASSICISM_SEMANTIC_MODEL_ROOTS or root in CLASSICISM_SEMANTIC_REDUCT_ROOTS:
        allowed_models |= {"paper_named_bbk_model", "paper_named_bbk_model_axioms"}
    if (root in CLASSICISM_SEMANTIC_R_ROOTS or root in CLASSICISM_SEMANTIC_REDUCT_ROOTS
            or root in CLASSICISM_SEMANTIC_R_SOUNDNESS_ROOTS
            or root in CLASSICISM_SEMANTIC_R_C_SOUNDNESS_ROOTS
            or root in CLASSICISM_SEMANTIC_R_DIRECT_C_ROOTS):
        allowed_models |= {"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
    if root in CLASSICISM_SEMANTIC_R_DIRECT_C_ROOTS:
        forbidden |= {"paper_R_equivalence_proves"}
    return forbidden | (set(model_predicates) - allowed_models)


ZF_REPRESENTATION_ROOTS = (
    "theorem:Bacon_Source_ZF_Action_BBK_Logical_Application.paper_ZF_action_bbk_denote_logical",
    "theorem:Bacon_Source_ZF_Action_BBK_Interpretation.paper_ZF_action_bbk_denote_locality",
    "theorem:Bacon_Source_ZF_Evaluation_Contexts.paper_ZF_action_abstract_cong",
    "theorem:Bacon_Source_ZF_Evaluation_Contexts.paper_ZF_action_eval_compatible",
    "theorem:Bacon_Source_ZF_Exponential_Identity_Application.paper_ZF_Pi_as_application_graph",
    "theorem:Bacon_Source_ZF_Action_BBK_Domains.paper_ZF_action_bbk_env_iff",
    "theorem:Bacon_Source_ZF_Premodel_Naturality_Regression.paper_ZF_degenerate_regression_guards",
    "theorem:Bacon_Source_ZF_Premodel_Naturality_Regression.paper_ZF_degenerate_totalized_naturality_fails",
    "theorem:Bacon_Source_ZF_Premodel_Naturality_Regression.paper_ZF_degenerate_partial_transport_undefined",
    "theorem:Bacon_Source_ZF_Logical_Naturality.paper_ZF_pair_lambda_target_naturality",
    "theorem:Bacon_Source_ZF_Logical_Naturality.paper_ZF_logical_value_precompose",
    "theorem:Bacon_Source_ZF_Assignment_Transport_Laws.paper_ZF_action_assignment_transport_identity",
    "theorem:Bacon_Source_ZF_Assignment_Transport_Laws.paper_ZF_action_assignment_transport_compose",
    "theorem:Bacon_Source_ZF_Premodel_Application_Naturality.paper_ZF_exponential_transport_apply",
    "theorem:Bacon_Source_ZF_Evaluation_Locality.paper_ZF_action_eval_locality",
    "theorem:Bacon_Source_ZF_Graph_Application.paper_ZF_graph_apply_Some_iff",
    "theorem:Bacon_Source_ZF_Graph_Application.paper_ZF_graph_apply_None_iff",
    "theorem:Bacon_Source_ZF_Graph_Application.paper_ZF_graph_apply_defined_value",
    "theorem:Bacon_Source_ZF_Logical_Value_Evaluation.paper_ZF_logical_not_apply",
    "theorem:Bacon_Source_ZF_Logical_Value_Evaluation.paper_ZF_logical_and_apply",
    "theorem:Bacon_Source_ZF_Logical_Value_Evaluation.paper_ZF_logical_or_apply",
    "theorem:Bacon_Source_ZF_Logical_Value_Evaluation.paper_ZF_logical_forall_apply",
    "theorem:Bacon_Source_ZF_Logical_Value_Evaluation.paper_ZF_logical_exists_apply",
    "theorem:Bacon_Source_ZF_Logical_Value_Evaluation.paper_ZF_logical_identity_apply",
    "theorem:Bacon_Source_ZF_Logical_Value_Evaluation.paper_ZF_logical_quantifier_test_type",
    "theorem:Bacon_Source_ZF_Partial_Abstraction.paper_ZF_action_abstract_defined",
    "theorem:Bacon_Source_ZF_Partial_Abstraction.paper_ZF_action_abstract_None_iff",
    "theorem:Bacon_Source_ZF_Partial_Abstraction.paper_ZF_action_abstract_graph",
    "theorem:Bacon_Source_ZF_Partial_Abstraction.paper_ZF_action_abstract_apply",
    "theorem:Bacon_Source_ZF_Partial_Interpretation.paper_ZF_action_eval_application_Some_iff",
    "theorem:Bacon_Source_ZF_Partial_Interpretation.paper_ZF_action_eval_abstraction_apply",
    "theorem:Bacon_Source_ZF_Partial_Interpretation.paper_ZF_action_eval_abstraction_None_iff",
    "theorem:Bacon_Source_ZF_Premodel_Evaluation.paper_ZF_action_eval_variable_typed",
    "theorem:Bacon_Source_ZF_Action_Assignments.paper_ZF_action_transport_env_typed",
    "theorem:Bacon_Source_ZF_Rooted_Category_Encoding.paper_ZF_category_encoding.paper_ZF_root_arrows_bijection",
    "theorem:Bacon_Source_ZF_Rooted_Category_Encoding.paper_ZF_category_encoding.paper_ZF_encoded_rooted_category",
    "theorem:Bacon_Source_ZF_R_Representation_Assignment_Syntax.paper_ZF_R_encode_assignment_domain",
    "theorem:Bacon_Source_ZF_R_Representation_Assignment_Syntax.paper_ZF_R_decode_assignment_domain",
    "theorem:Bacon_Source_ZF_R_Representation_Assignment_Syntax.paper_ZF_R_encode_assignment_adequate_iff",
    "theorem:Bacon_Source_ZF_R_Representation_Assignment_Syntax.paper_ZF_R_decode_assignment_adequate_iff",
    "theorem:Bacon_Source_ZF_R_Representation_Assignment_Syntax.paper_ZF_R_type_representation_domain_nonR",
    "theorem:Bacon_Source_ZF_R_Type_Recursion.paper_ZF_R_type_representation_Ind_encode",
    "theorem:Bacon_Source_ZF_R_Type_Recursion.paper_ZF_R_type_representation_Prop_domain",
    "theorem:Bacon_Source_ZF_R_Type_Recursion.paper_ZF_R_arrow_encode_value",
    "theorem:Bacon_Source_ZF_R_Type_Invariant.paper_ZF_R_type_invariant_decode_encode",
    "theorem:Bacon_Source_ZF_R_Type_Invariant.paper_ZF_R_type_invariant_encode_decode",
    "theorem:Bacon_Source_ZF_R_Type_Invariant.paper_ZF_R_type_invariant_inverse_map",
    "theorem:Bacon_Source_ZF_Identity_Individual_Base.paper_ZF_identity_fiber_elements",
    "theorem:Bacon_Source_ZF_Identity_Individual_Base.paper_ZF_identity_base_bijection",
    "theorem:Bacon_Source_ZF_Identity_Individual_Base.paper_ZF_identity_base_action",
    "theorem:Bacon_Source_ZF_Range_Carriers.paper_ZF_range_code_explode",
    "theorem:Bacon_Source_ZF_Range_Carriers.paper_ZF_range_fiber_bijection",
    "theorem:Bacon_Source_ZF_Range_Carriers.paper_ZF_range_decode_encode",
    "theorem:Bacon_Source_ZF_Range_Carriers.paper_ZF_range_encode_decode",
    "theorem:Bacon_Source_ZF_Range_Action.paper_ZF_range_action",
    "theorem:Bacon_Source_ZF_Range_Action.paper_ZF_range_subaction",
    "theorem:Bacon_Source_ZF_Range_Action.paper_ZF_range_forward_action_map",
    "theorem:Bacon_Source_ZF_Range_Action.paper_ZF_range_inverse_action_map",
    "theorem:Bacon_Source_ZF_Powerset_Reindexing.paper_ZF_category_encoding.paper_ZF_powerset_reindex",
    "theorem:Bacon_Source_ZF_Dependent_Pairs.paper_ZF_sigma_bijection",
    "theorem:Bacon_Source_ZF_Dependent_Pairs.paper_ZF_sigma_projections",
    "theorem:Bacon_Source_ZF_Dependent_Function_Graphs.paper_ZF_dependent_function_graph_bijection",
    "theorem:Bacon_Source_ZF_Dependent_Function_Graphs.paper_ZF_decode_encode_dependent_function",
    "theorem:Bacon_Source_ZF_Dependent_Function_Graphs.paper_ZF_encode_decode_dependent_function",
    "theorem:Bacon_Source_ZF_Embedded_Carriers.paper_ZF_image_code_bijection",
    "theorem:Bacon_Source_ZF_Embedded_Carriers.paper_ZF_image_inverse_bijection",
    "theorem:Bacon_Source_ZF_Embedded_Carriers.paper_ZF_identity_object_encoding",
    "theorem:Bacon_Source_ZF_Outgoing_Pairs.paper_ZF_pair_code_bijection",
    "theorem:Bacon_Source_ZF_Pair_Function_Graphs.paper_ZF_pair_function_graph_bijection",
    "theorem:Bacon_Source_ZF_Pair_Function_Graphs.paper_ZF_decode_encode_pair_function",
    "theorem:Bacon_Source_ZF_Pair_Function_Graphs.paper_ZF_encode_decode_pair_function",
    "theorem:Bacon_Source_ZF_Exponential_Codec.paper_ZF_action_pair.paper_ZF_exponential_code_bijection",
    "theorem:Bacon_Source_ZF_Exponential_Codec.paper_ZF_action_pair.paper_ZF_decode_encode_exponential",
    "theorem:Bacon_Source_ZF_Exponential_Codec.paper_ZF_action_pair.paper_ZF_encode_decode_exponential",
    "theorem:Bacon_Source_ZF_Exponential_Codec.paper_ZF_action_pair.paper_ZF_encode_exponential_type",
    "theorem:Bacon_Source_ZF_Exponential_Codec.paper_ZF_action_pair.paper_ZF_decode_exponential_type",
    "theorem:Bacon_Source_ZF_Pair_Transport.paper_ZF_pair_precompose",
    "theorem:Bacon_Source_ZF_Pair_Transport.paper_ZF_pair_advance",
    "theorem:Bacon_Source_ZF_Exponential_Transport.paper_ZF_encode_exponential_transport",
    "theorem:Bacon_Source_ZF_Exponential_Transport.paper_ZF_action_pair.paper_ZF_decode_exponential_transport",
    "theorem:Bacon_Source_ZF_Exponential_Action.paper_ZF_action_pair.paper_ZF_exponential_action",
    "theorem:Bacon_Source_ZF_Powerset_Coding.paper_ZF_powerset_fiber_bijection",
    "theorem:Bacon_Source_ZF_Powerset_Action.paper_ZF_decode_powerset_transport",
    "theorem:Bacon_Source_ZF_Powerset_Action.paper_ZF_powerset_action",
    "theorem:Bacon_Source_ZF_Individual_Action.paper_ZF_individual_fiber_bijection",
    "theorem:Bacon_Source_ZF_Individual_Action.paper_ZF_individual_action",
    "theorem:Bacon_Source_ZF_Individual_Action.paper_ZF_individual_decode_transport_on_fiber",
    "theorem:Bacon_Source_ZF_Individual_Action.paper_ZF_individual_fiber_nonempty",
    "theorem:Bacon_Source_ZF_Encoded_Category.paper_ZF_recode_category",
    "theorem:Bacon_Source_ZF_Reindexed_Action.paper_ZF_reindex_action",
    "theorem:Bacon_Source_ZF_Function_Graphs.paper_ZF_encode_function_type",
    "theorem:Bacon_Source_ZF_Function_Graphs.paper_ZF_decode_function_type",
    "theorem:Bacon_Source_ZF_Function_Graphs.paper_ZF_decode_encode_function",
    "theorem:Bacon_Source_ZF_Function_Graphs.paper_ZF_encode_decode_function",
    "theorem:Bacon_Source_ZF_Function_Graphs.paper_ZF_function_graph_bijection",
    "theorem:Bacon_Source_ZF_Subset_Carriers.paper_ZF_decode_encode_subset",
    "theorem:Bacon_Source_ZF_Subset_Carriers.paper_ZF_encode_decode_subset",
    "theorem:Bacon_Source_ZF_Subset_Carriers.paper_ZF_subset_carrier_bijection",
)

# Generic deductions from an independently supplied premodel. They may
# use that predicate, but neither R/F BBK models nor an action-model or
# totality predicate. The variable case above needs no premodel at all.
ZF_PREMODEL_DEDUCTION_ROOTS = (
    "theorem:Bacon_Source_ZF_Proposition_Transport.paper_ZF_premodel_proposition_member",
    "theorem:Bacon_Source_ZF_Proposition_Transport.paper_ZF_premodel_proposition_transport_test",
    "theorem:Bacon_Source_ZF_Model_Vector_Equality.paper_ZF_premodel_vector_equality",
    "theorem:Bacon_Source_ZF_Model_Evaluation_Contexts.paper_ZF_premodel_eval_compatible",
    "theorem:Bacon_Source_ZF_Exponential_Identity_Application.paper_ZF_premodel_transport_identity_application",
    "theorem:Bacon_Source_ZF_Assignment_Transport_Laws.paper_ZF_premodel_assignment_transport_identity",
    "theorem:Bacon_Source_ZF_Assignment_Transport_Laws.paper_ZF_premodel_assignment_transport_compose",
    "theorem:Bacon_Source_ZF_Premodel_Application_Naturality.paper_ZF_premodel_application_naturality",
    "theorem:Bacon_Source_ZF_Abstraction_Naturality.paper_ZF_action_abstract_naturality",
    "theorem:Bacon_Source_ZF_Abstraction_Naturality.paper_ZF_premodel_eval_Lam_naturality",
    "theorem:Bacon_Source_ZF_Model_Logical_Naturality.paper_ZF_premodel_logical_naturality",
    "theorem:Bacon_Source_ZF_Premodel_Application.paper_ZF_premodel_application_info",
    "theorem:Bacon_Source_ZF_Premodel_Evaluation.paper_ZF_action_eval_constant_typed",
    "theorem:Bacon_Source_ZF_Premodel_Evaluation.paper_ZF_action_eval_application_typed",
)

# These constructions use independently validated R models, unlike the
# generic set/function codecs above. HOL-ZF is allowed only for these exact
# roots; this is not a relaxation of the pure-HOL certificate boundary.
# These roots reason from the independent action-model criterion, not from
# a BBK representation or the constructed-model existence theorem.
ZF_ACTION_MODEL_DEDUCTION_ROOTS = (
    "theorem:Bacon_Source_ZF_Model_Vector_Identity.paper_ZF_action_model_uniform_truth_vector_identity",
    "theorem:Bacon_Source_ZF_Model_Truth_Separation.paper_ZF_action_model_formula_outgoing_truth",
    "theorem:Bacon_Source_ZF_Model_Truth_Separation.paper_ZF_action_model_uniform_truth_equal",
    "theorem:Bacon_Source_ZF_Action_BBK_Logical_Application.paper_ZF_action_bbk_unary_logical_denote",
    "theorem:Bacon_Source_ZF_Action_BBK_Logical_Application.paper_ZF_action_bbk_binary_logical_denote",
    "theorem:Bacon_Source_ZF_Action_BBK_Quantifier_Truth.paper_ZF_action_bbk_fresh_predicate_test",
    "theorem:Bacon_Source_ZF_Action_BBK_Propositional_Truth.paper_ZF_action_bbk_valuation_neg",
    "theorem:Bacon_Source_ZF_Action_BBK_Propositional_Truth.paper_ZF_action_bbk_valuation_conj",
    "theorem:Bacon_Source_ZF_Action_BBK_Propositional_Truth.paper_ZF_action_bbk_valuation_disj",
    "theorem:Bacon_Source_ZF_Action_BBK_Identity_Truth.paper_ZF_action_bbk_valuation_identity",
    "theorem:Bacon_Source_ZF_Action_BBK_Quantifier_Truth.paper_ZF_action_bbk_valuation_forall",
    "theorem:Bacon_Source_ZF_Action_BBK_Quantifier_Truth.paper_ZF_action_bbk_valuation_exists",
    "theorem:Bacon_Source_ZF_Model_Vector_Equality.paper_ZF_action_model_uniform_truth_vector_equal",
    "theorem:Bacon_Source_ZF_Action_BBK_Model.paper_ZF_action_bbk_denote_beta_eta",
    "theorem:Bacon_Source_ZF_Model_Conversion_Steps.paper_ZF_action_model_beta_step",
    "theorem:Bacon_Source_ZF_Model_Conversion_Steps.paper_ZF_action_model_eta_step",
    "theorem:Bacon_Source_ZF_Model_Signature_Conversion.paper_ZF_action_model_signature_conversion_total",
    "theorem:Bacon_Source_ZF_Model_Conversion.paper_ZF_action_model_signature_conversion",
    "theorem:Bacon_Source_ZF_Model_Conversion.paper_ZF_action_model_raw_conversion",
    "theorem:Bacon_Source_ZF_Action_BBK_Interpretation.paper_ZF_action_bbk_denote_total",
    "theorem:Bacon_Source_ZF_Action_BBK_Interpretation.paper_ZF_action_bbk_denote_application_data",
    "theorem:Bacon_Source_ZF_Action_BBK_Interpretation.paper_ZF_action_bbk_denote_application_cong",
    "theorem:Bacon_Source_ZF_Action_BBK_Interpretation.paper_ZF_action_bbk_holds_iff",
    "theorem:Bacon_Source_ZF_Model_Substitution.paper_ZF_action_model_substitution",
    "theorem:Bacon_Source_ZF_Model_Beta_Conversion.paper_ZF_action_model_beta",
    "theorem:Bacon_Source_ZF_Model_Eta_Conversion.paper_ZF_action_model_eta",
    "theorem:Bacon_Source_ZF_Action_Model_Nonempty.paper_ZF_action_model_value_at_object",
    "theorem:Bacon_Source_ZF_Action_Model_Nonempty.paper_ZF_action_model_R_domain_nonempty",
    "theorem:Bacon_Source_ZF_Action_BBK_Domains.paper_ZF_action_bbk_domain_nonempty",
    "theorem:Bacon_Source_ZF_Model_Logical_Naturality.paper_ZF_action_model_logical_value_member",
    "theorem:Bacon_Source_ZF_Model_Logical_Naturality.paper_ZF_action_model_logical_naturality",
    "theorem:Bacon_Source_ZF_Model_Evaluation_Naturality.paper_ZF_action_model_eval_naturality",
)

# Exact construction/regression certificates for the genuine degenerate
# premodel. Only the premodel predicate is allowed at these two roots.
ZF_PREMODEL_REGRESSION_ROOTS = (
    "theorem:Bacon_Source_ZF_Degenerate_Premodel.paper_ZF_degenerate_premodel",
    "theorem:Bacon_Source_ZF_Premodel_Naturality_Regression.paper_ZF_premodel_defined_value_need_not_be_selected",
)

# Exact reverse construction: a supplied ActionModel yields an independent
# R BBK model. The R predicate is a CONCLUSION, not a source-model premise.
# This tier is disjoint from both generic deductions and R-source inputs.
ZF_ACTION_TO_R_MODEL_ROOTS = (
    "theorem:Bacon_Source_ZF_Action_BBK_Model.paper_ZF_action_to_R_bbk_model",
)
ZF_REVERSE_MODEL_CONCLUSION_ALLOWLIST = {
    "theorem:Bacon_Source_ZF_Action_BBK_Model.paper_ZF_action_to_R_bbk_model": {"paper_R_bbk_model"},
}

# These exact C7-chain roots apply native R-H soundness to the DERIVED
# R-BBK model of a supplied action model. No F-H or C judgment is allowed.
ZF_NATIVE_R_H_MODEL_ROOTS = (
    "theorem:Bacon_Source_ZF_Action_BBK_Representation.paper_ZF_action_bbk_logical_equivalence_valid",
    "theorem:Bacon_Source_ZF_Action_BBK_Representation.paper_ZF_action_bbk_representation",
    "theorem:Bacon_Source_ZF_Action_H_Soundness.paper_ZF_action_model_H_truth",
    "theorem:Bacon_Source_ZF_Action_H_Soundness.paper_ZF_action_model_H_iff_truth",
    "theorem:Bacon_Source_ZF_Action_Logical_Equivalence.paper_ZF_action_model_logical_equivalence",
    "theorem:Bacon_Source_ZF_Action_Logical_Equivalence.paper_ZF_action_model_logical_equivalence_at_assignment",
)
ZF_NATIVE_R_H_PROOF_ALLOWLIST = {
    "theorem:Bacon_Source_ZF_Action_BBK_Representation.paper_ZF_action_bbk_logical_equivalence_valid": {"paper_R_named_H"},
    "theorem:Bacon_Source_ZF_Action_BBK_Representation.paper_ZF_action_bbk_representation": {"paper_R_named_H"},
    "theorem:Bacon_Source_ZF_Action_H_Soundness.paper_ZF_action_model_H_truth": {"paper_R_named_H"},
    "theorem:Bacon_Source_ZF_Action_H_Soundness.paper_ZF_action_model_H_iff_truth": {"paper_R_named_H"},
    "theorem:Bacon_Source_ZF_Action_Logical_Equivalence.paper_ZF_action_model_logical_equivalence": {"paper_R_named_H"},
    "theorem:Bacon_Source_ZF_Action_Logical_Equivalence.paper_ZF_action_model_logical_equivalence_at_assignment": {"paper_R_named_H"},
}

# Direct native-C action-model soundness. This exact tier permits native
# R-C and R-H through the proved R-BBK construction, never the separate
# general Equivalence-rule presentation or any F/other-C calculus.
ZF_NATIVE_R_C_MODEL_ROOTS = (
    "theorem:Bacon_Source_ZF_Action_Classicism_Soundness.paper_ZF_action_classicism_BBK_valid",
    "theorem:Bacon_Source_ZF_Action_Classicism_Soundness.paper_ZF_action_classicism_truth",
    "theorem:Bacon_Source_ZF_Action_Classicism_Soundness.paper_ZF_action_classicism_soundness",
)
ZF_NATIVE_R_C_PROOF_ALLOWLIST = {
    "theorem:Bacon_Source_ZF_Action_Classicism_Soundness.paper_ZF_action_classicism_BBK_valid": {"paper_R_named_H", "paper_R_classicism_proves"},
    "theorem:Bacon_Source_ZF_Action_Classicism_Soundness.paper_ZF_action_classicism_truth": {"paper_R_named_H", "paper_R_classicism_proves"},
    "theorem:Bacon_Source_ZF_Action_Classicism_Soundness.paper_ZF_action_classicism_soundness": {"paper_R_named_H", "paper_R_classicism_proves"},
}

ZF_SOURCE_R_MODEL_ROOTS = (
    "theorem:Bacon_Source_ZF_R_Coded_Application.paper_ZF_R_profile_encoding.paper_ZF_R_coded_application_transport",
    "theorem:Bacon_Source_ZF_R_Coded_Application.paper_ZF_R_type_encoding.paper_ZF_R_type_encode_pair_value",
    "theorem:Bacon_Source_ZF_R_Binary_Logical_Graphs.paper_ZF_R_type_encoding.paper_ZF_R_binary_partial_graph",
    "theorem:Bacon_Source_ZF_R_Binary_Logical_Graphs.paper_ZF_R_type_encoding.paper_ZF_R_binary_logical_graph",
    "theorem:Bacon_Source_ZF_R_Boolean_Profile_Code.paper_ZF_R_profile_encoding.paper_ZF_R_conjunction_profile_code",
    "theorem:Bacon_Source_ZF_R_Boolean_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_And_empty_correspondence",
    "theorem:Bacon_Source_ZF_R_Boolean_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_And",
    "theorem:Bacon_Source_ZF_R_Boolean_Profile_Code.paper_ZF_R_profile_encoding.paper_ZF_R_disjunction_profile_code",
    "theorem:Bacon_Source_ZF_R_Boolean_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_Or_empty_correspondence",
    "theorem:Bacon_Source_ZF_R_Boolean_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_Or",
    "theorem:Bacon_Source_ZF_R_Identity_Profile_Code.paper_ZF_R_profile_encoding.paper_ZF_R_identity_profile_code",
    "theorem:Bacon_Source_ZF_R_Identity_Profile_Code.paper_ZF_R_type_encoding.paper_ZF_R_identity_code_at_values",
    "theorem:Bacon_Source_ZF_R_Identity_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_Eq_empty_correspondence",
    "theorem:Bacon_Source_ZF_R_Identity_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_Eq",
    "theorem:Bacon_Source_ZF_R_Quantifier_Tests.paper_ZF_R_type_encoding.paper_ZF_R_predicate_source_test",
    "theorem:Bacon_Source_ZF_R_Quantifier_Tests.paper_ZF_R_type_encoding.paper_ZF_R_quantifier_tests",
    "theorem:Bacon_Source_ZF_R_Quantifier_Profile_Code.paper_ZF_R_type_encoding.paper_ZF_R_quantifier_profile_code",
    "theorem:Bacon_Source_ZF_R_Quantifier_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_quantifier_empty_correspondence",
    "theorem:Bacon_Source_ZF_R_Quantifier_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_quantifier",
    "theorem:Bacon_Source_ZF_R_Proposition_Identity_Truth.paper_ZF_R_profile_encoding.paper_ZF_R_proposition_identity_truth",
    "theorem:Bacon_Source_ZF_R_Eval_Logical_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_Logical",
    "theorem:Bacon_Source_ZF_R_Eval_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_typed_correspondence",
    "theorem:Bacon_Source_ZF_R_Eval_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_correspondence",
    "theorem:Bacon_Source_ZF_R_Constructed_Model.paper_ZF_R_type_encoding.paper_ZF_R_eval_decoded",
    "theorem:Bacon_Source_ZF_R_Constructed_Model.paper_ZF_R_type_encoding.paper_ZF_R_eval_total_typed",
    "theorem:Bacon_Source_ZF_R_Constructed_Model.paper_ZF_R_type_encoding.paper_ZF_R_constructed_model",
    "theorem:Bacon_Source_ZF_R_Constructed_Model.paper_ZF_R_type_encoding.paper_ZF_R_intensional_constructed_model",
    "theorem:Bacon_Source_ZF_R_Root_Truth_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_holds_encoded",
    "theorem:Bacon_Source_ZF_R_Root_Truth_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_holds_decoded",
    "theorem:Bacon_Source_ZF_R_Root_Truth_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_arrow_validity_iff",
    "theorem:Bacon_Source_ZF_R_Root_Truth_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_root_validity_iff",
    "theorem:Bacon_Source_ZF_R_Represented_Category_Action_Model.paper_ZF_R_type_encoding.paper_ZF_R_represented_category_action_model",
    "theorem:Bacon_Source_ZF_R_Lambda_Input.paper_ZF_R_type_encoding.paper_ZF_R_lambda_input_assignment",
    "theorem:Bacon_Source_ZF_R_Lambda_Input.paper_ZF_R_type_encoding.paper_ZF_R_lambda_old_input",
    "theorem:Bacon_Source_ZF_R_Lambda_Graph.paper_ZF_R_type_encoding.paper_ZF_R_lambda_graph_value",
    "theorem:Bacon_Source_ZF_R_Eval_Lambda_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_Lam",
    "theorem:Bacon_Source_ZF_R_Negation_Profile_Code.paper_ZF_R_profile_encoding.paper_ZF_R_negation_profile_code",
    "theorem:Bacon_Source_ZF_R_Negation_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_Not_empty_correspondence",
    "theorem:Bacon_Source_ZF_R_Negation_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_Not_correspondence",
    "theorem:Bacon_Source_ZF_R_Negation_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_Not",
    "theorem:Bacon_Source_ZF_R_Eval_Basic_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_Var",
    "theorem:Bacon_Source_ZF_R_Eval_Basic_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_Const",
    "theorem:Bacon_Source_ZF_R_Eval_Basic_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_App",
    "theorem:Bacon_Source_ZF_R_Assignment_Naturality.paper_ZF_R_type_encoding.paper_ZF_R_encode_assignment_naturality",
    "theorem:Bacon_Source_ZF_R_Assignment_Naturality.paper_ZF_R_type_encoding.paper_ZF_R_decode_assignment_naturality",
    "theorem:Bacon_Source_ZF_R_Premodel_Domains.paper_ZF_R_type_encoding.paper_ZF_R_premodel_Prop_subaction",
    "theorem:Bacon_Source_ZF_R_Premodel_Domains.paper_ZF_R_type_encoding.paper_ZF_R_premodel_arrow_subaction",
    "theorem:Bacon_Source_ZF_R_Family_Actions.paper_ZF_R_type_encoding.paper_ZF_R_Ind_nonempty",
    "theorem:Bacon_Source_ZF_R_Root_Constants.paper_ZF_R_type_encoding.paper_ZF_R_root_constant_type",
    "theorem:Bacon_Source_ZF_R_Root_Constants.paper_ZF_R_type_encoding.paper_ZF_R_root_constant_transport",
    "theorem:Bacon_Source_ZF_R_Constructed_Premodel.paper_ZF_R_type_encoding.paper_ZF_R_constructed_premodel",
    "theorem:Bacon_Source_ZF_R_Constructed_Premodel.paper_ZF_R_type_encoding.paper_ZF_R_intensional_constructed_premodel",
    "theorem:Bacon_Source_ZF_R_Canonical_Application.paper_ZF_R_type_encoding.paper_ZF_R_application_correspondence",
    "theorem:Bacon_Source_ZF_R_Canonical_Application.paper_ZF_R_type_encoding.paper_ZF_R_application_closed",
    "theorem:Bacon_Source_ZF_R_Representation_Assignments.paper_ZF_R_type_encoding.paper_ZF_R_encode_assignment_typed",
    "theorem:Bacon_Source_ZF_R_Representation_Assignments.paper_ZF_R_type_encoding.paper_ZF_R_decode_assignment_typed",
    "theorem:Bacon_Source_ZF_R_Representation_Assignments.paper_ZF_R_type_encoding.paper_ZF_R_decode_encode_assignment",
    "theorem:Bacon_Source_ZF_R_Representation_Assignments.paper_ZF_R_type_encoding.paper_ZF_R_encode_decode_assignment",
    "theorem:Bacon_Source_ZF_R_Individual_Base.paper_ZF_R_type_encoding.paper_ZF_R_Ind_elements",
    "theorem:Bacon_Source_ZF_R_Base_Invariants.paper_ZF_R_type_encoding.paper_ZF_R_Ind_invariant",
    "theorem:Bacon_Source_ZF_R_Proposition_Base.paper_ZF_R_type_encoding.paper_ZF_R_Prop_range",
    "theorem:Bacon_Source_ZF_R_Proposition_Base.paper_ZF_R_type_encoding.paper_ZF_R_Prop_subaction",
    "theorem:Bacon_Source_ZF_R_Base_Invariants.paper_ZF_R_type_encoding.paper_ZF_R_Prop_invariant",
    "theorem:Bacon_Source_ZF_R_Arrow_Coherence.paper_ZF_R_arrow_step.paper_ZF_R_arrow_body_coherent",
    "theorem:Bacon_Source_ZF_R_Arrow_Bound.paper_ZF_R_arrow_step.paper_ZF_R_arrow_code_type",
    "theorem:Bacon_Source_ZF_R_Arrow_Bound.paper_ZF_R_arrow_step.paper_ZF_R_arrow_range_elements",
    "theorem:Bacon_Source_ZF_R_Arrow_Naturality.paper_ZF_R_arrow_body_naturality",
    "theorem:Bacon_Source_ZF_R_Arrow_Naturality.paper_ZF_R_arrow_encode_naturality",
    "theorem:Bacon_Source_ZF_R_Arrow_Injectivity.paper_ZF_R_arrow_encode_injective_from_children",
    "theorem:Bacon_Source_ZF_R_Arrow_Action.paper_ZF_R_arrow_step.paper_ZF_R_arrow_range_action",
    "theorem:Bacon_Source_ZF_R_Arrow_Invariant.paper_ZF_R_arrow_invariant",
    "theorem:Bacon_Source_ZF_R_All_Type_Representation.paper_ZF_R_type_encoding.paper_ZF_R_all_type_invariant",
    "theorem:Bacon_Source_ZF_R_Truth_Profile_Coding.paper_ZF_R_profile_encoding.paper_ZF_R_truth_profile_code_elements",
    "theorem:Bacon_Source_ZF_R_Truth_Profile_Coding.paper_ZF_R_profile_encoding.paper_ZF_R_truth_profile_code_on",
    "theorem:Bacon_Source_ZF_R_Truth_Profile_Coding.paper_ZF_R_profile_encoding.paper_ZF_R_truth_profile_code_type",
    "theorem:Bacon_Source_ZF_R_Truth_Profile_Coding.paper_ZF_R_profile_encoding.paper_ZF_R_truth_profile_code_injective",
    "theorem:Bacon_Source_ZF_R_Truth_Profile_Action.paper_ZF_R_profile_encoding.paper_ZF_R_truth_profile_code_naturality",
    "theorem:Bacon_Source_ZF_R_Truth_Profile_Action.paper_ZF_R_profile_encoding.paper_ZF_R_truth_profile_action_map",
    "theorem:Bacon_Source_ZF_R_Truth_Profile_Action.paper_ZF_R_profile_encoding.paper_ZF_R_reindexed_proposition_action",
    "theorem:Bacon_Source_ZF_R_Proposition_Range.paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_elements",
    "theorem:Bacon_Source_ZF_R_Proposition_Range.paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_action",
    "theorem:Bacon_Source_ZF_R_Proposition_Range.paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_subaction",
    "theorem:Bacon_Source_ZF_R_Proposition_Range.paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_forward_map",
    "theorem:Bacon_Source_ZF_R_Proposition_Range.paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_bijection",
    "theorem:Bacon_Source_ZF_R_Proposition_Range.paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_decode_type",
    "theorem:Bacon_Source_ZF_R_Proposition_Range.paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_encode_decode",
    "theorem:Bacon_Source_ZF_R_Proposition_Range.paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_decode_encode",
    "theorem:Bacon_Source_ZF_R_Proposition_Range.paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_inverse_map",
)
ZF_FOUNDATION_ROOTS = (
    ZF_REPRESENTATION_ROOTS + ZF_PREMODEL_DEDUCTION_ROOTS
    + ZF_PREMODEL_REGRESSION_ROOTS + ZF_ACTION_MODEL_DEDUCTION_ROOTS
    + ZF_ACTION_TO_R_MODEL_ROOTS + ZF_NATIVE_R_H_MODEL_ROOTS
    + ZF_NATIVE_R_C_MODEL_ROOTS + ZF_SOURCE_R_MODEL_ROOTS + ZF_HULL_ROOTS
    + ZF_SIGNATURE_TRANSPORT_ROOTS
)
ZF_PROOF_PREDICATES = (BOOK_CONJUNCTION_PROOF_PREDICATES | RELATIONAL_CONSISTENCY_PREDICATES
                       | RELATIONAL_H_RETRACTION_PROXY_PREDICATES | RELATIONAL_WITNESS_SYNTAX_CONSTANTS
                       | RELATIONAL_IDENTITY_CLASS_PREDICATES | RELATIONAL_HENKIN_DATA_CONSTANTS
                       | RELATIONAL_CLOSED_HENKIN_PREDICATES | RELATIONAL_TERM_ENV_CONSTANTS
                       | RELATIONAL_REP_CHOICE_CONSTANTS | RELATIONAL_COUNT_CODE_CONSTANTS
                       | RELATIONAL_RECODING_DATA_CONSTANTS) | {
    "H_proves", "H_derivable", "H_set_derivable", "H_signature_proves", "H_consistent",
    "pH_proves", "pH_set_derivable", "pH_consistent", "paper_global_H",
    "paper_global_derivable", "paper_global_consistent", "paper_named_H",
    "paper_named_derivable", "paper_named_consistent", "paper_R_named_H",
    "paper_R_named_derivable", "paper_R_equivalence_proves", "paper_R_classicism_proves",
    "C_proves", "CE_proves", "CEV_proves", "HE_proves", "HLE_proves",
}
ZF_FOREIGN_MODEL_PREDICATES = BOOK_CONJUNCTION_MODEL_PREDICATES | {
    "paper_named_bbk_model", "paper_named_bbk_model_axioms", "paper_bbk_data_valid",
    "paper_bbk_data_morphism", "paper_bbk_model_morphism", "pbbk_model", "bbk_model",
    "paper_db_bbk_structure", "paper_db_bbk_structure_axioms",
    "paper_db_bbk_model", "paper_db_bbk_model_axioms", "bacon_general_model",
}

# Generic stages must not import an independent R BBK validator either.
ZF_INDEPENDENT_R_MODEL_PREDICATES = {
    "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_data_valid",
    "paper_R_bbk_data_morphism", "paper_R_bbk_model_morphism",
    "paper_R_bbk_homomorphism", "paper_R_bbk_subcategory",
}

# The premodel is a constructed conclusion at precisely these two roots.
# Do not turn this into an allowance for the whole source-R tier. In
# particular, no assumed interpretation/totality/action-model predicate is
# allowed. Raw evaluation equations are model-free representation roots.
ZF_PREMODEL_CONCLUSION_ALLOWLIST = {
    "theorem:Bacon_Source_ZF_R_Constructed_Premodel.paper_ZF_R_type_encoding.paper_ZF_R_constructed_premodel": {"paper_ZF_action_premodel"},
    "theorem:Bacon_Source_ZF_R_Constructed_Premodel.paper_ZF_R_type_encoding.paper_ZF_R_intensional_constructed_premodel": {"paper_ZF_action_premodel"},
}
# Exactly these construction conclusions may reach the independent model
# predicate. This is not an allowance for assumptions of a supplied model.
ZF_MODEL_CONCLUSION_ALLOWLIST = {
    "theorem:Bacon_Source_ZF_R_Constructed_Model.paper_ZF_R_type_encoding.paper_ZF_R_constructed_model": {"paper_ZF_action_model", "paper_ZF_action_premodel"},
    "theorem:Bacon_Source_ZF_R_Constructed_Model.paper_ZF_R_type_encoding.paper_ZF_R_intensional_constructed_model": {"paper_ZF_action_model", "paper_ZF_action_premodel"},
    "theorem:Bacon_Source_ZF_R_Represented_Category_Action_Model.paper_ZF_R_type_encoding.paper_ZF_R_represented_category_action_model": {"paper_ZF_action_model", "paper_ZF_action_premodel"},
}
# The application step and its full-induction/assignment/truth descendants
# use a derived premodel, but never an action-model or totality assumption.
ZF_R_DERIVED_PREMODEL_ROOTS = (
    "theorem:Bacon_Source_ZF_R_Eval_Basic_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_App",
    "theorem:Bacon_Source_ZF_R_Eval_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_typed_correspondence",
    "theorem:Bacon_Source_ZF_R_Eval_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_correspondence",
    "theorem:Bacon_Source_ZF_R_Constructed_Model.paper_ZF_R_type_encoding.paper_ZF_R_eval_decoded",
    "theorem:Bacon_Source_ZF_R_Constructed_Model.paper_ZF_R_type_encoding.paper_ZF_R_eval_total_typed",
    "theorem:Bacon_Source_ZF_R_Root_Truth_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_holds_encoded",
    "theorem:Bacon_Source_ZF_R_Root_Truth_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_holds_decoded",
    "theorem:Bacon_Source_ZF_R_Root_Truth_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_arrow_validity_iff",
    "theorem:Bacon_Source_ZF_R_Root_Truth_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_root_validity_iff",
)
ZF_ACTION_STAGE_PREDICATES = {
    "paper_ZF_action_premodel", "paper_ZF_action_premodel_axioms",
    "paper_ZF_action_model", "paper_ZF_action_model_axioms",
    "paper_ZF_action_interpretation", "paper_ZF_action_interpretation_axioms",
    "paper_ZF_action_interpretation_total", "paper_ZF_action_totality",
}


def zf_action_stage_forbidden(root):
    if root in SIGNATURE_ACTION_TRANSPORT_ROOTS:
        return ZF_ACTION_STAGE_PREDICATES - SIGNATURE_TRANSPORT_MODEL_ALLOWLIST[root]
    if root in ZF_HULL_CONSTRUCTION_ROOTS:
        return ZF_ACTION_STAGE_PREDICATES - {"paper_ZF_action_model", "paper_ZF_action_premodel"}
    allowed = (ZF_PREMODEL_CONCLUSION_ALLOWLIST.get(root, set())
               | ZF_MODEL_CONCLUSION_ALLOWLIST.get(root, set()))
    if (root in ZF_PREMODEL_DEDUCTION_ROOTS or root in ZF_R_DERIVED_PREMODEL_ROOTS
            or root in ZF_PREMODEL_REGRESSION_ROOTS):
        allowed = allowed | {"paper_ZF_action_premodel"}
    if (root in ZF_ACTION_MODEL_DEDUCTION_ROOTS or root in ZF_ACTION_TO_R_MODEL_ROOTS
            or root in ZF_NATIVE_R_H_MODEL_ROOTS or root in ZF_NATIVE_R_C_MODEL_ROOTS):
        allowed = allowed | {"paper_ZF_action_model", "paper_ZF_action_premodel"}
    return ZF_ACTION_STAGE_PREDICATES - allowed


def zf_representation_forbidden(root, model_predicates):
    if root in ZF_SIGNATURE_TRANSPORT_ROOTS:
        return signature_transport_forbidden(root, model_predicates) | zf_action_stage_forbidden(root)
    if root in ZF_HULL_ROOTS:
        return hull_action_pipeline_forbidden(root, model_predicates) | zf_action_stage_forbidden(root)
    if root not in ZF_FOUNDATION_ROOTS:
        return set()
    allowed_models = (
        {"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
        if root in ZF_SOURCE_R_MODEL_ROOTS else set()
    )
    allowed_models |= ZF_PREMODEL_CONCLUSION_ALLOWLIST.get(root, set())
    allowed_models |= ZF_MODEL_CONCLUSION_ALLOWLIST.get(root, set())
    if (root in ZF_PREMODEL_DEDUCTION_ROOTS or root in ZF_R_DERIVED_PREMODEL_ROOTS
            or root in ZF_PREMODEL_REGRESSION_ROOTS):
        allowed_models.add("paper_ZF_action_premodel")
    allowed_models |= ZF_REVERSE_MODEL_CONCLUSION_ALLOWLIST.get(root, set())
    if root in ZF_NATIVE_R_H_MODEL_ROOTS or root in ZF_NATIVE_R_C_MODEL_ROOTS:
        allowed_models.add("paper_R_bbk_model")
    if (root in ZF_ACTION_MODEL_DEDUCTION_ROOTS or root in ZF_ACTION_TO_R_MODEL_ROOTS
            or root in ZF_NATIVE_R_H_MODEL_ROOTS or root in ZF_NATIVE_R_C_MODEL_ROOTS):
        allowed_models |= {"paper_ZF_action_model", "paper_ZF_action_premodel"}
    return (
        (set(model_predicates) - allowed_models)
        | (ZF_PROOF_PREDICATES - ZF_NATIVE_R_H_PROOF_ALLOWLIST.get(root, set())
           - ZF_NATIVE_R_C_PROOF_ALLOWLIST.get(root, set()))
        | ZF_FOREIGN_MODEL_PREDICATES
        | ((ZF_INDEPENDENT_R_MODEL_PREDICATES - ZF_REVERSE_MODEL_CONCLUSION_ALLOWLIST.get(root, set())
            - ({"paper_R_bbk_model"} if root in ZF_NATIVE_R_H_MODEL_ROOTS or root in ZF_NATIVE_R_C_MODEL_ROOTS else set()))
           if root not in ZF_SOURCE_R_MODEL_ROOTS else set())
        | zf_action_stage_forbidden(root)
    )


# Pure-HOL semantic boundary: only the first root constructs an R-BBK
# model from native syntactic Henkin data. The second takes an explicit
# supplied R model and changes only its constant interpretation.
# These exact semantic endpoints derive model existence/countermodels
# from the entire native construction. Their explicit data allowance is
# applied only after all ordinary proof-layer exclusions, and contains
# no model predicates or foreign proof judgments.
RELATIONAL_MODEL_EXISTENCE_ROOTS = (
    *RELATIONAL_H_THEORY_MODEL_ROOTS,
    RELATIONAL_CARDINAL_MODEL_ROOT,
    "theorem:Bacon_Source_Relational_Nat_Model_Existence.paper_R_BBK_nat_model_existence",
    "theorem:Bacon_Source_Relational_Nat_Countermodel.paper_R_nat_closed_countermodel",
    "theorem:Bacon_Source_Relational_Nat_Completeness.paper_R_nat_closed_strong_completeness",
    "theorem:Bacon_Source_Relational_Countable_Model_Existence.paper_R_BBK_countable_union_model_existence",
    "theorem:Bacon_Source_Relational_Model_Existence.paper_R_BBK_model_existence",
    "theorem:Bacon_Source_Relational_Closed_Countermodel.paper_R_closed_countermodel",
    "theorem:Bacon_Source_Relational_Closed_Completeness.paper_R_closed_strong_completeness",
)
RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST = {
    "theorem:Bacon_Source_Relational_H_Theory_Model_Existence.paper_R_H_theory_model_existence": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_named_consistent", "paper_R_named_top", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_H_Theory_Bounded_Model.paper_R_H_theory_bounded_model_existence": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_consistent", "paper_R_named_top", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Bounded_Model_Existence.paper_R_BBK_bounded_model_existence": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_add_constant", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_consistent", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Nat_Model_Existence.paper_R_BBK_nat_model_existence": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_add_constant", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_count_tree", "paper_R_named_consistent", "paper_R_named_count_tree", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Nat_Countermodel.paper_R_nat_closed_countermodel": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_add_constant", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_count_tree", "paper_R_named_consistent", "paper_R_named_count_tree", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Nat_Completeness.paper_R_nat_closed_strong_completeness": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_add_constant", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_count_tree", "paper_R_named_consistent", "paper_R_named_count_tree", "paper_R_nat_BBK_consequence", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    "theorem:Bacon_Source_Relational_Countable_Model_Existence.paper_R_BBK_countable_union_model_existence": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension", "paper_R_H_retraction_support", "paper_R_local_retraction_support", "paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms", "paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application", "paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises", "paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory", "paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote", "paper_R_constant_pullback_denote", "paper_R_logical_count_tree", "paper_R_named_count_tree"},
    "theorem:Bacon_Source_Relational_Model_Existence.paper_R_BBK_model_existence": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension", "paper_R_H_retraction_support", "paper_R_local_retraction_support", "paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms", "paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application", "paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises", "paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory", "paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote", "paper_R_constant_pullback_denote"},
    "theorem:Bacon_Source_Relational_Closed_Countermodel.paper_R_closed_countermodel": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension", "paper_R_H_retraction_support", "paper_R_local_retraction_support", "paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms", "paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application", "paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises", "paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory", "paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote", "paper_R_constant_pullback_denote"},
    "theorem:Bacon_Source_Relational_Closed_Completeness.paper_R_closed_strong_completeness": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension", "paper_R_H_retraction_support", "paper_R_local_retraction_support", "paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms", "paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application", "paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises", "paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory", "paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote", "paper_R_constant_pullback_denote", "paper_R_closed_BBK_consequence"},
}
RELATIONAL_CANONICAL_MODEL_ROOTS = (
    "theorem:Bacon_Source_Relational_Identity_Model.paper_R_identity_bbk_model",
)
RELATIONAL_CONSTANT_PULLBACK_ROOTS = (
    "theorem:Bacon_Source_Relational_BBK_Constant_Pullback.paper_R_bbk_constant_pullback",
)


def relational_model_boundary_forbidden(root, model_predicates):
    if (root not in RELATIONAL_CANONICAL_MODEL_ROOTS and root not in RELATIONAL_CONSTANT_PULLBACK_ROOTS
            and root not in RELATIONAL_MODEL_EXISTENCE_ROOTS and root not in RELATIONAL_RECODING_MODEL_ROOTS):
        return set()
    allowed_data = (RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST.get(root, set())
                    | RELATIONAL_CLOSED_HENKIN_ROOT_ALLOWLIST.get(root, set())
                    | RELATIONAL_IDENTITY_CLASS_ROOT_ALLOWLIST.get(root, set())
                    | RELATIONAL_TERM_ENV_ROOT_ALLOWLIST.get(root, set())
                    | RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_RECODING_DATA_ROOT_ALLOWLIST.get(root, set()))
    allowed_proofs = ({"paper_R_named_H", "paper_R_named_derivable"}
                      if root in RELATIONAL_CANONICAL_MODEL_ROOTS or root in RELATIONAL_MODEL_EXISTENCE_ROOTS else set())
    return ((set(model_predicates) - {"paper_R_bbk_model"}) | ZF_FOREIGN_MODEL_PREDICATES
            | (ZF_INDEPENDENT_R_MODEL_PREDICATES - {"paper_R_bbk_model"})
            | (ZF_PROOF_PREDICATES - allowed_data - allowed_proofs))


SOURCE_PROOF_ROOTS = (
    *BOOK_EXPONENTIAL_ROOTS,
    *BOOK_MODAL_STRUCTURE_ROOTS,
    *FIGURE3_MODAL_ROOTS,
    *SIGNATURE_ACTION_TRANSPORT_ROOTS,
    *HULL_ACTION_PIPELINE_ROOTS,
    *RELATIONAL_T312_ROOTS,
    *RELATIONAL_N73_ROOTS,
    *RELATIONAL_CLOSURE_NAMING_DIAGRAM_ROOTS[:1],
    *RELATIONAL_CLOSURE_NAMING_DIAGRAM_ROOTS[3:],
    *RELATIONAL_NAMING_MODAL_SEPARATION_ROOTS,
    *RELATIONAL_NAMING_STRUCTURE_STABILITY_ROOTS,
    *RELATIONAL_CHOSEN_NAMING_ROOTS,
    *RELATIONAL_CHART_NECESSITATION_ROOTS,
    *RELATIONAL_ZETA_ROOTS,
    *RELATIONAL_NAMING_COORDINATE_MODEL_ROOTS,
    *RELATIONAL_A3_ROOTS,
    *RELATIONAL_SUBSTITUTION_MODEL_ROOTS,
    *RELATIONAL_A2_COMPLETE_ROOTS,
    *RELATIONAL_A2_CONTINUATION_ROOTS,
    *RELATIONAL_A2_BASE_ROOTS,
    *RELATIONAL_C_PREPARATION_ROOTS,
    *RELATIONAL_RECODING_MODEL_ROOTS,
    *RELATIONAL_MODEL_EXISTENCE_ROOTS,
    *RELATIONAL_CANONICAL_MODEL_ROOTS,
    *RELATIONAL_CONSTANT_PULLBACK_ROOTS,
    *CLASSICISM_SEMANTIC_ROOTS,
    *RELATIONAL_H_PROOF_ROOTS,
    *RELATIONAL_C_PROOF_ROOTS,
    *ZF_REPRESENTATION_ROOTS,
    *ZF_PREMODEL_DEDUCTION_ROOTS,
    *ZF_PREMODEL_REGRESSION_ROOTS,
    *ZF_ACTION_MODEL_DEDUCTION_ROOTS,
    *ZF_ACTION_TO_R_MODEL_ROOTS,
    *ZF_NATIVE_R_H_MODEL_ROOTS,
    *ZF_NATIVE_R_C_MODEL_ROOTS,
    *ZF_SOURCE_R_MODEL_ROOTS,
    "theorem:Bacon_Source_Global_Proof_Preservation.paper_global_H_target_eventual",
    "theorem:Bacon_Source_Closed_Proof_Preservation.paper_global_H_closed_preservation",
    "theorem:Bacon_Source_Reverse_Proof_Preservation.pH_to_paper_global_H",
    "theorem:Bacon_Source_Proof_Correspondence.paper_global_H_closed_iff",
    "theorem:Bacon_Source_Set_Correspondence.paper_closed_set_derivable_iff",
    "theorem:Bacon_Source_Consistency_Correspondence.paper_closed_set_consistency_iff",
    "theorem:Bacon_Source_BBK_Model_Existence.paper_db_BBK_model_existence",
    "theorem:Bacon_Source_BBK_Model_Existence.paper_db_BBK_countable_signature_model_existence",
    "theorem:Bacon_Source_BBK_Countermodels.paper_db_BBK_closed_countermodel",
    "theorem:Bacon_Source_BBK_Renaming_Derived.paper_db_bbk_structure.paper_db_rename_derived",
    "theorem:Bacon_Source_BBK_Reverse_Booleans.paper_db_bbk_structure.paper_db_imp_truth",
    "theorem:Bacon_Source_BBK_Global_Soundness.paper_db_bbk_structure.paper_db_global_H_soundness",
    "theorem:Bacon_Source_BBK_Global_Soundness.paper_db_bbk_structure.paper_db_global_set_soundness",
    "theorem:Bacon_Source_BBK_Strong_Completeness.paper_db_closed_strong_completeness",
    "theorem:Bacon_Source_Named_Completion_Denotation.paper_db_bbk_structure.paper_db_named_completion_independent",
    "theorem:Bacon_Source_Named_Tagged_Model.paper_db_bbk_structure.paper_db_tagged_named_model",
    "theorem:Bacon_Finite_Calibration_BBK_Inhabitation.pH_empty_consistent_from_finite_calibration",
    "theorem:Bacon_Finite_Calibration_BBK_Inhabitation.paper_standard_named_model_exists_from_finite_calibration",
    *NAMED_SYNTAX_ROOTS,
    *NAMED_MODEL_ROOTS,
    *NAMED_REVERSE_MODEL_ROOTS,
    *NAMED_PROOF_ROOTS,
    *NATIVE_H_ROOTS,
    *BOOK_ENV_ROOTS,
    *BOOK_HENKIN_SYNTAX_ROOTS,
    *BOOK_THEORY_ROOTS,
    *BOOK_BBK_SYNTAX_ROOTS,
    *BOOK_BBK_CONSTRUCTION_ROOTS,
    *BOOK_INHABITATION_ROOTS,
    *BOOK_CONVERSION_ROOTS,
    *BOOK_PRINTED_INDEPENDENT_ROOTS,
    # Existing primitive syntax roots already occur in BOOK_CONVERSION_ROOTS;
    # strengthen their policy without checking or reporting them twice.
    *(root for root in BOOK_CONJUNCTION_ROOTS if root not in BOOK_CONVERSION_ROOTS),
    "theorem:Bacon_Source_Named_Reverse_Open_Validity.paper_named_bbk_model.paper_named_reverse_open_valid_iff",
    "theorem:Bacon_Source_Named_H_Soundness.paper_named_bbk_model.paper_named_H_soundness",
    "theorem:Bacon_Source_Named_H_Soundness.paper_named_bbk_model.paper_named_local_soundness",
    "theorem:Bacon_Source_Named_Model_Existence.paper_named_BBK_model_existence",
    "theorem:Bacon_Source_Named_Closed_Countermodel.paper_named_closed_countermodel",
    "theorem:Bacon_Source_Named_Closed_Strong_Completeness.paper_named_closed_strong_completeness",
    "theorem:Bacon_Source_Named_Consistent_Negation.paper_named_consistent_insert_not",
    "theorem:Bacon_Source_Named_Countable_Model_Existence.paper_named_BBK_countable_signature_model_existence",
    "theorem:Bacon_Source_Named_Nat_Countermodel.paper_named_nat_closed_countermodel",
    "theorem:Bacon_Source_Named_Nat_Strong_Completeness.paper_named_nat_closed_strong_completeness",
)


def check_zf_action_policy_controls():
    """Keep exact model conclusions distinct from generic and derived use."""
    if len(ZF_PREMODEL_CONCLUSION_ALLOWLIST) != 2:
        raise SystemExit("Expected exactly two premodel construction exceptions")
    if not set(ZF_PREMODEL_CONCLUSION_ALLOWLIST) <= set(ZF_SOURCE_R_MODEL_ROOTS):
        raise SystemExit("Premodel exception is not a source-R construction root")
    if any(allowed != {"paper_ZF_action_premodel"}
           for allowed in ZF_PREMODEL_CONCLUSION_ALLOWLIST.values()):
        raise SystemExit("Premodel exception permits a later semantic stage")
    expected_direct_c = {"theorem:Bacon_Source_Relational_Classicism_BBK_Soundness.paper_R_bbk_model.paper_R_classicism_BBK_soundness"}
    if set(CLASSICISM_SEMANTIC_R_DIRECT_C_ROOTS) != expected_direct_c:
        raise SystemExit("Unexpected pure direct-C semantic root")
    for direct_root in CLASSICISM_SEMANTIC_R_DIRECT_C_ROOTS:
        if direct_root in ZF_FOUNDATION_ROOTS:
            raise SystemExit("Pure direct-C theorem acquired HOL-ZF foundation")
        direct_models = {"paper_R_bbk_model", "paper_named_bbk_model", "pbbk_model",
                         "paper_ZF_action_model", "unknown_model"}
        direct_blocked = classicism_semantic_forbidden(direct_root, direct_models)
        if not (direct_models - {"paper_R_bbk_model"}) <= direct_blocked:
            raise SystemExit("Direct-C theorem permits a foreign model")
        if not {"paper_R_equivalence_proves", "C_proves", "CE_proves", "CEV_proves",
                "H_proves", "pH_proves", "paper_named_H", "paper_global_H"} <= direct_blocked:
            raise SystemExit("Direct-C theorem permits the wrong proof presentation")
        if {"paper_R_classicism_proves", "paper_R_named_H", "paper_R_bbk_model"} & direct_blocked:
            raise SystemExit("Direct-C native premises were forbidden")
    expected_models = {
        "theorem:Bacon_Source_ZF_R_Constructed_Model.paper_ZF_R_type_encoding.paper_ZF_R_constructed_model",
        "theorem:Bacon_Source_ZF_R_Constructed_Model.paper_ZF_R_type_encoding.paper_ZF_R_intensional_constructed_model",
        "theorem:Bacon_Source_ZF_R_Represented_Category_Action_Model.paper_ZF_R_type_encoding.paper_ZF_R_represented_category_action_model",
    }
    if set(ZF_MODEL_CONCLUSION_ALLOWLIST) != expected_models:
        raise SystemExit("Expected exactly the three action-model construction exceptions")
    if not expected_models <= set(ZF_SOURCE_R_MODEL_ROOTS):
        raise SystemExit("Action-model conclusion is not a source-R construction root")
    if any(allowed != {"paper_ZF_action_model", "paper_ZF_action_premodel"}
           for allowed in ZF_MODEL_CONCLUSION_ALLOWLIST.values()):
        raise SystemExit("Action-model conclusion permits an unrelated semantic stage")
    expected_derived = {
        "theorem:Bacon_Source_ZF_R_Eval_Basic_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_App",
        "theorem:Bacon_Source_ZF_R_Eval_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_typed_correspondence",
        "theorem:Bacon_Source_ZF_R_Eval_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_eval_correspondence",
        "theorem:Bacon_Source_ZF_R_Constructed_Model.paper_ZF_R_type_encoding.paper_ZF_R_eval_decoded",
        "theorem:Bacon_Source_ZF_R_Constructed_Model.paper_ZF_R_type_encoding.paper_ZF_R_eval_total_typed",
        "theorem:Bacon_Source_ZF_R_Root_Truth_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_holds_encoded",
        "theorem:Bacon_Source_ZF_R_Root_Truth_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_holds_decoded",
        "theorem:Bacon_Source_ZF_R_Root_Truth_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_arrow_validity_iff",
        "theorem:Bacon_Source_ZF_R_Root_Truth_Correspondence.paper_ZF_R_type_encoding.paper_ZF_R_root_validity_iff",
    }
    if set(ZF_R_DERIVED_PREMODEL_ROOTS) != expected_derived:
        raise SystemExit("Unexpected derived-premodel exception outside the checked induction chain")
    if not set(ZF_R_DERIVED_PREMODEL_ROOTS) <= set(ZF_SOURCE_R_MODEL_ROOTS):
        raise SystemExit("Derived-premodel exception is not a source-R root")
    if set(ZF_PREMODEL_DEDUCTION_ROOTS) & (set(ZF_REPRESENTATION_ROOTS) | set(ZF_SOURCE_R_MODEL_ROOTS)):
        raise SystemExit("Generic premodel deductions overlap another ZF tier")
    expected_regressions = {
        "theorem:Bacon_Source_ZF_Degenerate_Premodel.paper_ZF_degenerate_premodel",
        "theorem:Bacon_Source_ZF_Premodel_Naturality_Regression.paper_ZF_premodel_defined_value_need_not_be_selected",
    }
    if set(ZF_PREMODEL_REGRESSION_ROOTS) != expected_regressions:
        raise SystemExit("Unexpected premodel regression exception")
    expected_model_deductions = {
        "theorem:Bacon_Source_ZF_Model_Vector_Identity.paper_ZF_action_model_uniform_truth_vector_identity",
        "theorem:Bacon_Source_ZF_Model_Truth_Separation.paper_ZF_action_model_formula_outgoing_truth",
        "theorem:Bacon_Source_ZF_Model_Truth_Separation.paper_ZF_action_model_uniform_truth_equal",
        "theorem:Bacon_Source_ZF_Action_BBK_Logical_Application.paper_ZF_action_bbk_unary_logical_denote",
        "theorem:Bacon_Source_ZF_Action_BBK_Logical_Application.paper_ZF_action_bbk_binary_logical_denote",
        "theorem:Bacon_Source_ZF_Action_BBK_Quantifier_Truth.paper_ZF_action_bbk_fresh_predicate_test",
        "theorem:Bacon_Source_ZF_Action_BBK_Propositional_Truth.paper_ZF_action_bbk_valuation_neg",
        "theorem:Bacon_Source_ZF_Action_BBK_Propositional_Truth.paper_ZF_action_bbk_valuation_conj",
        "theorem:Bacon_Source_ZF_Action_BBK_Propositional_Truth.paper_ZF_action_bbk_valuation_disj",
        "theorem:Bacon_Source_ZF_Action_BBK_Identity_Truth.paper_ZF_action_bbk_valuation_identity",
        "theorem:Bacon_Source_ZF_Action_BBK_Quantifier_Truth.paper_ZF_action_bbk_valuation_forall",
        "theorem:Bacon_Source_ZF_Action_BBK_Quantifier_Truth.paper_ZF_action_bbk_valuation_exists",
        "theorem:Bacon_Source_ZF_Model_Vector_Equality.paper_ZF_action_model_uniform_truth_vector_equal",
        "theorem:Bacon_Source_ZF_Action_BBK_Model.paper_ZF_action_bbk_denote_beta_eta",
        "theorem:Bacon_Source_ZF_Model_Conversion_Steps.paper_ZF_action_model_beta_step",
        "theorem:Bacon_Source_ZF_Model_Conversion_Steps.paper_ZF_action_model_eta_step",
        "theorem:Bacon_Source_ZF_Model_Signature_Conversion.paper_ZF_action_model_signature_conversion_total",
        "theorem:Bacon_Source_ZF_Model_Conversion.paper_ZF_action_model_signature_conversion",
        "theorem:Bacon_Source_ZF_Model_Conversion.paper_ZF_action_model_raw_conversion",
        "theorem:Bacon_Source_ZF_Action_BBK_Interpretation.paper_ZF_action_bbk_denote_total",
        "theorem:Bacon_Source_ZF_Action_BBK_Interpretation.paper_ZF_action_bbk_denote_application_data",
        "theorem:Bacon_Source_ZF_Action_BBK_Interpretation.paper_ZF_action_bbk_denote_application_cong",
        "theorem:Bacon_Source_ZF_Action_BBK_Interpretation.paper_ZF_action_bbk_holds_iff",
        "theorem:Bacon_Source_ZF_Model_Substitution.paper_ZF_action_model_substitution",
        "theorem:Bacon_Source_ZF_Model_Beta_Conversion.paper_ZF_action_model_beta",
        "theorem:Bacon_Source_ZF_Model_Eta_Conversion.paper_ZF_action_model_eta",
        "theorem:Bacon_Source_ZF_Action_Model_Nonempty.paper_ZF_action_model_value_at_object",
        "theorem:Bacon_Source_ZF_Action_Model_Nonempty.paper_ZF_action_model_R_domain_nonempty",
        "theorem:Bacon_Source_ZF_Action_BBK_Domains.paper_ZF_action_bbk_domain_nonempty",
        "theorem:Bacon_Source_ZF_Model_Logical_Naturality.paper_ZF_action_model_logical_value_member",
        "theorem:Bacon_Source_ZF_Model_Logical_Naturality.paper_ZF_action_model_logical_naturality",
        "theorem:Bacon_Source_ZF_Model_Evaluation_Naturality.paper_ZF_action_model_eval_naturality",
    }
    if set(ZF_ACTION_MODEL_DEDUCTION_ROOTS) != expected_model_deductions:
        raise SystemExit("Unexpected generic action-model deduction allowance")
    expected_reverse = {"theorem:Bacon_Source_ZF_Action_BBK_Model.paper_ZF_action_to_R_bbk_model"}
    if set(ZF_ACTION_TO_R_MODEL_ROOTS) != expected_reverse:
        raise SystemExit("Unexpected ActionModel-to-R-BBK construction root")
    if set(ZF_REVERSE_MODEL_CONCLUSION_ALLOWLIST) != expected_reverse:
        raise SystemExit("Reverse R-BBK conclusion allowance has the wrong scope")
    if any(allowed != {"paper_R_bbk_model"}
           for allowed in ZF_REVERSE_MODEL_CONCLUSION_ALLOWLIST.values()):
        raise SystemExit("Reverse construction permits a foreign model predicate")
    expected_h_roots = {
        "theorem:Bacon_Source_ZF_Action_BBK_Representation.paper_ZF_action_bbk_logical_equivalence_valid",
        "theorem:Bacon_Source_ZF_Action_BBK_Representation.paper_ZF_action_bbk_representation",
        "theorem:Bacon_Source_ZF_Action_H_Soundness.paper_ZF_action_model_H_truth",
        "theorem:Bacon_Source_ZF_Action_H_Soundness.paper_ZF_action_model_H_iff_truth",
        "theorem:Bacon_Source_ZF_Action_Logical_Equivalence.paper_ZF_action_model_logical_equivalence",
        "theorem:Bacon_Source_ZF_Action_Logical_Equivalence.paper_ZF_action_model_logical_equivalence_at_assignment",
    }
    if set(ZF_NATIVE_R_H_MODEL_ROOTS) != expected_h_roots:
        raise SystemExit("Unexpected native R-H action-model root")
    if set(ZF_NATIVE_R_H_PROOF_ALLOWLIST) != expected_h_roots:
        raise SystemExit("Native R-H allowance has the wrong root scope")
    if any(allowed != {"paper_R_named_H"} for allowed in ZF_NATIVE_R_H_PROOF_ALLOWLIST.values()):
        raise SystemExit("Native R-H allowance permits a foreign proof judgment")
    expected_c_roots = {
        "theorem:Bacon_Source_ZF_Action_Classicism_Soundness.paper_ZF_action_classicism_BBK_valid",
        "theorem:Bacon_Source_ZF_Action_Classicism_Soundness.paper_ZF_action_classicism_truth",
        "theorem:Bacon_Source_ZF_Action_Classicism_Soundness.paper_ZF_action_classicism_soundness",
    }
    if set(ZF_NATIVE_R_C_MODEL_ROOTS) != expected_c_roots:
        raise SystemExit("Unexpected native R-C action-model root")
    if set(ZF_NATIVE_R_C_PROOF_ALLOWLIST) != expected_c_roots:
        raise SystemExit("Native R-C allowance has the wrong root scope")
    if any(allowed != {"paper_R_named_H", "paper_R_classicism_proves"}
           for allowed in ZF_NATIVE_R_C_PROOF_ALLOWLIST.values()):
        raise SystemExit("Native R-C allowance permits a foreign proof presentation")
    tiers = [set(ZF_REPRESENTATION_ROOTS), set(ZF_PREMODEL_DEDUCTION_ROOTS),
             set(ZF_PREMODEL_REGRESSION_ROOTS), set(ZF_ACTION_MODEL_DEDUCTION_ROOTS),
             set(ZF_ACTION_TO_R_MODEL_ROOTS), set(ZF_NATIVE_R_H_MODEL_ROOTS),
             set(ZF_NATIVE_R_C_MODEL_ROOTS), set(ZF_SOURCE_R_MODEL_ROOTS),
             set(ZF_HULL_ROOTS[:2]), set(ZF_HULL_CONSTRUCTION_ROOTS), set(ZF_SIGNATURE_TRANSPORT_ROOTS)]
    if sum(map(len, tiers)) != len(set().union(*tiers)):
        raise SystemExit("ZF dependency tiers overlap")
    probes = {"paper_R_bbk_model", "paper_R_bbk_data_valid", "paper_named_bbk_model",
              "paper_ZF_action_premodel", "paper_ZF_action_model", "policy_probe_model"}
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = zf_action_stage_forbidden(root) | zf_representation_forbidden(root, probes)
        allowed_here = (root in ZF_PREMODEL_CONCLUSION_ALLOWLIST
                        or root in ZF_MODEL_CONCLUSION_ALLOWLIST
                        or root in ZF_PREMODEL_DEDUCTION_ROOTS
                        or root in ZF_R_DERIVED_PREMODEL_ROOTS
                        or root in ZF_PREMODEL_REGRESSION_ROOTS
                        or root in ZF_ACTION_MODEL_DEDUCTION_ROOTS
                        or root in ZF_ACTION_TO_R_MODEL_ROOTS
                        or root in ZF_NATIVE_R_H_MODEL_ROOTS
                        or root in ZF_NATIVE_R_C_MODEL_ROOTS
                        or root in ZF_HULL_CONSTRUCTION_ROOTS
                        or root in SIGNATURE_ACTION_TRANSPORT_ROOTS[7:])
        if ("paper_ZF_action_premodel" not in blocked) != allowed_here:
            raise SystemExit(f"Premodel negative control failed: {root}")
        model_allowed = (root in ZF_MODEL_CONCLUSION_ALLOWLIST
                         or root in ZF_ACTION_MODEL_DEDUCTION_ROOTS
                         or root in ZF_ACTION_TO_R_MODEL_ROOTS
                         or root in ZF_NATIVE_R_H_MODEL_ROOTS
                         or root in ZF_NATIVE_R_C_MODEL_ROOTS
                         or root in ZF_HULL_CONSTRUCTION_ROOTS
                         or root in SIGNATURE_ACTION_TRANSPORT_ROOTS[7:])
        if ("paper_ZF_action_model" not in blocked) != model_allowed:
            raise SystemExit(f"Action-model conclusion negative control failed: {root}")
        never_allowed = ZF_ACTION_STAGE_PREDICATES - {"paper_ZF_action_premodel", "paper_ZF_action_model"}
        if not never_allowed <= blocked:
            raise SystemExit(f"Later action-stage negative control failed: {root}")
        if root in ZF_FOUNDATION_ROOTS:
            allowed_proofs = (ZF_NATIVE_R_H_PROOF_ALLOWLIST.get(root, set())
                              | ZF_NATIVE_R_C_PROOF_ALLOWLIST.get(root, set())
                              | ({"paper_R_named_H", "paper_R_named_derivable", "paper_R_classicism_proves"}
                                 if root in ZF_HULL_CONSTRUCTION_ROOTS else set())
                              | SIGNATURE_TRANSPORT_PROOF_ALLOWLIST.get(root, set()))
            if not (ZF_PROOF_PREDICATES - allowed_proofs) <= blocked or "paper_named_bbk_model" not in blocked:
                raise SystemExit(f"ZF proof/F-model negative control failed: {root}")
            if allowed_proofs & blocked:
                raise SystemExit(f"Native R-H positive control failed: {root}")
            if "policy_probe_model" not in blocked:
                raise SystemExit(f"Unknown-model negative control failed: {root}")
            if root not in ZF_SOURCE_R_MODEL_ROOTS:
                reverse_allowed = ZF_REVERSE_MODEL_CONCLUSION_ALLOWLIST.get(root, set())
                if root in ZF_NATIVE_R_H_MODEL_ROOTS or root in ZF_NATIVE_R_C_MODEL_ROOTS:
                    reverse_allowed = reverse_allowed | {"paper_R_bbk_model"}
                if root in ZF_HULL_CONSTRUCTION_ROOTS:
                    reverse_allowed |= HULL_ACTION_MODEL_ALLOWLIST[root] & ZF_INDEPENDENT_R_MODEL_PREDICATES
                reverse_allowed |= SIGNATURE_TRANSPORT_MODEL_ALLOWLIST.get(root, set()) & ZF_INDEPENDENT_R_MODEL_PREDICATES
                if not (ZF_INDEPENDENT_R_MODEL_PREDICATES - reverse_allowed) <= blocked:
                    raise SystemExit(f"Generic ZF R-model negative control failed: {root}")
                if reverse_allowed & blocked:
                    raise SystemExit(f"Reverse R-BBK conclusion positive control failed: {root}")


def check_relational_consistency_policy_controls():
    expected_roots = {
        "theorem:Bacon_Source_Relational_Deduction.paper_R_named_derivable_deduction",
        "theorem:Bacon_Source_Relational_Deduction.paper_R_named_derivable_deduction_iff",
        "theorem:Bacon_Source_Relational_Explosion.paper_R_named_derivable_explosion",
        "theorem:Bacon_Source_Relational_Explosion.paper_R_named_derivable_reductio",
        "theorem:Bacon_Source_Relational_Consistency.paper_R_named_consistent_finite_character",
        "theorem:Bacon_Source_Relational_Consistency.paper_R_named_consistent_insert_not",
        "theorem:Bacon_Source_Relational_Consequence_Closure.paper_R_named_derivable_cut",
        "theorem:Bacon_Source_Relational_Consequence_Closure.paper_R_named_consistent_insert_derivable",
        "theorem:Bacon_Source_Relational_Consequence_Closure.paper_R_named_consistent_decision_extension",
        "theorem:Bacon_Source_Relational_Lindenbaum.paper_R_named_consistent_chain_Union",
        "theorem:Bacon_Source_Relational_Lindenbaum.paper_R_closed_maximal_extension_exists",
        "theorem:Bacon_Source_Relational_Maximal_Theory.paper_R_closed_maximal_consequence",
        "theorem:Bacon_Source_Relational_Maximal_Theory.paper_R_closed_maximal_membership_iff",
        "theorem:Bacon_Source_Relational_Maximal_Theory.paper_R_closed_maximal_exactly_one",
        "theorem:Bacon_Source_Relational_Existence.paper_R_named_type_existence",
    }
    expected_allowances = {
        "theorem:Bacon_Source_Relational_Henkin_Existential_Membership.paper_R_closed_Henkin_exists_member": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Universal_Membership.paper_R_closed_Henkin_forall_member": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_exists_class": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_forall_class": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_forall_truth": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_exists_truth": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Model.paper_R_identity_bbk_model": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_neg_truth": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_conj_truth": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_disj_truth": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_valuation_identity": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_denote_identity_truth": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_not_member": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_and_member": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_or_member": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_not": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_and": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_or": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_class": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_rep": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_declared_constant": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_identity_domain_nonempty": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_full_premises_closed": {"paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_stage_consistent_full_signature": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_full_premises_consistent": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Closed_Witness_Completeness.paper_R_closed_witness_complete_from_conditionals": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension"},
        "theorem:Bacon_Source_Relational_Closed_Henkin_Theory.paper_R_closed_maximal_Henkin": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension"},
        "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension"},
        "theorem:Bacon_Source_Relational_Constant_Map_Consistency.paper_R_named_consistent_injective_constant_map_iff": {"paper_R_named_consistent"},
        "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_closed": {"paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_original_consistent": {"paper_R_named_consistent"},
        "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_premises_consistent": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Witness_Family_Syntax.paper_R_witness_family_closed_theory": {"paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Finite_Witness_Family.paper_R_named_consistent_finite_witness_family": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Witness_Family_Consistency.paper_R_named_consistent_witness_family": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Witness_Syntax.paper_R_witness_sentence": {"paper_R_sentence"},
        "theorem:Bacon_Source_Relational_Witness_Consistency.paper_R_named_consistent_fresh_witness": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"},
        "theorem:Bacon_Source_Relational_Local_Signature_Conservativity.paper_R_named_consistent_signature_transport": {"paper_R_named_consistent"},
        "theorem:Bacon_Source_Relational_Consistency.paper_R_named_consistent_finite_character": {"paper_R_named_consistent"},
        "theorem:Bacon_Source_Relational_Consistency.paper_R_named_consistent_insert_not": {"paper_R_named_consistent"},
        "theorem:Bacon_Source_Relational_Consequence_Closure.paper_R_named_consistent_insert_derivable": {"paper_R_named_consistent"},
        "theorem:Bacon_Source_Relational_Consequence_Closure.paper_R_named_consistent_decision_extension": {"paper_R_named_consistent"},
        "theorem:Bacon_Source_Relational_Lindenbaum.paper_R_named_consistent_chain_Union": {"paper_R_named_consistent"},
        "theorem:Bacon_Source_Relational_Lindenbaum.paper_R_closed_maximal_extension_exists": set(RELATIONAL_CONSISTENCY_PREDICATES),
        "theorem:Bacon_Source_Relational_Maximal_Theory.paper_R_closed_maximal_consequence": set(RELATIONAL_CONSISTENCY_PREDICATES),
        "theorem:Bacon_Source_Relational_Maximal_Theory.paper_R_closed_maximal_membership_iff": set(RELATIONAL_CONSISTENCY_PREDICATES),
        "theorem:Bacon_Source_Relational_Maximal_Theory.paper_R_closed_maximal_exactly_one": set(RELATIONAL_CONSISTENCY_PREDICATES),
    }
    if set(RELATIONAL_H_CORE_ROOTS) != expected_roots:
        raise SystemExit("Unexpected native R-H core endpoint")
    if RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST != expected_allowances:
        raise SystemExit("Native R consistency predicate allowance changed scope")
    if not expected_roots <= set(RELATIONAL_H_PROOF_ROOTS):
        raise SystemExit("Native R-H core endpoint escaped its pure proof tier")
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        allowed = RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST.get(root, set())
        blocked = relational_consistency_forbidden(root)
        if (RELATIONAL_CONSISTENCY_PREDICATES - allowed) - blocked or allowed & blocked:
            raise SystemExit(f"Consistency predicate isolation failed: {root}")
        if root in expected_roots:
            if root in ZF_FOUNDATION_ROOTS:
                raise SystemExit("Native R-H consistency core acquired HOL-ZF")
            model_probes = {"paper_R_bbk_model", "paper_named_bbk_model", "pbbk_model",
                            "paper_ZF_action_model", "unknown_model"}
            proof_blocked = classicism_semantic_forbidden(root, model_probes) | blocked
            if not model_probes <= proof_blocked:
                raise SystemExit("Native R-H consistency core permits a model")
            if not (ZF_PROOF_PREDICATES - {"paper_R_named_H", "paper_R_named_derivable"} - allowed) <= proof_blocked:
                raise SystemExit("Native R-H consistency core permits a foreign judgment")
            if allowed & proof_blocked:
                raise SystemExit("Native consistency endpoint forbids its declared predicate")


def check_relational_retraction_policy_controls():
    expected_h = {
        "theorem:Bacon_Source_Relational_H_Retraction.paper_R_named_H_retraction_support",
        "theorem:Bacon_Source_Relational_H_Signature_Conservativity.paper_R_named_H_foreign_constants_eliminate",
        "theorem:Bacon_Source_Relational_H_Signature_Conservativity.paper_R_named_H_signature_iff",
    }
    expected_local = {
        "theorem:Bacon_Source_Relational_Local_Retraction.paper_R_named_derivable_retraction_support",
        "theorem:Bacon_Source_Relational_Local_Signature_Conservativity.paper_R_named_derivable_foreign_constants_eliminate",
        "theorem:Bacon_Source_Relational_Local_Signature_Conservativity.paper_R_named_derivable_signature_iff",
        "theorem:Bacon_Source_Relational_Local_Signature_Conservativity.paper_R_named_consistent_signature_transport",
    }
    expected_identity = {
        "theorem:Bacon_Source_Relational_Conversion_Identity_Steps.paper_R_named_H_beta_identity",
        "theorem:Bacon_Source_Relational_Conversion_Identity_Steps.paper_R_named_H_eta_identity",
        "theorem:Bacon_Source_Relational_Conversion_Identity.paper_R_named_H_raw_conversion_identity",
        "theorem:Bacon_Source_Relational_Application_Congruence.paper_R_named_identity_App_argument",
        "theorem:Bacon_Source_Relational_Application_Congruence.paper_R_named_identity_App_head",
        "theorem:Bacon_Source_Relational_Application_Congruence.paper_R_named_identity_App",
        "theorem:Bacon_Source_Relational_Identity_Proof_Basics.paper_R_named_derivable_beta_iff",
        "theorem:Bacon_Source_Relational_Identity_Derivations.paper_R_named_identity_refl",
        "theorem:Bacon_Source_Relational_Identity_Derivations.paper_R_named_identity_sym",
        "theorem:Bacon_Source_Relational_Identity_Derivations.paper_R_named_identity_trans",
    }
    if set(RELATIONAL_H_RETRACTION_ROOTS) != expected_h or set(RELATIONAL_H_LOCAL_RETRACTION_ROOTS) != expected_local:
        raise SystemExit("Unexpected native R-H retraction endpoint")
    if set(RELATIONAL_H_IDENTITY_ROOTS) != expected_identity:
        raise SystemExit("Unexpected native R-H identity endpoint")
    expected_predicates = {"paper_R_H_retraction_support", "paper_R_local_retraction_support"}
    if RELATIONAL_H_RETRACTION_PROXY_PREDICATES != expected_predicates:
        raise SystemExit("Retraction proof proxy predicate changed")
    expected_allowances = {root: {"paper_R_H_retraction_support"} for root in expected_h}
    expected_allowances.update({root: set(expected_predicates) for root in expected_local})
    expected_allowances["theorem:Bacon_Source_Relational_Witness_Consistency.paper_R_named_consistent_fresh_witness"] = set(expected_predicates)
    expected_allowances["theorem:Bacon_Source_Relational_Finite_Witness_Family.paper_R_named_consistent_finite_witness_family"] = set(expected_predicates)
    expected_allowances["theorem:Bacon_Source_Relational_Witness_Family_Consistency.paper_R_named_consistent_witness_family"] = set(expected_predicates)
    expected_allowances["theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_premises_consistent"] = set(expected_predicates)
    expected_allowances["theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_stage_consistent_full_signature"] = set(expected_predicates)
    expected_allowances["theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_full_premises_consistent"] = set(expected_predicates)
    expected_allowances["theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists"] = set(expected_predicates)
    witness_consistency_roots = {
        "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_stage_consistent_full_signature",
        "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_full_premises_consistent",
        "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists",
        "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_premises_consistent",
        "theorem:Bacon_Source_Relational_Witness_Consistency.paper_R_named_consistent_fresh_witness",
        "theorem:Bacon_Source_Relational_Finite_Witness_Family.paper_R_named_consistent_finite_witness_family",
        "theorem:Bacon_Source_Relational_Witness_Family_Consistency.paper_R_named_consistent_witness_family",
    }
    if RELATIONAL_RETRACTION_PROXY_ROOT_ALLOWLIST != expected_allowances:
        raise SystemExit("Retraction proxy allowance changed exact root scope")
    expected = expected_h | expected_local | expected_identity | witness_consistency_roots
    if not expected <= set(RELATIONAL_H_PROOF_ROOTS):
        raise SystemExit("Retraction or identity endpoint escaped the pure R-H proof tier")
    transport = "theorem:Bacon_Source_Relational_Local_Signature_Conservativity.paper_R_named_consistent_signature_transport"
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        proxy_blocked = relational_retraction_proxy_forbidden(root)
        allowed = expected_allowances.get(root, set())
        if not expected_predicates - allowed <= proxy_blocked or allowed & proxy_blocked:
            raise SystemExit(f"Retraction proxy isolation failed: {root}")
        if root in expected:
            if root in ZF_FOUNDATION_ROOTS:
                raise SystemExit("Retraction or identity proof acquired HOL-ZF")
            consistency_allowed = ({"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension"} if root == "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists"
                                   else {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory"}
                                   if root in witness_consistency_roots
                                   else {"paper_R_named_consistent"} if root == transport else set())
            if RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST.get(root, set()) != consistency_allowed:
                raise SystemExit("Retraction or identity proof acquired a consistency shortcut")
            models = {"paper_R_bbk_model", "paper_named_bbk_model", "pbbk_model",
                      "paper_ZF_action_model", "unknown_model"}
            blocked = (classicism_semantic_forbidden(root, models)
                       | relational_consistency_forbidden(root) | proxy_blocked)
            if not models | (RELATIONAL_CONSISTENCY_PREDICATES - consistency_allowed) <= blocked:
                raise SystemExit("Retraction or identity proof permits a model or consistency shortcut")
            needed = ({"paper_R_named_H", "paper_R_named_derivable"} | allowed | consistency_allowed
                      | RELATIONAL_WITNESS_SYNTAX_ROOT_ALLOWLIST.get(root, set())
                      | RELATIONAL_HENKIN_DATA_ROOT_ALLOWLIST.get(root, set())
                      | RELATIONAL_CLOSED_HENKIN_ROOT_ALLOWLIST.get(root, set()))
            if not ZF_PROOF_PREDICATES - needed <= blocked:
                raise SystemExit("Retraction or identity proof permits a foreign calculus")
            if (allowed | consistency_allowed) & blocked:
                raise SystemExit("Retraction proof proxy positive control failed")


def check_relational_witness_class_policy_controls():
    expected_witness = {
        "theorem:Bacon_Source_Relational_Witness_Family_Syntax.paper_R_witness_family_closed_theory",
        "theorem:Bacon_Source_Relational_Finite_Witness_Family.paper_R_named_consistent_finite_witness_family",
        "theorem:Bacon_Source_Relational_Witness_Family_Consistency.paper_R_named_consistent_witness_family",
        "theorem:Bacon_Source_Relational_Local_Exchange.paper_R_named_derivable_empty_iff",
        "theorem:Bacon_Source_Relational_Local_Inst.paper_R_named_derivable_Inst",
        "theorem:Bacon_Source_Relational_Witness_Syntax.paper_R_witness_sentence",
        "theorem:Bacon_Source_Relational_Witness_Syntax.paper_R_witness_retract",
        "theorem:Bacon_Source_Relational_Witness_Propositional.paper_R_named_derivable_not_intro",
        "theorem:Bacon_Source_Relational_Witness_Consistency.paper_R_named_consistent_fresh_witness",
    }
    expected_classes = {
        "theorem:Bacon_Source_Relational_Identity_Representatives.paper_R_identity_class_rep",
        "theorem:Bacon_Source_Relational_Identity_Application.paper_R_identity_application_domain",
        "theorem:Bacon_Source_Relational_Identity_Application.paper_R_identity_application_classes",
        "theorem:Bacon_Source_Relational_Identity_Application.paper_R_identity_application_representatives",
        "theorem:Bacon_Source_Relational_Identity_Class_Relation.paper_R_identity_relation_equiv",
        "theorem:Bacon_Source_Relational_Identity_Classes.paper_R_identity_class_eq_iff",
        "theorem:Bacon_Source_Relational_Identity_Classes.paper_R_identity_value_nonempty",
        "theorem:Bacon_Source_Relational_Identity_Classes.paper_R_identity_domains_disjoint",
    }
    if set(RELATIONAL_H_WITNESS_ROOTS) != expected_witness or set(RELATIONAL_H_IDENTITY_CLASS_ROOTS) != expected_classes:
        raise SystemExit("Unexpected witness or identity-class proof endpoint")
    if RELATIONAL_WITNESS_SYNTAX_CONSTANTS != {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"} or RELATIONAL_IDENTITY_CLASS_PREDICATES != {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"}:
        raise SystemExit("Witness/class proof-data isolation set changed")
    expected_witness_allowances = {
        "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_full_premises_closed": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_finite_premises_stage_bound": {"paper_R_witness_axiom", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_stage_consistent_full_signature": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_full_premises_consistent": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Henkin_Witness_Coverage.paper_R_henkin_full_witness_axiom": {"paper_R_witness_axiom", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Closed_Witness_Completeness.paper_R_closed_witness_complete_from_conditionals": {"paper_R_witness_axiom"},
        "theorem:Bacon_Source_Relational_Closed_Henkin_Theory.paper_R_closed_maximal_Henkin": {"paper_R_witness_axiom"},
        "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Henkin_Stage_Signature.paper_R_henkin_signature_family": {"paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_mono": {"paper_R_witness_axiom", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_closed": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_original_consistent": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_premises_consistent": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Witness_Family_Syntax.paper_R_witness_family_closed_theory": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Finite_Witness_Family.paper_R_named_consistent_finite_witness_family": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Witness_Family_Consistency.paper_R_named_consistent_witness_family": {"paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms"},
        "theorem:Bacon_Source_Relational_Witness_Syntax.paper_R_witness_sentence": {"paper_R_add_constant", "paper_R_witness_axiom"},
        "theorem:Bacon_Source_Relational_Witness_Syntax.paper_R_witness_retract": {"paper_R_add_constant", "paper_R_witness_axiom"},
        "theorem:Bacon_Source_Relational_Witness_Consistency.paper_R_named_consistent_fresh_witness": {"paper_R_add_constant", "paper_R_witness_axiom"},
    }
    expected_class_allowances = {
        "theorem:Bacon_Source_Relational_Environment_Finite_Identity.paper_R_environment_subst_assignment_identity": {"paper_R_closed_terms"},
        "theorem:Bacon_Source_Relational_Arbitrary_Representatives.paper_R_identity_denote_arbitrary_representatives": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Identity_Countable_Domains.paper_R_identity_domains_countable": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain"},
        "theorem:Bacon_Source_Relational_Environment_Update_Identity.paper_R_environment_subst_update_identity": {"paper_R_closed_terms"},
        "theorem:Bacon_Source_Relational_Henkin_Existential_Membership.paper_R_closed_Henkin_exists_member": {"paper_R_closed_terms"},
        "theorem:Bacon_Source_Relational_Henkin_Universal_Membership.paper_R_closed_Henkin_forall_member": {"paper_R_closed_terms"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_exists_class": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_forall_class": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
        "theorem:Bacon_Source_Relational_Identity_Fresh_Application.paper_R_identity_denote_fresh_application": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_forall_truth": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_exists_truth": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
        "theorem:Bacon_Source_Relational_Identity_Model.paper_R_identity_bbk_model": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
        "theorem:Bacon_Source_Relational_Environment_Conversion.paper_R_environment_subst_raw_conversion": {"paper_R_closed_terms"},
        "theorem:Bacon_Source_Relational_Identity_Conversion.paper_R_identity_denote_beta_eta": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_neg_truth": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_conj_truth": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_disj_truth": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_valuation_identity": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class"},
        "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_denote_identity_truth": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Identity_Application_Congruence.paper_R_identity_denote_application_cong": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
        "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_not_member": {"paper_R_closed_terms"},
        "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_and_member": {"paper_R_closed_terms"},
        "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_or_member": {"paper_R_closed_terms"},
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_not": {"paper_R_closed_terms", "paper_R_identity_class"},
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_and": {"paper_R_closed_terms", "paper_R_identity_class"},
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_or": {"paper_R_closed_terms", "paper_R_identity_class"},
        "theorem:Bacon_Source_Relational_Representative_Assignments.paper_R_representative_assignment_domain": {"paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Representative_Assignments.paper_R_representative_assignment_typed": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Environment_Substitution_Typing.paper_R_representative_substitution_closed_terms": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Propositional_Identity_Derivations.paper_R_closed_propositional_identity_membership": {"paper_R_closed_terms"},
        "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_class": {"paper_R_closed_terms", "paper_R_identity_class"},
        "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_rep": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_type": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_var": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_locality": {"paper_R_identity_class", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_App": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
        "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_identity_domain_nonempty": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain"},
        "theorem:Bacon_Source_Relational_Identity_Representatives.paper_R_identity_class_rep": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep"},
        "theorem:Bacon_Source_Relational_Identity_Application.paper_R_identity_application_domain": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
        "theorem:Bacon_Source_Relational_Identity_Application.paper_R_identity_application_classes": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
        "theorem:Bacon_Source_Relational_Identity_Application.paper_R_identity_application_representatives": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application"},
        "theorem:Bacon_Source_Relational_Identity_Class_Relation.paper_R_identity_relation_equiv": {"paper_R_closed_terms", "paper_R_identity_relation"},
        "theorem:Bacon_Source_Relational_Identity_Classes.paper_R_identity_class_eq_iff": {"paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class"},
        "theorem:Bacon_Source_Relational_Identity_Classes.paper_R_identity_value_nonempty": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain"},
        "theorem:Bacon_Source_Relational_Identity_Classes.paper_R_identity_domains_disjoint": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain"},
    }
    if RELATIONAL_WITNESS_SYNTAX_ROOT_ALLOWLIST != expected_witness_allowances or RELATIONAL_IDENTITY_CLASS_ROOT_ALLOWLIST != expected_class_allowances:
        raise SystemExit("Witness/class data allowance changed exact root scope")
    expected = expected_witness | expected_classes
    if not expected <= set(RELATIONAL_H_PROOF_ROOTS):
        raise SystemExit("Witness/class endpoint escaped its pure R-H tier")
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        data_allowed = expected_witness_allowances.get(root, set()) | expected_class_allowances.get(root, set())
        data_blocked = relational_witness_class_forbidden(root)
        if not (RELATIONAL_WITNESS_SYNTAX_CONSTANTS | RELATIONAL_IDENTITY_CLASS_PREDICATES) - data_allowed <= data_blocked or data_allowed & data_blocked:
            raise SystemExit(f"Witness/class data isolation failed: {root}")
        if root in expected:
            if root in ZF_FOUNDATION_ROOTS:
                raise SystemExit("Witness/class proof acquired HOL-ZF")
            cons = RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST.get(root, set())
            proxy = RELATIONAL_RETRACTION_PROXY_ROOT_ALLOWLIST.get(root, set())
            if root in expected_classes and (cons or proxy):
                raise SystemExit("Identity classes acquired consistency or retraction assumptions")
            models = {"paper_R_bbk_model", "paper_named_bbk_model", "pbbk_model", "paper_ZF_action_model", "unknown_model"}
            blocked = (classicism_semantic_forbidden(root, models) | data_blocked
                       | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root))
            allowed = data_allowed | cons | proxy
            if not models <= blocked or not ZF_PROOF_PREDICATES - {"paper_R_named_H", "paper_R_named_derivable"} - allowed <= blocked:
                raise SystemExit("Witness/class proof permits a model or foreign calculus")
            if allowed & blocked:
                raise SystemExit("Witness/class predicate positive control failed")


def check_relational_constant_map_policy_controls():
    expected_raw = {
        "theorem:Bacon_Source_Relational_Constant_Map.paper_R_constant_map_type",
        "theorem:Bacon_Source_Relational_Constant_Map.paper_R_constant_map_fv",
        "theorem:Bacon_Source_Relational_Constant_Map_Binding.paper_R_constant_map_subst",
        "theorem:Bacon_Source_Relational_Constant_Map_Binding.paper_R_constant_map_free_for",
        "theorem:Bacon_Source_Relational_Constant_Map_Binding.paper_R_constant_map_raw_conversion",
    }
    expected_h = {"theorem:Bacon_Source_Relational_H_Constant_Map.paper_R_named_H_constant_map"}
    if set(RELATIONAL_CONSTANT_MAP_RAW_ROOTS) != expected_raw or set(RELATIONAL_H_CONSTANT_MAP_ROOTS) != expected_h:
        raise SystemExit("Unexpected constant-map endpoint")
    for root in expected_raw | expected_h:
        if root in ZF_FOUNDATION_ROOTS:
            raise SystemExit("Constant-map proof acquired HOL-ZF")
        if (root in RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST or root in RELATIONAL_RETRACTION_PROXY_ROOT_ALLOWLIST
                or root in RELATIONAL_WITNESS_SYNTAX_ROOT_ALLOWLIST or root in RELATIONAL_IDENTITY_CLASS_ROOT_ALLOWLIST):
            raise SystemExit("Constant-map proof acquired an unrelated proof-data allowance")
        models = {"paper_R_bbk_model", "paper_named_bbk_model", "pbbk_model", "paper_ZF_action_model", "unknown_model"}
        blocked = (classicism_semantic_forbidden(root, models) | relational_consistency_forbidden(root)
                   | relational_retraction_proxy_forbidden(root) | relational_witness_class_forbidden(root))
        if not models <= blocked:
            raise SystemExit("Constant-map proof permits a model")
        if root in expected_raw:
            if not {"paper_R_named_H", "paper_R_named_derivable", "H_proves", "paper_named_H", "C_proves"} <= blocked:
                raise SystemExit("Raw constant mapping permits theoremhood")
        elif not ZF_PROOF_PREDICATES - {"paper_R_named_H", "paper_R_named_derivable"} <= blocked:
            raise SystemExit("Native H constant mapping permits a foreign calculus")


def check_relational_henkin_stage_policy_controls():
    expected_raw = {
        "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_full_premises_closed",
        "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_finite_premises_stage_bound",
        "theorem:Bacon_Source_Relational_Henkin_Witness_Coverage.paper_R_henkin_full_witness_axiom",
        "theorem:Bacon_Source_Relational_Henkin_Name_Stages.paper_R_henkin_signature_original_iff",
        "theorem:Bacon_Source_Relational_Henkin_Name_Stages.paper_R_henkin_signature_witness_fresh",
        "theorem:Bacon_Source_Relational_Henkin_Stage_Signature.paper_R_henkin_stage_typed_names_inj_on",
        "theorem:Bacon_Source_Relational_Henkin_Stage_Signature.paper_R_henkin_signature_family",
        "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_mono",
        "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_closed",
        "theorem:Bacon_Source_Relational_Henkin_Full_Signature.paper_R_henkin_full_language_eventually",
        "theorem:Bacon_Source_Relational_Henkin_Full_Signature.paper_R_henkin_full_closed_predicate_witness",
    }
    expected_h = {
        "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_declared_constant",
        "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_identity_domain_nonempty",
        "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_stage_consistent_full_signature",
        "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_full_premises_consistent",
        "theorem:Bacon_Source_Relational_Closed_Witness_Completeness.paper_R_closed_witness_complete_from_conditionals",
        "theorem:Bacon_Source_Relational_Closed_Henkin_Theory.paper_R_closed_maximal_Henkin",
        "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists",
        "theorem:Bacon_Source_Relational_Local_Constant_Map.paper_R_named_derivable_constant_map",
        "theorem:Bacon_Source_Relational_Local_Constant_Map.paper_R_named_derivable_injective_constant_map_iff",
        "theorem:Bacon_Source_Relational_Constant_Map_Consistency.paper_R_named_consistent_injective_constant_map_iff",
        "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_original_consistent",
        "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_premises_consistent",
    }
    expected_data = {
        "theorem:Bacon_Source_Relational_Henkin_Countable_Signature.paper_R_henkin_full_names_countable": {"paper_R_henkin_signature", "paper_R_henkin_full_signature", "ROriginal", "RWitness"},
        "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_full_premises_closed": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises"},
        "theorem:Bacon_Source_Relational_Henkin_Full_Premises.paper_R_henkin_finite_premises_stage_bound": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_premises"},
        "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_stage_consistent_full_signature": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature"},
        "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_full_premises_consistent": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises"},
        "theorem:Bacon_Source_Relational_Henkin_Witness_Coverage.paper_R_henkin_full_witness_axiom": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises"},
        "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises"},
        "theorem:Bacon_Source_Relational_Henkin_Name_Stages.paper_R_henkin_signature_original_iff": {"paper_R_henkin_signature", "ROriginal", "RWitness"},
        "theorem:Bacon_Source_Relational_Henkin_Name_Stages.paper_R_henkin_signature_witness_fresh": {"paper_R_henkin_signature", "ROriginal", "RWitness"},
        "theorem:Bacon_Source_Relational_Henkin_Stage_Signature.paper_R_henkin_stage_typed_names_inj_on": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "ROriginal", "RWitness"},
        "theorem:Bacon_Source_Relational_Henkin_Stage_Signature.paper_R_henkin_signature_family": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "ROriginal", "RWitness"},
        "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_mono": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness"},
        "theorem:Bacon_Source_Relational_Henkin_Premise_Stages.paper_R_henkin_premises_closed": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness"},
        "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_original_consistent": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness"},
        "theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_premises_consistent": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness"},
        "theorem:Bacon_Source_Relational_Henkin_Full_Signature.paper_R_henkin_full_language_eventually": {"paper_R_henkin_signature", "paper_R_henkin_full_signature", "ROriginal", "RWitness"},
        "theorem:Bacon_Source_Relational_Henkin_Full_Signature.paper_R_henkin_full_closed_predicate_witness": {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_full_signature", "ROriginal", "RWitness"},
    }
    if set(RELATIONAL_HENKIN_SYNTAX_ROOTS) != expected_raw or set(RELATIONAL_HENKIN_PROOF_ROOTS) != expected_h:
        raise SystemExit("Unexpected Henkin-stage endpoint")
    if RELATIONAL_HENKIN_DATA_CONSTANTS != {"paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises"} or RELATIONAL_HENKIN_DATA_ROOT_ALLOWLIST != expected_data:
        raise SystemExit("Henkin-stage proof-data allowance changed scope")
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        data_allowed = expected_data.get(root, set())
        data_blocked = relational_henkin_data_forbidden(root)
        if not RELATIONAL_HENKIN_DATA_CONSTANTS - data_allowed <= data_blocked or data_allowed & data_blocked:
            raise SystemExit(f"Henkin data isolation failed: {root}")
        if root in expected_raw | expected_h:
            if root in ZF_FOUNDATION_ROOTS:
                raise SystemExit("Native Henkin construction acquired HOL-ZF")
            cons = RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST.get(root, set())
            proxies = RELATIONAL_RETRACTION_PROXY_ROOT_ALLOWLIST.get(root, set())
            witness = RELATIONAL_WITNESS_SYNTAX_ROOT_ALLOWLIST.get(root, set())
            if root not in {"theorem:Bacon_Source_Relational_Henkin_Stage_Consistency.paper_R_henkin_premises_consistent", "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_stage_consistent_full_signature", "theorem:Bacon_Source_Relational_Henkin_Union_Consistency.paper_R_henkin_full_premises_consistent", "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists"} and proxies:
                raise SystemExit("Stage syntax or carrier mapping acquired retraction proxies")
            models = {"paper_R_bbk_model", "paper_named_bbk_model", "pbbk_model", "paper_ZF_action_model", "unknown_model"}
            blocked = (classicism_semantic_forbidden(root, models) | data_blocked
                       | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                       | relational_witness_class_forbidden(root))
            allowed = (cons | proxies | witness | data_allowed | RELATIONAL_CLOSED_HENKIN_ROOT_ALLOWLIST.get(root, set())
                       | RELATIONAL_IDENTITY_CLASS_ROOT_ALLOWLIST.get(root, set()))
            if not models <= blocked or allowed & blocked:
                raise SystemExit("Henkin-stage model/predicate controls failed")
            if root in expected_raw:
                if not {"paper_R_named_H", "paper_R_named_derivable", "H_proves", "paper_named_H", "C_proves"} <= blocked:
                    raise SystemExit("Henkin syntax depends on theoremhood")
            elif not ZF_PROOF_PREDICATES - {"paper_R_named_H", "paper_R_named_derivable"} - allowed <= blocked:
                raise SystemExit("Henkin proof permits a foreign calculus")


def check_relational_closed_henkin_policy_controls():
    expected = {
        "theorem:Bacon_Source_Relational_Henkin_Existential_Membership.paper_R_closed_Henkin_exists_member": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Universal_Membership.paper_R_closed_Henkin_forall_member": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_exists_class": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_forall_class": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_forall_truth": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_exists_truth": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Model.paper_R_identity_bbk_model": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_neg_truth": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_conj_truth": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_disj_truth": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_valuation_identity": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_denote_identity_truth": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_not_member": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_and_member": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_or_member": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_not": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_and": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_or": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_class": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_rep": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_declared_constant": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Henkin_Domain_Inhabitation.paper_R_closed_Henkin_identity_domain_nonempty": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Closed_Witness_Completeness.paper_R_closed_witness_complete_from_conditionals": {"paper_R_closed_constant_witness_complete"},
        "theorem:Bacon_Source_Relational_Closed_Henkin_Theory.paper_R_closed_maximal_Henkin": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
        "theorem:Bacon_Source_Relational_Closed_Henkin_Extension.paper_R_closed_Henkin_extension_exists": {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"},
    }
    if RELATIONAL_CLOSED_HENKIN_PREDICATES != {"paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory"} or RELATIONAL_CLOSED_HENKIN_ROOT_ALLOWLIST != expected:
        raise SystemExit("Closed-Henkin predicate allowance changed exact scope")
    if not set(expected) <= set(RELATIONAL_HENKIN_PROOF_ROOTS) | set(RELATIONAL_TERM_ENV_PROOF_ROOTS) | set(RELATIONAL_CANONICAL_MODEL_ROOTS):
        raise SystemExit("Closed-Henkin endpoint escaped its native R-H proof tier")
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        allowed = expected.get(root, set())
        blocked = relational_closed_henkin_forbidden(root)
        if not RELATIONAL_CLOSED_HENKIN_PREDICATES - allowed <= blocked or allowed & blocked:
            raise SystemExit(f"Closed-Henkin isolation failed: {root}")
        if root in expected:
            if root in ZF_FOUNDATION_ROOTS:
                raise SystemExit("Closed-Henkin construction acquired HOL-ZF")
            models = {"paper_R_bbk_model", "paper_named_bbk_model", "pbbk_model", "paper_ZF_action_model", "unknown_model"}
            denied = classicism_semantic_forbidden(root, models) | relational_model_boundary_forbidden(root, models) | blocked
            permitted_models = {"paper_R_bbk_model"} if root in RELATIONAL_CANONICAL_MODEL_ROOTS else set()
            if not models - permitted_models <= denied or allowed & denied:
                raise SystemExit("Closed-Henkin model/predicate controls failed")


def check_relational_term_env_policy_controls():
    expected_raw = {
        "theorem:Bacon_Source_Relational_Environment_Update_Syntax.paper_R_environment_subst_update_closed",
        "theorem:Bacon_Source_Relational_Environment_Beta_Syntax.paper_R_environment_subst_beta_commute",
        "theorem:Bacon_Source_Relational_Environment_Contractions.paper_R_environment_subst_beta_contract",
        "theorem:Bacon_Source_Relational_Environment_Contractions.paper_R_environment_subst_eta_contract",
        "theorem:Bacon_Source_Relational_Environment_Conversion.paper_R_environment_subst_raw_conversion",
        "theorem:Bacon_Source_Relational_Term_Type.paper_R_term_type_eq",
        "theorem:Bacon_Source_Relational_Environment_Substitution.paper_R_environment_subst_locality",
        "theorem:Bacon_Source_Relational_Environment_Substitution.paper_R_environment_subst_fv",
        "theorem:Bacon_Source_Relational_Environment_Substitution_Typing.paper_R_environment_subst_type",
        "theorem:Bacon_Source_Relational_Representative_Assignments.paper_R_representative_assignment_domain",
        "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_locality",
    }
    expected_h = {
        "theorem:Bacon_Source_Relational_Environment_Finite_Identity.paper_R_environment_subst_assignment_identity",
        "theorem:Bacon_Source_Relational_Arbitrary_Representatives.paper_R_identity_denote_arbitrary_representatives",
        "theorem:Bacon_Source_Relational_Environment_Update_Identity.paper_R_environment_subst_update_identity",
        "theorem:Bacon_Source_Relational_Quantifier_Duality.paper_R_named_H_quantifier_duality",
        "theorem:Bacon_Source_Relational_Henkin_Existential_Membership.paper_R_closed_Henkin_exists_member",
        "theorem:Bacon_Source_Relational_Henkin_Universal_Membership.paper_R_closed_Henkin_forall_member",
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_exists_class",
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_forall_class",
        "theorem:Bacon_Source_Relational_Identity_Fresh_Application.paper_R_identity_denote_fresh_application",
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_forall_truth",
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_exists_truth",
        "theorem:Bacon_Source_Relational_Identity_Conversion.paper_R_identity_denote_beta_eta",
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_neg_truth",
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_conj_truth",
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_disj_truth",
        "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_valuation_identity",
        "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_denote_identity_truth",
        "theorem:Bacon_Source_Relational_Identity_Application_Congruence.paper_R_identity_denote_application_cong",
        "theorem:Bacon_Source_Relational_Boolean_PC.paper_R_named_H_PC_template",
        "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_not_member",
        "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_and_member",
        "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_or_member",
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_not",
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_and",
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_or",
        "theorem:Bacon_Source_Relational_Representative_Assignments.paper_R_representative_assignment_typed",
        "theorem:Bacon_Source_Relational_Environment_Substitution_Typing.paper_R_representative_substitution_closed_terms",
        "theorem:Bacon_Source_Relational_Propositional_Identity_Derivations.paper_R_named_derivable_propositional_identity",
        "theorem:Bacon_Source_Relational_Propositional_Identity_Derivations.paper_R_closed_propositional_identity_membership",
        "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_class",
        "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_rep",
        "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_type",
        "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_var",
        "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_App",
    }
    expected_data = {
        "theorem:Bacon_Source_Relational_Environment_Finite_Identity.paper_R_environment_subst_assignment_identity": {"paper_R_environment_subst", "paper_R_closed_term_assignment"},
        "theorem:Bacon_Source_Relational_Arbitrary_Representatives.paper_R_identity_denote_arbitrary_representatives": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Environment_Update_Syntax.paper_R_environment_subst_update_closed": {"paper_R_environment_subst"},
        "theorem:Bacon_Source_Relational_Environment_Update_Identity.paper_R_environment_subst_update_identity": {"paper_R_environment_subst", "paper_R_closed_term_assignment"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_exists_class": {"paper_R_identity_valuation"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_forall_class": {"paper_R_identity_valuation"},
        "theorem:Bacon_Source_Relational_Identity_Fresh_Application.paper_R_identity_denote_fresh_application": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_forall_truth": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_exists_truth": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Identity_Model.paper_R_identity_bbk_model": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_BBK_Constant_Pullback.paper_R_bbk_constant_pullback": {"paper_R_constant_pullback_denote"},
        "theorem:Bacon_Source_Relational_Environment_Beta_Syntax.paper_R_environment_subst_beta_commute": {"paper_R_environment_subst"},
        "theorem:Bacon_Source_Relational_Environment_Contractions.paper_R_environment_subst_beta_contract": {"paper_R_environment_subst"},
        "theorem:Bacon_Source_Relational_Environment_Contractions.paper_R_environment_subst_eta_contract": {"paper_R_environment_subst"},
        "theorem:Bacon_Source_Relational_Environment_Conversion.paper_R_environment_subst_raw_conversion": {"paper_R_environment_subst", "paper_R_closed_term_assignment"},
        "theorem:Bacon_Source_Relational_Identity_Conversion.paper_R_identity_denote_beta_eta": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_neg_truth": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_conj_truth": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_disj_truth": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_valuation_identity": {"paper_R_identity_valuation"},
        "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_denote_identity_truth": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Identity_Application_Congruence.paper_R_identity_denote_application_cong": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_not": {"paper_R_identity_valuation"},
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_and": {"paper_R_identity_valuation"},
        "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_or": {"paper_R_identity_valuation"},
        "theorem:Bacon_Source_Relational_Term_Type.paper_R_term_type_eq": {"paper_R_term_type"},
        "theorem:Bacon_Source_Relational_Environment_Substitution.paper_R_environment_subst_locality": {"paper_R_environment_subst"},
        "theorem:Bacon_Source_Relational_Environment_Substitution.paper_R_environment_subst_fv": {"paper_R_environment_subst"},
        "theorem:Bacon_Source_Relational_Environment_Substitution_Typing.paper_R_environment_subst_type": {"paper_R_environment_subst"},
        "theorem:Bacon_Source_Relational_Representative_Assignments.paper_R_representative_assignment_domain": {"paper_R_representative_assignment"},
        "theorem:Bacon_Source_Relational_Representative_Assignments.paper_R_representative_assignment_typed": {"paper_R_representative_assignment", "paper_R_closed_term_assignment"},
        "theorem:Bacon_Source_Relational_Environment_Substitution_Typing.paper_R_representative_substitution_closed_terms": {"paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment"},
        "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_class": {"paper_R_identity_valuation"},
        "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_rep": {"paper_R_identity_valuation"},
        "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_type": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_var": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_locality": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_identity_denote"},
        "theorem:Bacon_Source_Relational_Identity_Interpretation.paper_R_identity_denote_App": {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_denote"},
    }
    if set(RELATIONAL_TERM_ENV_RAW_ROOTS) != expected_raw or set(RELATIONAL_TERM_ENV_PROOF_ROOTS) != expected_h:
        raise SystemExit("Unexpected canonical term/environment endpoint")
    if RELATIONAL_TERM_ENV_CONSTANTS != {"paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote", "paper_R_constant_pullback_denote"} or RELATIONAL_TERM_ENV_ROOT_ALLOWLIST != expected_data:
        raise SystemExit("Canonical term/environment data allowance changed scope")
    henkin_membership_roots = {"theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_class", "theorem:Bacon_Source_Relational_Identity_Valuation.paper_R_identity_valuation_rep", "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_not_member", "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_and_member", "theorem:Bacon_Source_Relational_Henkin_Boolean_Membership.paper_R_closed_Henkin_or_member", "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_not", "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_and", "theorem:Bacon_Source_Relational_Identity_Boolean_Valuation.paper_R_identity_valuation_or", "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_neg_truth", "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_conj_truth", "theorem:Bacon_Source_Relational_Identity_Propositional_Truth.paper_R_identity_denote_disj_truth", "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_valuation_identity", "theorem:Bacon_Source_Relational_Identity_Identity_Truth.paper_R_identity_denote_identity_truth", "theorem:Bacon_Source_Relational_Henkin_Existential_Membership.paper_R_closed_Henkin_exists_member", "theorem:Bacon_Source_Relational_Henkin_Universal_Membership.paper_R_closed_Henkin_forall_member", "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_exists_class", "theorem:Bacon_Source_Relational_Identity_Quantifier_Valuation.paper_R_identity_valuation_forall_class", "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_forall_truth", "theorem:Bacon_Source_Relational_Identity_Quantifier_Truth.paper_R_identity_denote_exists_truth"}
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        allowed_data = expected_data.get(root, set())
        data_blocked = relational_term_env_forbidden(root)
        if not RELATIONAL_TERM_ENV_CONSTANTS - allowed_data <= data_blocked or allowed_data & data_blocked:
            raise SystemExit(f"Canonical term/environment data isolation failed: {root}")
        if root in expected_raw | expected_h:
            if root in ZF_FOUNDATION_ROOTS:
                raise SystemExit("Canonical term/environment proof acquired HOL-ZF")
            if root in RELATIONAL_RETRACTION_PROXY_ROOT_ALLOWLIST or root in RELATIONAL_WITNESS_SYNTAX_ROOT_ALLOWLIST or root in RELATIONAL_HENKIN_DATA_ROOT_ALLOWLIST:
                raise SystemExit("Canonical interpretation acquired retraction or staged construction data")
            cons = RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST.get(root, set())
            henkin = RELATIONAL_CLOSED_HENKIN_ROOT_ALLOWLIST.get(root, set())
            if root not in henkin_membership_roots and (cons or henkin):
                raise SystemExit("Structural interpretation acquired Henkin or consistency assumptions")
            classes = RELATIONAL_IDENTITY_CLASS_ROOT_ALLOWLIST.get(root, set())
            if root in {"theorem:Bacon_Source_Relational_Term_Type.paper_R_term_type_eq", "theorem:Bacon_Source_Relational_Environment_Substitution.paper_R_environment_subst_locality", "theorem:Bacon_Source_Relational_Environment_Substitution.paper_R_environment_subst_fv", "theorem:Bacon_Source_Relational_Environment_Substitution_Typing.paper_R_environment_subst_type", "theorem:Bacon_Source_Relational_Propositional_Identity_Derivations.paper_R_named_derivable_propositional_identity", "theorem:Bacon_Source_Relational_Boolean_PC.paper_R_named_H_PC_template", "theorem:Bacon_Source_Relational_Environment_Beta_Syntax.paper_R_environment_subst_beta_commute", "theorem:Bacon_Source_Relational_Environment_Contractions.paper_R_environment_subst_beta_contract", "theorem:Bacon_Source_Relational_Environment_Contractions.paper_R_environment_subst_eta_contract", "theorem:Bacon_Source_Relational_Quantifier_Duality.paper_R_named_H_quantifier_duality"} and classes:
                raise SystemExit("Raw type/substitution or native LL proof acquired class data")
            allowed = allowed_data | cons | henkin | classes | RELATIONAL_REP_CHOICE_ROOT_ALLOWLIST.get(root, set())
            models = {"paper_R_bbk_model", "paper_named_bbk_model", "pbbk_model", "paper_ZF_action_model", "unknown_model"}
            blocked = (classicism_semantic_forbidden(root, models) | data_blocked
                       | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                       | relational_witness_class_forbidden(root) | relational_closed_henkin_forbidden(root)
                       | relational_henkin_data_forbidden(root))
            if not models <= blocked or allowed & blocked:
                raise SystemExit("Canonical term/environment model/predicate control failed")
            if root in expected_raw:
                if not {"paper_R_named_H", "paper_R_named_derivable", "H_proves", "paper_named_H", "C_proves"} <= blocked:
                    raise SystemExit("Raw type/environment equality acquired theoremhood")
            elif not ZF_PROOF_PREDICATES - {"paper_R_named_H", "paper_R_named_derivable"} - allowed <= blocked:
                raise SystemExit("Canonical term/environment proof permits foreign proof dependencies")


def check_relational_model_boundary_policy_controls():
    if set(RELATIONAL_CANONICAL_MODEL_ROOTS) != {"theorem:Bacon_Source_Relational_Identity_Model.paper_R_identity_bbk_model"} or set(RELATIONAL_CONSTANT_PULLBACK_ROOTS) != {"theorem:Bacon_Source_Relational_BBK_Constant_Pullback.paper_R_bbk_constant_pullback"}:
        raise SystemExit("Unexpected pure R-BBK construction/pullback boundary")
    for root in RELATIONAL_CANONICAL_MODEL_ROOTS + RELATIONAL_CONSTANT_PULLBACK_ROOTS:
        if root in ZF_FOUNDATION_ROOTS or root in RELATIONAL_H_PROOF_ROOTS:
            raise SystemExit("R-BBK construction/pullback escaped its pure semantic boundary")
        if root in RELATIONAL_RETRACTION_PROXY_ROOT_ALLOWLIST or root in RELATIONAL_HENKIN_DATA_ROOT_ALLOWLIST or root in RELATIONAL_WITNESS_SYNTAX_ROOT_ALLOWLIST:
            raise SystemExit("R-BBK constructor gained staged construction or proof-retraction assumptions")
        if root in RELATIONAL_CONSTANT_PULLBACK_ROOTS:
            if (root in RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST or root in RELATIONAL_CLOSED_HENKIN_ROOT_ALLOWLIST
                    or root in RELATIONAL_IDENTITY_CLASS_ROOT_ALLOWLIST):
                raise SystemExit("R-BBK pullback gained canonical or Henkin premises")
            if RELATIONAL_TERM_ENV_ROOT_ALLOWLIST.get(root) != {"paper_R_constant_pullback_denote"}:
                raise SystemExit("R-BBK pullback gained unrelated canonical interpretation data")
        models = {"paper_R_bbk_model", "paper_named_bbk_model", "pbbk_model", "paper_ZF_action_model", "unknown_model"}
        blocked = (relational_model_boundary_forbidden(root, models) | zf_action_stage_forbidden(root)
                   | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                   | relational_witness_class_forbidden(root) | relational_closed_henkin_forbidden(root)
                   | relational_henkin_data_forbidden(root) | relational_term_env_forbidden(root))
        if not models - {"paper_R_bbk_model"} <= blocked or "paper_R_bbk_model" in blocked:
            raise SystemExit("Pure R-BBK model predicate boundary failed")
        if not {"paper_R_classicism_proves", "paper_R_equivalence_proves", "H_proves", "paper_named_H", "pH_proves", "C_proves"} <= blocked:
            raise SystemExit("Pure R-BBK constructor/pullback permits a foreign proof")
        native = {"paper_R_named_H", "paper_R_named_derivable"}
        if root in RELATIONAL_CONSTANT_PULLBACK_ROOTS and not native <= blocked:
            raise SystemExit("R-BBK pullback acquired theoremhood")
        if root in RELATIONAL_CANONICAL_MODEL_ROOTS and native & blocked:
            raise SystemExit("Canonical model native proof dependencies were forbidden")


def check_relational_model_existence_policy_controls():
    expected = {
        "theorem:Bacon_Source_Relational_H_Theory_Model_Existence.paper_R_H_theory_model_existence": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_named_consistent", "paper_R_named_top", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_H_Theory_Bounded_Model.paper_R_H_theory_bounded_model_existence": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_consistent", "paper_R_named_top", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Bounded_Model_Existence.paper_R_BBK_bounded_model_existence": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_add_constant", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_consistent", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Nat_Model_Existence.paper_R_BBK_nat_model_existence": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_add_constant", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_count_tree", "paper_R_named_consistent", "paper_R_named_count_tree", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Nat_Countermodel.paper_R_nat_closed_countermodel": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_add_constant", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_count_tree", "paper_R_named_consistent", "paper_R_named_count_tree", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Nat_Completeness.paper_R_nat_closed_strong_completeness": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_add_constant", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_count_tree", "paper_R_named_consistent", "paper_R_named_count_tree", "paper_R_nat_BBK_consequence", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Countable_Model_Existence.paper_R_BBK_countable_union_model_existence": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension", "paper_R_H_retraction_support", "paper_R_local_retraction_support", "paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms", "paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application", "paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises", "paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory", "paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote", "paper_R_constant_pullback_denote", "paper_R_logical_count_tree", "paper_R_named_count_tree"},
        "theorem:Bacon_Source_Relational_Model_Existence.paper_R_BBK_model_existence": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension", "paper_R_H_retraction_support", "paper_R_local_retraction_support", "paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms", "paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application", "paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises", "paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory", "paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote", "paper_R_constant_pullback_denote"},
        "theorem:Bacon_Source_Relational_Closed_Countermodel.paper_R_closed_countermodel": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension", "paper_R_H_retraction_support", "paper_R_local_retraction_support", "paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms", "paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application", "paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises", "paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory", "paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote", "paper_R_constant_pullback_denote"},
        "theorem:Bacon_Source_Relational_Closed_Completeness.paper_R_closed_strong_completeness": {"paper_R_named_consistent", "paper_R_sentence", "paper_R_closed_theory", "paper_R_closed_maximal_extension", "paper_R_H_retraction_support", "paper_R_local_retraction_support", "paper_R_add_constant", "paper_R_witness_axiom", "paper_R_witness_family_signature", "paper_R_witness_family_axioms", "paper_R_closed_terms", "paper_R_identity_relation", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_identity_rep", "paper_R_identity_application", "paper_R_henkin_signature", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_henkin_stage_axioms", "paper_R_henkin_premises", "ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_full_premises", "paper_R_closed_constant_witness_complete", "paper_R_closed_Henkin_theory", "paper_R_term_type", "paper_R_environment_subst", "paper_R_representative_assignment", "paper_R_closed_term_assignment", "paper_R_identity_valuation", "paper_R_identity_denote", "paper_R_constant_pullback_denote", "paper_R_closed_BBK_consequence"},
    }
    if RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST != expected or set(RELATIONAL_MODEL_EXISTENCE_ROOTS) != set(expected):
        raise SystemExit("Native model-existence data exception changed exact scope")
    forbidden_payload = ZF_PROOF_PREDICATES - set().union(*expected.values())
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        permitted = RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
        if root not in expected and permitted:
            raise SystemExit("Older root gained complete-construction data")
        if root in expected:
            if root in ZF_FOUNDATION_ROOTS or root in RELATIONAL_H_PROOF_ROOTS:
                raise SystemExit("Pure R completeness escaped its semantic foundation tier")
            models = {"paper_R_bbk_model", "paper_named_bbk_model", "pbbk_model", "paper_ZF_action_model", "unknown_model"}
            blocked = (relational_model_boundary_forbidden(root, models) | zf_action_stage_forbidden(root)
                       | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                       | relational_witness_class_forbidden(root) | relational_henkin_data_forbidden(root)
                       | relational_closed_henkin_forbidden(root) | relational_term_env_forbidden(root) | {"paper_R_closed_BBK_consequence"})
            blocked -= permitted
            if not models - {"paper_R_bbk_model"} <= blocked or "paper_R_bbk_model" in blocked:
                raise SystemExit("Native model-existence model boundary failed")
            if not forbidden_payload - {"paper_R_named_H", "paper_R_named_derivable"} <= blocked:
                raise SystemExit("Native model-existence acquired a foreign proof")
            if {"paper_R_named_H", "paper_R_named_derivable"} & blocked:
                raise SystemExit("Native model-existence proof dependencies forbidden")
            if root != "theorem:Bacon_Source_Relational_Closed_Completeness.paper_R_closed_strong_completeness" and "paper_R_closed_BBK_consequence" not in blocked:
                raise SystemExit("Model existence/countermodel gained semantic consequence shortcut")


def check_relational_representative_counting_policy_controls():
    expected_count = {
        "theorem:Bacon_Source_Relational_Nat_Model_Existence.paper_R_BBK_nat_model_existence",
        "theorem:Bacon_Source_Relational_Nat_Countermodel.paper_R_nat_closed_countermodel",
        "theorem:Bacon_Source_Relational_Nat_Completeness.paper_R_nat_closed_strong_completeness",
        "theorem:Bacon_Source_Relational_Admitted_Terms_Countable.paper_R_admitted_terms_countable",
        "theorem:Bacon_Source_Relational_Henkin_Countable_Signature.paper_R_henkin_full_names_countable",
        "theorem:Bacon_Source_Relational_Identity_Countable_Domains.paper_R_identity_domains_countable",
        "theorem:Bacon_Source_Relational_Countable_Model_Existence.paper_R_BBK_countable_union_model_existence",
    }
    expected_rep_data = {
        "theorem:Bacon_Source_Relational_Environment_Finite_Identity.paper_R_environment_subst_assignment_identity": {"paper_R_environment_paste"},
        "theorem:Bacon_Source_Relational_Arbitrary_Representatives.paper_R_identity_denote_arbitrary_representatives": {"paper_R_environment_paste", "paper_R_represents_class_assignment"},
    }
    expected_codes = {
        "theorem:Bacon_Source_Relational_Nat_Model_Existence.paper_R_BBK_nat_model_existence": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
        "theorem:Bacon_Source_Relational_Nat_Countermodel.paper_R_nat_closed_countermodel": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
        "theorem:Bacon_Source_Relational_Nat_Completeness.paper_R_nat_closed_strong_completeness": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
        "theorem:Bacon_Source_Relational_Admitted_Terms_Countable.paper_R_admitted_terms_countable": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
        "theorem:Bacon_Source_Relational_Henkin_Countable_Signature.paper_R_henkin_full_names_countable": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
        "theorem:Bacon_Source_Relational_Identity_Countable_Domains.paper_R_identity_domains_countable": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
        "theorem:Bacon_Source_Relational_Countable_Model_Existence.paper_R_BBK_countable_union_model_existence": {"paper_R_logical_count_tree", "paper_R_named_count_tree"},
    }
    if set(RELATIONAL_COUNTING_ROOTS) != expected_count or set(RELATIONAL_COUNTING_RAW_ROOTS) != expected_count - {"theorem:Bacon_Source_Relational_Countable_Model_Existence.paper_R_BBK_countable_union_model_existence", "theorem:Bacon_Source_Relational_Nat_Model_Existence.paper_R_BBK_nat_model_existence", "theorem:Bacon_Source_Relational_Nat_Countermodel.paper_R_nat_closed_countermodel", "theorem:Bacon_Source_Relational_Nat_Completeness.paper_R_nat_closed_strong_completeness"}:
        raise SystemExit("Unexpected native counting endpoint")
    if RELATIONAL_REP_CHOICE_CONSTANTS != {"paper_R_environment_paste", "paper_R_represents_class_assignment"} or RELATIONAL_REP_CHOICE_ROOT_ALLOWLIST != expected_rep_data:
        raise SystemExit("Representative-choice data allowance changed scope")
    if RELATIONAL_COUNT_CODE_CONSTANTS != {"paper_R_logical_count_tree", "paper_R_named_count_tree"} or RELATIONAL_COUNT_CODE_ROOT_ALLOWLIST != expected_codes:
        raise SystemExit("Native syntax-code data allowance changed scope")
    generic = {"pHct_Atom", "pHct_Unary", "pHct_Binary", "pHct_type_code"}
    if RELATIONAL_COUNT_GENERIC_PHCT_CONSTANTS != generic:
        raise SystemExit("Generic F-side syntax coding whitelist changed")
    probes = generic | {"pHct_term_tree", "pHct_name_tree", "pHct_universe", "pHct_code",
                        "pHct_future_model_code", "pH_closed_Henkin", "pHc_domain"}
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        allowed = expected_rep_data.get(root, set()) | expected_codes.get(root, set())
        denied = relational_rep_count_data_forbidden(root)
        if not (RELATIONAL_REP_CHOICE_CONSTANTS | RELATIONAL_COUNT_CODE_CONSTANTS) - allowed <= denied or allowed & denied:
            raise SystemExit(f"Representative/counting data isolation failed: {root}")
        if root in expected_count:
            if root in ZF_FOUNDATION_ROOTS:
                raise SystemExit("Native counting proof acquired HOL-ZF")
            coding_denied = relational_counting_coding_forbidden(root, probes)
            if generic & coding_denied or not probes - generic <= coding_denied:
                raise SystemExit("Countability acquired a nongeneric F coding shortcut")
            if root in RELATIONAL_COUNTING_RAW_ROOTS:
                models = {"paper_R_bbk_model", "paper_named_bbk_model", "pbbk_model", "paper_ZF_action_model", "unknown_model"}
                blocked = classicism_semantic_forbidden(root, models)
                if not models | {"paper_R_named_H", "paper_R_named_derivable", "H_proves", "paper_named_H", "C_proves"} <= blocked:
                    raise SystemExit("Raw countability acquired a model or theoremhood")
            else:
                permitted = RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST[root]
                if generic & permitted or any(name.startswith("pHct_") for name in permitted):
                    raise SystemExit("Countable model construction exempts imported F coding")


def check_relational_recoding_policy_controls():
    expected_raw = {"theorem:Bacon_Source_Relational_Recoding_Assignments.paper_R_recode_inverse_assignment_typed", "theorem:Bacon_Source_Relational_Recoding_Assignments.paper_R_recode_assignment_inverse_left", "theorem:Bacon_Source_Relational_Recoding_Assignments.paper_R_recode_assignment_inverse_right"}
    expected_semantic = {"theorem:Bacon_Source_Relational_Recoding_Structure.paper_R_bbk_model.paper_R_recode_denote_application", "theorem:Bacon_Source_Relational_Recoding_Truth.paper_R_bbk_model.paper_R_recode_identity_truth", "theorem:Bacon_Source_Relational_Recoding_Quantifiers.paper_R_bbk_model.paper_R_recode_forall_truth", "theorem:Bacon_Source_Relational_Recoding_Quantifiers.paper_R_bbk_model.paper_R_recode_exists_truth", "theorem:Bacon_Source_Relational_Recoding_Model.paper_R_bbk_model.paper_R_recode_model", "theorem:Bacon_Source_Relational_Recoding_Validity.paper_R_bbk_model.paper_R_recode_valid_iff"}
    nat_roots = {"theorem:Bacon_Source_Relational_Nat_Model_Existence.paper_R_BBK_nat_model_existence", "theorem:Bacon_Source_Relational_Nat_Countermodel.paper_R_nat_closed_countermodel", "theorem:Bacon_Source_Relational_Nat_Completeness.paper_R_nat_closed_strong_completeness"}
    expected_data = {
        "theorem:Bacon_Source_Relational_Recoding_Assignments.paper_R_recode_inverse_assignment_typed": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse"},
        "theorem:Bacon_Source_Relational_Recoding_Assignments.paper_R_recode_assignment_inverse_left": {"paper_R_recode_assignment", "paper_R_recode_inverse"},
        "theorem:Bacon_Source_Relational_Recoding_Assignments.paper_R_recode_assignment_inverse_right": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse"},
        "theorem:Bacon_Source_Relational_Recoding_Structure.paper_R_bbk_model.paper_R_recode_denote_application": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote"},
        "theorem:Bacon_Source_Relational_Recoding_Truth.paper_R_bbk_model.paper_R_recode_identity_truth": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote", "paper_R_recode_valuation"},
        "theorem:Bacon_Source_Relational_Recoding_Quantifiers.paper_R_bbk_model.paper_R_recode_forall_truth": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote", "paper_R_recode_valuation"},
        "theorem:Bacon_Source_Relational_Recoding_Quantifiers.paper_R_bbk_model.paper_R_recode_exists_truth": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote", "paper_R_recode_valuation"},
        "theorem:Bacon_Source_Relational_Recoding_Model.paper_R_bbk_model.paper_R_recode_model": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote", "paper_R_recode_valuation"},
        "theorem:Bacon_Source_Relational_Recoding_Validity.paper_R_bbk_model.paper_R_recode_valid_iff": {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote", "paper_R_recode_valuation"},
    }
    if set(RELATIONAL_RECODING_RAW_ROOTS) != expected_raw or set(RELATIONAL_RECODING_MODEL_ROOTS) != expected_semantic:
        raise SystemExit("Unexpected R carrier-recoding root")
    if RELATIONAL_RECODING_DATA_CONSTANTS != {"paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse", "paper_R_recode_denote", "paper_R_recode_valuation"} or RELATIONAL_RECODING_DATA_ROOT_ALLOWLIST != expected_data:
        raise SystemExit("Recoding data allowance changed exact scope")
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        allowed_data = expected_data.get(root, set())
        denied_data = relational_recoding_data_forbidden(root)
        if not RELATIONAL_RECODING_DATA_CONSTANTS - allowed_data <= denied_data or allowed_data & denied_data:
            raise SystemExit(f"Recoding data isolation failed: {root}")
        if root in expected_raw | expected_semantic | nat_roots:
            if root in ZF_FOUNDATION_ROOTS:
                raise SystemExit("R carrier recoding acquired HOL-ZF")
            models = {"paper_R_bbk_model", "paper_named_bbk_model", "pbbk_model", "paper_ZF_action_model", "unknown_model"}
            blocked = (classicism_semantic_forbidden(root, models) | relational_model_boundary_forbidden(root, models)
                       | zf_action_stage_forbidden(root) | denied_data | relational_consistency_forbidden(root)
                       | relational_retraction_proxy_forbidden(root) | relational_witness_class_forbidden(root)
                       | relational_henkin_data_forbidden(root) | relational_closed_henkin_forbidden(root)
                       | relational_term_env_forbidden(root) | relational_rep_count_data_forbidden(root)
                       | {"paper_R_closed_BBK_consequence", "paper_R_nat_BBK_consequence",
                          "paper_R_classicism_proves", "paper_R_equivalence_proves"})
            blocked -= RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
            permitted_model = {"paper_R_bbk_model"} if root in expected_semantic | nat_roots else set()
            if not models - permitted_model <= blocked or permitted_model & blocked:
                raise SystemExit("R recoding model boundary failed")
            native = {"paper_R_named_H", "paper_R_named_derivable"}
            if root in expected_raw | expected_semantic and not native <= blocked:
                raise SystemExit("Data/model recoding acquired theoremhood")
            if not {"H_proves", "pH_proves", "paper_named_H", "C_proves", "paper_R_classicism_proves", "paper_R_equivalence_proves"} <= blocked:
                raise SystemExit("R recoding acquired a foreign calculus")
            if root != "theorem:Bacon_Source_Relational_Nat_Completeness.paper_R_nat_closed_strong_completeness" and "paper_R_nat_BBK_consequence" not in blocked:
                raise SystemExit("Nat semantic consequence escaped its sole completeness root")
            if root in expected_semantic:
                if any(root in table for table in (RELATIONAL_CONSISTENCY_ROOT_ALLOWLIST,
                        RELATIONAL_CLOSED_HENKIN_ROOT_ALLOWLIST, RELATIONAL_IDENTITY_CLASS_ROOT_ALLOWLIST,
                        RELATIONAL_HENKIN_DATA_ROOT_ALLOWLIST, RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST)):
                    raise SystemExit("Supplied-model recoding acquired canonical construction premises")
    # Inspect the ACTUAL construction dictionary, not another table that
    # happens to contain the same root key with only syntax-code data.
    native_base = RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST["theorem:Bacon_Source_Relational_Countable_Model_Existence.paper_R_BBK_countable_union_model_existence"]
    required_base = native_base | RELATIONAL_RECODING_DATA_CONSTANTS
    for root in nat_roots:
        permitted = RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
        if not native_base <= permitted:
            raise SystemExit("Nat model construction omits its native Henkin/canonical construction base")
        if "paper_R_closed_BBK_consequence" in permitted:
            raise SystemExit("Nat construction permits the old canonical-carrier consequence predicate")
        expected_nat = required_base | (
            {"paper_R_nat_BBK_consequence"} if root == "theorem:Bacon_Source_Relational_Nat_Completeness.paper_R_nat_closed_strong_completeness" else set())
        if permitted != expected_nat:
            raise SystemExit("Nat model construction allowance differs from native base plus recoding")
        if not {"paper_R_logical_count_tree", "paper_R_named_count_tree"} <= permitted:
            raise SystemExit("Nat model construction lacks its checked count data")
        if any(name.startswith("pHct_") for name in permitted):
            raise SystemExit("Nat model construction exempts nongeneric F coding")


def check_relational_cardinal_c_preparation_policy_controls():
    expected_c = (
        "theorem:Bacon_Source_Relational_Vector_Proof_Syntax.paper_R_named_lam_vec_self_beta",
        "theorem:Bacon_Source_Relational_Vector_Identity_Recovery.paper_R_named_identity_from_lam_vec",
        "theorem:Bacon_Source_Relational_Closed_LE_Generators.paper_R_local_H_in_classicism",
        "theorem:Bacon_Source_Relational_Closed_LE_Generators.paper_R_classicism_LE_closed_generator",
    )
    expected_raw = (
        "theorem:Bacon_Source_Relational_Admitted_Syntax_Cardinal.paper_R_admitted_syntax_cardinal_bound",
        "theorem:Bacon_Source_Relational_Henkin_Cardinal_Signature.paper_R_henkin_full_names_cardinal_bound",
        "theorem:Bacon_Source_Relational_Identity_Cardinal_Domains.paper_R_identity_domains_cardinal_bound",
    )
    expected_model = "theorem:Bacon_Source_Relational_Bounded_Model_Existence.paper_R_BBK_bounded_model_existence"
    expected_codes = {"paper_R_finite_syntax_code", "paper_R_logical_nat_code", "paper_R_type_nat_code"}
    expected_aux = {
        "theorem:Bacon_Source_Relational_Admitted_Syntax_Cardinal.paper_R_admitted_syntax_cardinal_bound": set(),
        "theorem:Bacon_Source_Relational_Henkin_Cardinal_Signature.paper_R_henkin_full_names_cardinal_bound": {"ROriginal", "RWitness", "paper_R_henkin_full_signature", "paper_R_henkin_signature"},
        "theorem:Bacon_Source_Relational_Identity_Cardinal_Domains.paper_R_identity_domains_cardinal_bound": {"paper_R_closed_terms", "paper_R_identity_class", "paper_R_identity_domain", "paper_R_term_type"},
    }
    if (RELATIONAL_C_PREPARATION_ROOTS != expected_c
            or RELATIONAL_C_PREPARATION_C_ROOTS != expected_c[2:]
            or RELATIONAL_CARDINAL_RAW_ROOTS != expected_raw
            or RELATIONAL_CARDINAL_MODEL_ROOT != expected_model
            or RELATIONAL_CARDINAL_CODE_CONSTANTS != expected_codes
            or RELATIONAL_CARDINAL_AUX_DATA_ALLOWLIST != expected_aux):
        raise SystemExit("Cardinal/C preparation root or data scope changed")
    native_base = RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST[
        "theorem:Bacon_Source_Relational_Model_Existence.paper_R_BBK_model_existence"]
    expected_construction = native_base | {
        "paper_R_recode_domain", "paper_R_recode_assignment", "paper_R_recode_inverse",
        "paper_R_recode_denote", "paper_R_recode_valuation",
    } | expected_codes
    permitted = RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(expected_model, set())
    if not native_base <= permitted or permitted != expected_construction:
        raise SystemExit("Bounded model lacks exact native construction plus recoding/cardinal codes")
    excluded = {"paper_R_logical_count_tree", "paper_R_named_count_tree",
                "paper_R_closed_BBK_consequence", "paper_R_nat_BBK_consequence"}
    if permitted & excluded or any(name.startswith(("pHct_", "pHc_")) for name in permitted):
        raise SystemExit("Bounded model gained countable/F coding or semantic consequence")
    models = {"paper_R_bbk_model", "paper_named_bbk_model", "paper_ZF_action_model",
              "pbbk_model", "unknown_model"}
    probes = {"pHct_Atom", "pHct_type_code", "pHct_future_code", "pHc_domain",
              "pH_closed_Henkin", "pH_countable_closed_Henkin"} | excluded
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        data_blocked = relational_cardinal_data_forbidden(root)
        data_blocked -= RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
        if root in expected_raw or root == expected_model or root == RELATIONAL_H_THEORY_MODEL_ROOTS[1]:
            if data_blocked & expected_codes:
                raise SystemExit("Cardinal endpoint lost its own syntax codes")
            if root in ZF_FOUNDATION_ROOTS:
                raise SystemExit("Pure HOL cardinal endpoint acquired HOL-ZF")
            forbidden_codes = relational_cardinal_coding_forbidden(root, probes)
            if not probes - {"paper_R_closed_BBK_consequence", "paper_R_nat_BBK_consequence"} <= forbidden_codes:
                raise SystemExit("Cardinal construction gained an F/counting-code shortcut")
        elif not expected_codes <= data_blocked:
            raise SystemExit("Older endpoint gained new cardinal syntax data")
        if root in expected_raw:
            blocked = (classicism_semantic_forbidden(root, models)
                       | relational_consistency_forbidden(root)
                       | relational_retraction_proxy_forbidden(root)
                       | relational_witness_class_forbidden(root)
                       | relational_henkin_data_forbidden(root)
                       | relational_closed_henkin_forbidden(root)
                       | relational_term_env_forbidden(root)
                       | relational_recoding_data_forbidden(root))
            blocked -= expected_aux[root]
            required = (models | {"paper_R_named_H", "paper_R_named_derivable",
                        "paper_R_classicism_proves", "paper_R_equivalence_proves"}
                        | RELATIONAL_CONSISTENCY_PREDICATES | RELATIONAL_CLOSED_HENKIN_PREDICATES)
            # The ordinary main-loop C guard is checked explicitly here.
            blocked |= {"paper_R_classicism_proves", "paper_R_equivalence_proves"}
            if not required <= blocked or expected_aux[root] & blocked:
                raise SystemExit("Raw cardinal bound acquired theoremhood, consistency or a model")
        if root in expected_c:
            allowed = (set() if root == expected_c[0]
                       else {"paper_R_named_H", "paper_R_named_derivable"})
            if root in expected_c[2:]:
                allowed.add("paper_R_classicism_proves")
            blocked = relational_c_preparation_forbidden(root, models)
            if not (ZF_PROOF_PREDICATES - allowed) | models <= blocked or allowed & blocked:
                raise SystemExit("Native C preparation crossed its exact proof boundary")
            if not {"paper_R_equivalence_proves", "named_beta_eta_in_language"} <= blocked:
                raise SystemExit("Native C preparation gained Equivalence or F conversion")
            if root in ZF_FOUNDATION_ROOTS:
                raise SystemExit("Native C preparation acquired HOL-ZF")


def check_relational_a2_base_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_Classicism_A2_H.paper_R_classicism_A2_H",
        "theorem:Bacon_Source_Relational_Closed_Identity_Vector.paper_R_closed_identity_vector_transport",
        "theorem:Bacon_Source_Relational_Classicism_A2_Closed_Identity.paper_R_classicism_A2_closed_identity",
    )
    expected_data = {
        "theorem:Bacon_Source_Relational_Classicism_A2_H.paper_R_classicism_A2_H": {"paper_R_named_top"},
        "theorem:Bacon_Source_Relational_Closed_Identity_Vector.paper_R_closed_identity_vector_transport": {"paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst"},
        "theorem:Bacon_Source_Relational_Classicism_A2_Closed_Identity.paper_R_classicism_A2_closed_identity": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst"},
    }
    if (RELATIONAL_A2_BASE_ROOTS != expected
            or RELATIONAL_A2_BASE_C_ROOTS != (expected[0], expected[2])
            or RELATIONAL_A2_TOP_CONSTANTS != {"paper_R_named_top"}
            or RELATIONAL_A2_BASE_DATA_ALLOWLIST != expected_data):
        raise SystemExit("A2 base-case root or literal-top data scope changed")
    models = {"paper_R_bbk_model", "paper_named_bbk_model", "paper_ZF_action_model",
              "pbbk_model", "unknown_model"}
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = relational_a2_base_forbidden(root, models)
        blocked |= (relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                    | relational_witness_class_forbidden(root) | relational_henkin_data_forbidden(root)
                    | relational_closed_henkin_forbidden(root) | relational_term_env_forbidden(root))
        blocked -= (RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CARDINAL_AUX_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_BASE_DATA_ALLOWLIST.get(root, set()))
        if root not in expected:
            if root not in RELATIONAL_H_THEORY_MODEL_ROOTS and "paper_R_named_top" not in blocked:
                raise SystemExit("Older endpoint gained the new literal truth abbreviation")
            continue
        if root in ZF_FOUNDATION_ROOTS:
            raise SystemExit("Native A2 base proof acquired HOL-ZF")
        allowed = {"paper_R_named_H", "paper_R_named_derivable"} | expected_data[root]
        if root in (expected[0], expected[2]):
            allowed.add("paper_R_classicism_proves")
        else:
            blocked.add("paper_R_classicism_proves")
        if not ((ZF_PROOF_PREDICATES - allowed) | models) <= blocked or allowed & blocked:
            raise SystemExit("A2 base case crossed its native proof/data boundary")
        if not {"paper_R_equivalence_proves", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("A2 base case gained Equivalence or F conversion")
        if root == expected[1] and "paper_R_named_top" not in blocked:
            raise SystemExit("Closed identity transport acquired an unused truth abbreviation")


def check_relational_a2_continuation_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_Conversion_Congruence.paper_R_raw_beta_eta_lam_vec",
        "theorem:Bacon_Source_Relational_Classicism_A2_MP.paper_R_classicism_A2_MP",
        "theorem:Bacon_Source_Relational_Classicism_A2_Local.paper_R_classicism_A2_local_H",
        "theorem:Bacon_Source_Relational_Classicism_A2_LE.paper_R_classicism_A2_LE",
        "theorem:Bacon_Source_Relational_Universal_Proof_Basics.paper_R_named_H_all_top",
        "theorem:Bacon_Source_Relational_Forall_Disjunction_Proof.paper_R_named_H_forall_or_distribution",
        "theorem:Bacon_Source_Relational_Naming_Charts.paper_R_naming_chart_exists",
        "theorem:Bacon_Source_Relational_Naming_Charts.paper_R_naming_chart_for_term",
    )
    expected_data = {
        "theorem:Bacon_Source_Relational_Conversion_Congruence.paper_R_raw_beta_eta_lam_vec": set(),
        "theorem:Bacon_Source_Relational_Classicism_A2_MP.paper_R_classicism_A2_MP": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste"},
        "theorem:Bacon_Source_Relational_Classicism_A2_Local.paper_R_classicism_A2_local_H": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste"},
        "theorem:Bacon_Source_Relational_Classicism_A2_LE.paper_R_classicism_A2_LE": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste"},
        "theorem:Bacon_Source_Relational_Universal_Proof_Basics.paper_R_named_H_all_top": {"paper_R_named_top"},
        "theorem:Bacon_Source_Relational_Forall_Disjunction_Proof.paper_R_named_H_forall_or_distribution": set(),
        "theorem:Bacon_Source_Relational_Naming_Charts.paper_R_naming_chart_exists": {"paper_R_naming_chart"},
        "theorem:Bacon_Source_Relational_Naming_Charts.paper_R_naming_chart_for_term": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart"},
    }
    if (RELATIONAL_A2_CONTINUATION_ROOTS != expected
            or RELATIONAL_A2_CONTINUATION_C_ROOTS != expected[1:4]
            or RELATIONAL_A2_CONTINUATION_H_ROOTS != expected[4:6]
            or RELATIONAL_NAMING_DATA_CONSTANTS != {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart"}
            or RELATIONAL_A2_CONTINUATION_DATA_ALLOWLIST != expected_data):
        raise SystemExit("A2 continuation or finite naming policy changed exact scope")
    models = {"paper_R_bbk_model", "paper_named_bbk_model", "paper_ZF_action_model",
              "pbbk_model", "unknown_model"}
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = (relational_a2_continuation_forbidden(root, models)
                   | relational_a2_base_forbidden(root, models)
                   | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                   | relational_witness_class_forbidden(root) | relational_henkin_data_forbidden(root)
                   | relational_closed_henkin_forbidden(root) | relational_term_env_forbidden(root)
                   | relational_rep_count_data_forbidden(root) | relational_recoding_data_forbidden(root))
        blocked -= (RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CARDINAL_AUX_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_BASE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_CONTINUATION_DATA_ALLOWLIST.get(root, set()))
        if root not in expected:
            if not RELATIONAL_NAMING_DATA_CONSTANTS <= blocked:
                raise SystemExit("Older endpoint gained finite naming data")
            if (root not in RELATIONAL_A2_BASE_C_ROOTS and root not in RELATIONAL_H_THEORY_MODEL_ROOTS
                    and "paper_R_named_top" not in blocked):
                raise SystemExit("Older endpoint gained the literal truth abbreviation")
            continue
        if root in ZF_FOUNDATION_ROOTS:
            raise SystemExit("Native A2/naming endpoint acquired HOL-ZF")
        allowed = set(expected_data[root])
        if root in expected[1:6]:
            allowed |= {"paper_R_named_H", "paper_R_named_derivable"}
        if root in expected[1:4]:
            allowed.add("paper_R_classicism_proves")
        if not ((ZF_PROOF_PREDICATES - allowed) | models) <= blocked or allowed & blocked:
            raise SystemExit("A2/naming endpoint crossed its exact proof/data boundary")
        if not {"paper_R_equivalence_proves", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("A2/naming endpoint gained Equivalence or F conversion")
        if root not in expected[1:5] and "paper_R_named_top" not in blocked:
            raise SystemExit("Raw naming/conversion or H distribution acquired unused literal top")
        if root in expected[6:] and not {
                "paper_R_named_H", "paper_R_named_derivable", "paper_R_classicism_proves",
                "paper_R_identity_domain", "paper_R_recode_domain"} <= blocked:
            raise SystemExit("Finite naming acquired theoremhood or semantic domain construction")


def check_relational_a2_complete_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_Gen_Distribution_Proof.paper_R_named_H_Gen_distribution",
        "theorem:Bacon_Source_Relational_Inst_Gen_Certificate.paper_R_named_H_Inst_Gen_equivalence",
        "theorem:Bacon_Source_Relational_Classicism_A2.paper_R_classicism_A2",
        "theorem:Bacon_Source_Relational_Naming_Replacement.paper_R_naming_replace_language",
        "theorem:Bacon_Source_Relational_Naming_Replacement.paper_R_naming_replace_chart_fv",
        "theorem:Bacon_Source_Relational_Naming_Assignments.paper_R_naming_override_typed",
        "theorem:Bacon_Source_Relational_Naming_Assignments.paper_R_naming_override_agrees",
        "theorem:Bacon_Source_Relational_Naming_Assignments.paper_R_naming_override_adequate",
    )
    expected_data = {
        "theorem:Bacon_Source_Relational_Gen_Distribution_Proof.paper_R_named_H_Gen_distribution": set(),
        "theorem:Bacon_Source_Relational_Inst_Gen_Certificate.paper_R_named_H_Inst_Gen_equivalence": set(),
        "theorem:Bacon_Source_Relational_Classicism_A2.paper_R_classicism_A2": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste"},
        "theorem:Bacon_Source_Relational_Naming_Replacement.paper_R_naming_replace_language": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace"},
        "theorem:Bacon_Source_Relational_Naming_Replacement.paper_R_naming_replace_chart_fv": {"paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace"},
        "theorem:Bacon_Source_Relational_Naming_Assignments.paper_R_naming_override_typed": {"paper_R_naming_chart", "paper_R_naming_override"},
        "theorem:Bacon_Source_Relational_Naming_Assignments.paper_R_naming_override_agrees": {"paper_R_naming_chart", "paper_R_naming_override"},
        "theorem:Bacon_Source_Relational_Naming_Assignments.paper_R_naming_override_adequate": {"paper_R_naming_support", "paper_R_naming_replace", "paper_R_naming_override"},
    }
    if (RELATIONAL_A2_COMPLETE_ROOTS != expected
            or RELATIONAL_A2_COMPLETE_C_ROOTS != (expected[2],)
            or RELATIONAL_A2_COMPLETE_H_ROOTS != expected[:2]
            or RELATIONAL_NAMING_REPLACEMENT_CONSTANTS != {"paper_R_naming_replace", "paper_R_naming_override"}
            or RELATIONAL_A2_COMPLETE_DATA_ALLOWLIST != expected_data):
        raise SystemExit("Full A2 or naming replacement policy changed exact scope")
    models = {"paper_R_bbk_model", "paper_named_bbk_model", "paper_ZF_action_model",
              "pbbk_model", "unknown_model"}
    all_naming = RELATIONAL_NAMING_DATA_CONSTANTS | RELATIONAL_NAMING_REPLACEMENT_CONSTANTS
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = (relational_a2_complete_forbidden(root, models)
                   | relational_a2_continuation_forbidden(root, models)
                   | relational_a2_base_forbidden(root, models)
                   | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                   | relational_witness_class_forbidden(root) | relational_henkin_data_forbidden(root)
                   | relational_closed_henkin_forbidden(root) | relational_term_env_forbidden(root)
                   | relational_rep_count_data_forbidden(root) | relational_recoding_data_forbidden(root))
        blocked -= (RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CARDINAL_AUX_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_BASE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_CONTINUATION_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_COMPLETE_DATA_ALLOWLIST.get(root, set()))
        if root not in expected:
            if not RELATIONAL_NAMING_REPLACEMENT_CONSTANTS <= blocked:
                raise SystemExit("Older endpoint gained naming replacement/override data")
            continue
        if root in ZF_FOUNDATION_ROOTS:
            raise SystemExit("Pure A2/naming proof acquired HOL-ZF")
        allowed = set(expected_data[root])
        if root in expected[:3]:
            allowed |= {"paper_R_named_H", "paper_R_named_derivable"}
        if root == expected[2]:
            allowed.add("paper_R_classicism_proves")
        if not ((ZF_PROOF_PREDICATES - allowed) | models | (all_naming - allowed)) <= blocked or allowed & blocked:
            raise SystemExit("Full A2/naming endpoint crossed its exact proof/data boundary")
        if not {"paper_R_equivalence_proves", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("Full A2/naming endpoint gained Equivalence or F conversion")
        if root != expected[2] and "paper_R_named_top" not in blocked:
            raise SystemExit("H certificate or naming acquired unused literal top")
        if root in expected[3:] and not {
                "paper_R_named_H", "paper_R_named_derivable", "paper_R_classicism_proves",
                "paper_R_identity_domain", "paper_R_recode_domain", "paper_R_named_consistent",
                "paper_R_closed_Henkin_theory"} <= blocked:
            raise SystemExit("Raw naming acquired proof or model-construction machinery")


def check_relational_a3_substitution_policy_controls():
    expected_c = (
        "theorem:Bacon_Source_Relational_Classicism_A3.paper_R_classicism_A3",
        "theorem:Bacon_Source_Relational_Classicism_A3.paper_R_classicism_propositional_equivalence",
        "theorem:Bacon_Source_Relational_Classicism_Equivalence_Iff.paper_R_classicism_equivalence_iff",
    )
    expected_model = ("theorem:Bacon_Source_Relational_Substitution_Denotation.paper_R_bbk_model.paper_R_substitution_denote",)
    expected_data = {
        "theorem:Bacon_Source_Relational_Classicism_A3.paper_R_classicism_A3": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste", "paper_R_A3_selector", "paper_R_A3_vector_context"},
        "theorem:Bacon_Source_Relational_Classicism_A3.paper_R_classicism_propositional_equivalence": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste", "paper_R_A3_selector", "paper_R_A3_vector_context"},
        "theorem:Bacon_Source_Relational_Classicism_Equivalence_Iff.paper_R_classicism_equivalence_iff": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste", "paper_R_A3_selector", "paper_R_A3_vector_context"},
    }
    if (RELATIONAL_A3_ROOTS != expected_c
            or RELATIONAL_A3_EQUIVALENCE_ROOTS != (expected_c[2],)
            or RELATIONAL_SUBSTITUTION_MODEL_ROOTS != expected_model
            or RELATIONAL_A3_SELECTOR_CONSTANTS != {"paper_R_A3_selector", "paper_R_A3_vector_context"}
            or RELATIONAL_A3_DATA_ALLOWLIST != expected_data):
        raise SystemExit("A3/semantic-substitution policy changed exact scope")
    models = {"paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_named_bbk_model",
              "paper_ZF_action_model", "pbbk_model", "unknown_model"}
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = (relational_a3_forbidden(root, models)
                   | relational_a2_complete_forbidden(root, models)
                   | relational_a2_continuation_forbidden(root, models)
                   | relational_a2_base_forbidden(root, models)
                   | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                   | relational_witness_class_forbidden(root) | relational_henkin_data_forbidden(root)
                   | relational_closed_henkin_forbidden(root) | relational_term_env_forbidden(root)
                   | relational_rep_count_data_forbidden(root) | relational_recoding_data_forbidden(root))
        blocked -= (RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CARDINAL_AUX_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_BASE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_CONTINUATION_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_COMPLETE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A3_DATA_ALLOWLIST.get(root, set()))
        if root not in expected_c:
            if not RELATIONAL_A3_SELECTOR_CONSTANTS <= blocked:
                raise SystemExit("Older endpoint gained A3 selector data")
        if root in expected_c:
            allowed = {"paper_R_named_H", "paper_R_named_derivable", "paper_R_classicism_proves"} | expected_data[root]
            if root == expected_c[2]:
                allowed.add("paper_R_equivalence_proves")
            if not ((ZF_PROOF_PREDICATES - allowed) | models) <= blocked or allowed & blocked:
                raise SystemExit("A3 or PE acquired an Equivalence/semantic shortcut")
            if root in ZF_FOUNDATION_ROOTS:
                raise SystemExit("Native A3 proof acquired HOL-ZF")
        elif root in expected_model:
            model = {"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
            if not (ZF_PROOF_PREDICATES | (models - model)) <= blocked or model & blocked:
                raise SystemExit("Supplied R-model substitution acquired H/C or a foreign model")
            if not {"paper_R_named_top", "paper_R_identity_domain", "paper_R_identity_denote"} <= blocked:
                raise SystemExit("Semantic substitution gained canonical or A2 construction data")
            if root in ZF_FOUNDATION_ROOTS:
                raise SystemExit("R substitution acquired HOL-ZF")
        if root in expected_c + expected_model and "named_beta_eta_in_language" not in blocked:
            raise SystemExit("Native A3/substitution acquired full-F conversion")


def check_relational_zeta_coordinate_policy_controls():
    expected_zeta = ("theorem:Bacon_Source_Relational_Classicism_Zeta.paper_R_classicism_zeta",)
    expected_chart = ("theorem:Bacon_Source_Relational_Naming_Coordinate_Denotation.paper_R_bbk_model.paper_R_naming_chart_coordinate_denote",)
    expected_data = {
        "theorem:Bacon_Source_Relational_Classicism_Zeta.paper_R_classicism_zeta": {"paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste", "paper_R_A3_selector", "paper_R_A3_vector_context"},
        "theorem:Bacon_Source_Relational_Naming_Coordinate_Denotation.paper_R_bbk_model.paper_R_naming_chart_coordinate_denote": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override"},
    }
    if (RELATIONAL_ZETA_ROOTS != expected_zeta
            or RELATIONAL_NAMING_COORDINATE_MODEL_ROOTS != expected_chart
            or RELATIONAL_ZETA_COORDINATE_DATA_ALLOWLIST != expected_data):
        raise SystemExit("Zeta/one-coordinate chart policy changed exact scope")
    models = {"paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_named_bbk_model",
              "paper_ZF_action_model", "pbbk_model", "unknown_model"}
    naming = RELATIONAL_NAMING_DATA_CONSTANTS | RELATIONAL_NAMING_REPLACEMENT_CONSTANTS
    for root in expected_zeta + expected_chart:
        blocked = (relational_zeta_coordinate_forbidden(root, models)
                   | relational_a3_forbidden(root, models) | relational_a2_complete_forbidden(root, models)
                   | relational_a2_continuation_forbidden(root, models) | relational_a2_base_forbidden(root, models)
                   | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                   | relational_witness_class_forbidden(root) | relational_henkin_data_forbidden(root)
                   | relational_closed_henkin_forbidden(root) | relational_term_env_forbidden(root)
                   | relational_rep_count_data_forbidden(root) | relational_recoding_data_forbidden(root))
        blocked -= RELATIONAL_ZETA_COORDINATE_DATA_ALLOWLIST.get(root, set())
        if root in ZF_FOUNDATION_ROOTS:
            raise SystemExit("Pure zeta/chart endpoint acquired HOL-ZF")
        allowed = set(expected_data[root])
        if root in expected_zeta:
            allowed |= {"paper_R_named_H", "paper_R_named_derivable", "paper_R_classicism_proves"}
            if not ((ZF_PROOF_PREDICATES - allowed) | models | naming) <= blocked or allowed & blocked:
                raise SystemExit("Zeta acquired recursive Equivalence, semantics or naming data")
        else:
            model = {"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
            if not (ZF_PROOF_PREDICATES | (models - model)) <= blocked or (allowed | model) & blocked:
                raise SystemExit("Coordinate chart semantics acquired theoremhood or a foreign model")
            if not RELATIONAL_A3_SELECTOR_CONSTANTS | {"paper_R_named_top"} <= blocked:
                raise SystemExit("Coordinate chart semantics acquired A2/A3 proof data")
        if not {"paper_R_equivalence_proves", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("Zeta/chart endpoint acquired Equivalence or F conversion")


def check_relational_chart_necessitation_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_Naming_Chart_Independence.paper_R_bbk_model.paper_R_naming_chart_denote_independent",
        "theorem:Bacon_Source_Relational_Naming_Larger_Support.paper_R_bbk_model.paper_R_naming_larger_support_denote",
        "theorem:Bacon_Source_Relational_Naming_Larger_Support.paper_R_bbk_model.paper_R_naming_chart_denote_locality",
        "theorem:Bacon_Source_Relational_H_Theory_Necessitation.paper_R_H_theory_necessitation",
        "theorem:Bacon_Source_Relational_Classicism_H_Theory.paper_R_classicism_necessitation",
    )
    expected_constants = {"paper_R_naming_mix", "paper_R_naming_chart_denote", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box"}
    expected_data = {
        "theorem:Bacon_Source_Relational_Naming_Chart_Independence.paper_R_bbk_model.paper_R_naming_chart_denote_independent": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_mix", "paper_R_naming_chart_denote"},
        "theorem:Bacon_Source_Relational_Naming_Larger_Support.paper_R_bbk_model.paper_R_naming_larger_support_denote": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote"},
        "theorem:Bacon_Source_Relational_Naming_Larger_Support.paper_R_bbk_model.paper_R_naming_chart_denote_locality": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote"},
        "theorem:Bacon_Source_Relational_H_Theory_Necessitation.paper_R_H_theory_necessitation": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box"},
        "theorem:Bacon_Source_Relational_Classicism_H_Theory.paper_R_classicism_necessitation": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box", "paper_R_named_top", "paper_R_closed_terms", "paper_R_closed_term_assignment", "paper_R_environment_subst", "paper_R_environment_paste", "paper_R_A3_selector", "paper_R_A3_vector_context"},
    }
    if (RELATIONAL_CHART_NECESSITATION_ROOTS != expected
            or RELATIONAL_CHART_MODEL_ROOTS != expected[:3]
            or RELATIONAL_GENERIC_NECESSITATION_ROOTS != (expected[3],)
            or RELATIONAL_C_NECESSITATION_ROOTS != (expected[4],)
            or RELATIONAL_CHART_NECESSITATION_CONSTANTS != expected_constants
            or RELATIONAL_CHART_NECESSITATION_DATA_ALLOWLIST != expected_data):
        raise SystemExit("Chart/Necessitation proof and definition scope changed")
    models = {"paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_named_bbk_model",
              "paper_ZF_action_model", "pbbk_model", "unknown_model"}
    naming = RELATIONAL_NAMING_DATA_CONSTANTS | RELATIONAL_NAMING_REPLACEMENT_CONSTANTS
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = (relational_chart_necessitation_forbidden(root, models)
                   | relational_zeta_coordinate_forbidden(root, models) | relational_a3_forbidden(root, models)
                   | relational_a2_complete_forbidden(root, models)
                   | relational_a2_continuation_forbidden(root, models) | relational_a2_base_forbidden(root, models)
                   | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                   | relational_witness_class_forbidden(root) | relational_henkin_data_forbidden(root)
                   | relational_closed_henkin_forbidden(root) | relational_term_env_forbidden(root)
                   | relational_rep_count_data_forbidden(root) | relational_recoding_data_forbidden(root))
        blocked -= (RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CARDINAL_AUX_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_BASE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_CONTINUATION_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_COMPLETE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A3_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_ZETA_COORDINATE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CHART_NECESSITATION_DATA_ALLOWLIST.get(root, set()))
        if root not in expected:
            required_old = expected_constants - ({"paper_R_H_theory"} if root in RELATIONAL_H_THEORY_MODEL_ROOTS else set())
            if not required_old <= blocked:
                raise SystemExit("Older endpoint gained chart interpretation or H-theory/box definitions")
            continue
        if root in ZF_FOUNDATION_ROOTS:
            raise SystemExit("Pure chart/Necessitation endpoint acquired HOL-ZF")
        allowed = set(expected_data[root])
        if root in expected[:3]:
            model = {"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
            if not (ZF_PROOF_PREDICATES | (models - model) | (expected_constants - allowed)) <= blocked or (allowed | model) & blocked:
                raise SystemExit("Chart semantics gained H/C/theory/box or a foreign model")
            if not {"paper_R_named_top", "paper_R_A3_selector", "paper_R_identity_domain"} <= blocked:
                raise SystemExit("Chart semantics acquired A2/A3 or canonical construction")
        else:
            allowed.add("paper_R_named_H")
            if root == expected[4]:
                allowed |= {"paper_R_named_derivable", "paper_R_classicism_proves"}
            if not ((ZF_PROOF_PREDICATES - allowed) | models | naming | (expected_constants - allowed)) <= blocked or allowed & blocked:
                raise SystemExit("Necessitation crossed its supplied-theory/native-C boundary")
            if root == expected[3] and not {
                    "paper_R_named_derivable", "paper_R_classicism_proves",
                    "paper_R_named_top", "paper_R_A3_selector", "paper_R_closed_terms"} <= blocked:
                raise SystemExit("Generic Necessitation acquired C/A2 or local proof machinery")
        if not {"paper_R_equivalence_proves", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("Chart/Necessitation acquired recursive Equivalence or F conversion")


def check_relational_chosen_naming_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_Naming_Interpretation.paper_R_bbk_model.paper_R_naming_denote_type",
        "theorem:Bacon_Source_Relational_Naming_Interpretation.paper_R_bbk_model.paper_R_naming_denote_old",
        "theorem:Bacon_Source_Relational_Naming_Interpretation.paper_R_bbk_model.paper_R_naming_denote_value_constant",
    )
    expected_data = {
        "theorem:Bacon_Source_Relational_Naming_Interpretation.paper_R_bbk_model.paper_R_naming_denote_type": {"paper_R_naming_support", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_signature", "paper_R_naming_chart"},
        "theorem:Bacon_Source_Relational_Naming_Interpretation.paper_R_bbk_model.paper_R_naming_denote_old": {"paper_R_naming_support", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote"},
        "theorem:Bacon_Source_Relational_Naming_Interpretation.paper_R_bbk_model.paper_R_naming_denote_value_constant": {"paper_R_naming_support", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_signature", "paper_R_naming_chart"},
    }
    if (RELATIONAL_CHOSEN_NAMING_ROOTS != expected
            or RELATIONAL_CHOSEN_NAMING_CONSTANTS != {"paper_R_naming_chosen_chart", "paper_R_naming_denote"}
            or RELATIONAL_CHOSEN_NAMING_DATA_ALLOWLIST != expected_data):
        raise SystemExit("Chosen naming interpretation policy changed exact scope")
    models = {"paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_named_bbk_model",
              "paper_ZF_action_model", "pbbk_model", "unknown_model"}
    model = {"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
    all_naming = (RELATIONAL_NAMING_DATA_CONSTANTS | RELATIONAL_NAMING_REPLACEMENT_CONSTANTS
                  | RELATIONAL_CHOSEN_NAMING_CONSTANTS | {"paper_R_naming_chart_denote", "paper_R_naming_mix"})
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = (relational_chosen_naming_forbidden(root, models)
                   | relational_chart_necessitation_forbidden(root, models)
                   | relational_zeta_coordinate_forbidden(root, models) | relational_a3_forbidden(root, models)
                   | relational_a2_complete_forbidden(root, models)
                   | relational_a2_continuation_forbidden(root, models) | relational_a2_base_forbidden(root, models)
                   | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                   | relational_witness_class_forbidden(root) | relational_henkin_data_forbidden(root)
                   | relational_closed_henkin_forbidden(root) | relational_term_env_forbidden(root)
                   | relational_rep_count_data_forbidden(root) | relational_recoding_data_forbidden(root))
        blocked -= (RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CARDINAL_AUX_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_BASE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_CONTINUATION_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_COMPLETE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A3_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_ZETA_COORDINATE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CHART_NECESSITATION_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CHOSEN_NAMING_DATA_ALLOWLIST.get(root, set()))
        if root not in expected:
            if not RELATIONAL_CHOSEN_NAMING_CONSTANTS <= blocked:
                raise SystemExit("Older endpoint gained chosen-chart interpretation data")
            continue
        if root in ZF_FOUNDATION_ROOTS:
            raise SystemExit("Chosen naming interpretation acquired HOL-ZF")
        allowed = expected_data[root]
        if not (ZF_PROOF_PREDICATES | (models - model) | (all_naming - allowed)) <= blocked or (allowed | model) & blocked:
            raise SystemExit("Chosen naming crossed its exact supplied-R-model/data boundary")
        if not {"paper_R_named_top", "paper_R_A3_selector", "paper_R_identity_domain",
                "paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("Chosen naming acquired proof/canonical/box/F conversion machinery")
        if root == expected[1] and not {"paper_R_naming_signature", "paper_R_naming_chart"} <= blocked:
            raise SystemExit("Old preservation gained unused chart validity or signature data")


def check_relational_naming_structure_stability_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_Naming_Finite_Family.paper_R_naming_family_chart_exists",
        "theorem:Bacon_Source_Relational_Naming_Structure.paper_R_bbk_model.paper_R_naming_denote_locality",
        "theorem:Bacon_Source_Relational_Naming_Structure.paper_R_bbk_model.paper_R_naming_denote_application_cong",
        "theorem:Bacon_Source_Relational_Identity_Stability.paper_R_H_theory_identity_stability",
    )
    expected_data = {
        "theorem:Bacon_Source_Relational_Naming_Finite_Family.paper_R_naming_family_chart_exists": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_family_support", "paper_R_naming_family_vars"},
        "theorem:Bacon_Source_Relational_Naming_Structure.paper_R_bbk_model.paper_R_naming_denote_locality": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote"},
        "theorem:Bacon_Source_Relational_Naming_Structure.paper_R_bbk_model.paper_R_naming_denote_application_cong": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix", "paper_R_naming_family_support", "paper_R_naming_family_vars"},
        "theorem:Bacon_Source_Relational_Identity_Stability.paper_R_H_theory_identity_stability": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box"},
    }
    if (RELATIONAL_NAMING_STRUCTURE_STABILITY_ROOTS != expected
            or RELATIONAL_NAMING_STRUCTURE_MODEL_ROOTS != expected[1:3]
            or RELATIONAL_IDENTITY_STABILITY_ROOTS != (expected[3],)
            or RELATIONAL_NAMING_FAMILY_CONSTANTS != {"paper_R_naming_family_support", "paper_R_naming_family_vars"}
            or RELATIONAL_NAMING_STRUCTURE_STABILITY_DATA_ALLOWLIST != expected_data):
        raise SystemExit("Finite-family/naming-structure/identity-stability scope changed")
    models = {"paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_named_bbk_model",
              "paper_ZF_action_model", "pbbk_model", "unknown_model"}
    all_data = (RELATIONAL_NAMING_DATA_CONSTANTS | RELATIONAL_NAMING_REPLACEMENT_CONSTANTS
                | RELATIONAL_CHOSEN_NAMING_CONSTANTS | RELATIONAL_CHART_NECESSITATION_CONSTANTS
                | RELATIONAL_NAMING_FAMILY_CONSTANTS)
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = (relational_naming_structure_stability_forbidden(root, models)
                   | relational_chosen_naming_forbidden(root, models) | relational_chart_necessitation_forbidden(root, models)
                   | relational_zeta_coordinate_forbidden(root, models) | relational_a3_forbidden(root, models)
                   | relational_a2_complete_forbidden(root, models)
                   | relational_a2_continuation_forbidden(root, models) | relational_a2_base_forbidden(root, models)
                   | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                   | relational_witness_class_forbidden(root) | relational_henkin_data_forbidden(root)
                   | relational_closed_henkin_forbidden(root) | relational_term_env_forbidden(root)
                   | relational_rep_count_data_forbidden(root) | relational_recoding_data_forbidden(root))
        blocked -= (RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CARDINAL_AUX_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_BASE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_CONTINUATION_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_COMPLETE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A3_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_ZETA_COORDINATE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CHART_NECESSITATION_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CHOSEN_NAMING_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_NAMING_STRUCTURE_STABILITY_DATA_ALLOWLIST.get(root, set()))
        if root not in expected:
            if not RELATIONAL_NAMING_FAMILY_CONSTANTS <= blocked:
                raise SystemExit("Older endpoint gained finite-family data")
            continue
        if root in ZF_FOUNDATION_ROOTS:
            raise SystemExit("Naming structure or identity stability acquired HOL-ZF")
        allowed = set(expected_data[root])
        if root in expected[1:3]:
            model = {"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
            if not (ZF_PROOF_PREDICATES | (models - model) | (all_data - allowed)) <= blocked or (allowed | model) & blocked:
                raise SystemExit("Naming structure acquired H/C, foreign models or unused family data")
        else:
            if root == expected[3]:
                allowed |= {"paper_R_named_H", "paper_R_named_derivable"}
            if not ((ZF_PROOF_PREDICATES - allowed) | models | (all_data - allowed)) <= blocked or allowed & blocked:
                raise SystemExit("Raw family or generic identity stability crossed its proof/model boundary")
        if not {"paper_R_classicism_proves", "paper_R_equivalence_proves", "paper_R_named_top",
                "paper_R_A3_selector", "paper_R_identity_domain", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("Family/structure/stability acquired C/A3, canonical or F conversion machinery")


def check_relational_naming_modal_separation_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_neg_truth",
        "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_conj_truth",
        "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_disj_truth",
        "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_identity_truth",
        "theorem:Bacon_Source_Relational_Naming_Quantifier_Truth.paper_R_bbk_model.paper_R_naming_forall_truth",
        "theorem:Bacon_Source_Relational_Naming_Quantifier_Truth.paper_R_bbk_model.paper_R_naming_exists_truth",
        "theorem:Bacon_Source_Relational_H_Theory_Normal_K.paper_R_H_theory_normal_K",
        "theorem:Bacon_Source_Relational_H_Theory_Modal_PE.paper_R_H_theory_modal_PE",
        "theorem:Bacon_Source_Relational_H_Theory_Boxed_Consequences.paper_R_H_theory_necessitate_local_consequence",
        "theorem:Bacon_Source_Relational_Separating_Consistency.paper_R_bbk_model.paper_R_separating_negation_consistent",
        "theorem:Bacon_Source_Relational_Separating_Consistency.paper_R_bbk_model.paper_R_identity_diagram_separating_consistent",
    )
    expected_data = {
        "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_neg_truth": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix"},
        "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_conj_truth": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix"},
        "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_disj_truth": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix"},
        "theorem:Bacon_Source_Relational_Naming_Boolean_Truth.paper_R_bbk_model.paper_R_naming_identity_truth": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix"},
        "theorem:Bacon_Source_Relational_Naming_Quantifier_Truth.paper_R_bbk_model.paper_R_naming_forall_truth": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix"},
        "theorem:Bacon_Source_Relational_Naming_Quantifier_Truth.paper_R_bbk_model.paper_R_naming_exists_truth": {"paper_R_naming_signature", "paper_R_naming_support", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_override", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_mix"},
        "theorem:Bacon_Source_Relational_H_Theory_Normal_K.paper_R_H_theory_normal_K": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box"},
        "theorem:Bacon_Source_Relational_H_Theory_Modal_PE.paper_R_H_theory_modal_PE": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box"},
        "theorem:Bacon_Source_Relational_H_Theory_Boxed_Consequences.paper_R_H_theory_necessitate_local_consequence": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box", "paper_R_imp_list"},
        "theorem:Bacon_Source_Relational_Separating_Consistency.paper_R_bbk_model.paper_R_separating_negation_consistent": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box", "paper_R_imp_list", "paper_R_named_consistent"},
        "theorem:Bacon_Source_Relational_Separating_Consistency.paper_R_bbk_model.paper_R_identity_diagram_separating_consistent": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box", "paper_R_imp_list", "paper_R_named_consistent"},
    }
    if (RELATIONAL_NAMING_MODAL_SEPARATION_ROOTS != expected
            or RELATIONAL_NAMING_TRUTH_MODEL_ROOTS != expected[:6]
            or RELATIONAL_MODAL_H_THEORY_ROOTS != expected[6:9]
            or RELATIONAL_SEPARATING_MODEL_ROOTS != expected[9:]
            or RELATIONAL_IMPLICATION_LIST_CONSTANTS != {"paper_R_imp_list"}
            or RELATIONAL_NAMING_MODAL_SEPARATION_DATA_ALLOWLIST != expected_data):
        raise SystemExit("Naming/modal/separating-consistency policy changed exact scope")
    models = {"paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_named_bbk_model",
              "paper_ZF_action_model", "pbbk_model", "unknown_model"}
    data_constants = (RELATIONAL_NAMING_DATA_CONSTANTS | RELATIONAL_NAMING_REPLACEMENT_CONSTANTS
                      | RELATIONAL_CHOSEN_NAMING_CONSTANTS | RELATIONAL_CHART_NECESSITATION_CONSTANTS
                      | RELATIONAL_NAMING_FAMILY_CONSTANTS | RELATIONAL_IMPLICATION_LIST_CONSTANTS)
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = (relational_naming_modal_separation_forbidden(root, models)
                   | relational_naming_structure_stability_forbidden(root, models)
                   | relational_chosen_naming_forbidden(root, models) | relational_chart_necessitation_forbidden(root, models)
                   | relational_zeta_coordinate_forbidden(root, models) | relational_a3_forbidden(root, models)
                   | relational_a2_complete_forbidden(root, models)
                   | relational_a2_continuation_forbidden(root, models) | relational_a2_base_forbidden(root, models)
                   | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                   | relational_witness_class_forbidden(root) | relational_henkin_data_forbidden(root)
                   | relational_closed_henkin_forbidden(root) | relational_term_env_forbidden(root)
                   | relational_rep_count_data_forbidden(root) | relational_recoding_data_forbidden(root))
        blocked -= (RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CARDINAL_AUX_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_BASE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_CONTINUATION_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_COMPLETE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A3_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_ZETA_COORDINATE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CHART_NECESSITATION_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CHOSEN_NAMING_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_NAMING_STRUCTURE_STABILITY_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_NAMING_MODAL_SEPARATION_DATA_ALLOWLIST.get(root, set()))
        if root not in expected:
            if "paper_R_imp_list" not in blocked:
                raise SystemExit("Older endpoint gained finite implication-list data")
            continue
        if root in ZF_FOUNDATION_ROOTS:
            raise SystemExit("Native naming/modal/separation acquired HOL-ZF")
        allowed = set(expected_data[root])
        if root in expected[6:]:
            allowed |= {"paper_R_named_H", "paper_R_named_derivable"}
        model = ({"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
                 if root in expected[:6] or root in expected[9:] else set())
        required = (ZF_PROOF_PREDICATES - allowed) | (models - model) | (data_constants - allowed)
        if not required <= blocked or (allowed | model) & blocked:
            raise SystemExit("Naming/modal/separation crossed its exact proof/model/data boundary")
        if root not in expected[9:] and "paper_R_named_consistent" not in blocked:
            raise SystemExit("An earlier naming/modal endpoint gained consistency machinery")
        if not {"paper_R_classicism_proves", "paper_R_equivalence_proves", "paper_R_named_top",
                "paper_R_A3_selector", "paper_R_identity_domain", "paper_R_closed_Henkin_theory",
                "paper_R_closed_maximal_extension", "paper_R_closed_theory",
                "paper_R_H_retraction_support", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("Naming/modal/separation acquired C or canonical/F construction")
        if root in expected[9:] and root in RELATIONAL_MODEL_EXISTENCE_ROOTS:
            raise SystemExit("Conditional separating consistency was classified as model construction")


def check_relational_closure_naming_diagram_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_H_Theory_Universal_Closure.paper_R_H_theory_closed_universal_instance",
        "theorem:Bacon_Source_Relational_H_Theory_Model_Existence.paper_R_H_theory_model_existence",
        "theorem:Bacon_Source_Relational_H_Theory_Bounded_Model.paper_R_H_theory_bounded_model_existence",
        "theorem:Bacon_Source_Relational_Naming_Conversion.paper_R_bbk_model.paper_R_naming_denote_conversion",
        "theorem:Bacon_Source_Relational_Naming_Model.paper_R_bbk_model.paper_R_naming_model",
        "theorem:Bacon_Source_Relational_Positive_Diagram.paper_R_bbk_model.paper_R_positive_diagram_valid",
        "theorem:Bacon_Source_Relational_Positive_Diagram_Consistency.paper_R_bbk_model.paper_R_positive_diagram_separating_consistent",
    )
    expected_data = {
        "theorem:Bacon_Source_Relational_H_Theory_Universal_Closure.paper_R_H_theory_closed_universal_instance": {"paper_R_H_theory", "paper_R_all_vec", "paper_R_named_top"},
        "theorem:Bacon_Source_Relational_Naming_Conversion.paper_R_bbk_model.paper_R_naming_denote_conversion": {"paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support"},
        "theorem:Bacon_Source_Relational_Naming_Model.paper_R_bbk_model.paper_R_naming_model": {"paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support"},
        "theorem:Bacon_Source_Relational_Positive_Diagram.paper_R_bbk_model.paper_R_positive_diagram_valid": {"paper_R_positive_diagram"},
        "theorem:Bacon_Source_Relational_Positive_Diagram_Consistency.paper_R_bbk_model.paper_R_positive_diagram_separating_consistent": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_imp_list", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_positive_diagram"},
    }
    if (RELATIONAL_CLOSURE_NAMING_DIAGRAM_ROOTS != expected
            or RELATIONAL_H_THEORY_MODEL_ROOTS != expected[1:3]
            or RELATIONAL_CLOSURE_DIAGRAM_CONSTANTS != {"paper_R_all_vec", "paper_R_sentence_fragment", "paper_R_positive_diagram"}
            or RELATIONAL_CLOSURE_NAMING_DIAGRAM_DATA_ALLOWLIST != expected_data):
        raise SystemExit("H-theory existence/naming model/positive diagram scope changed")
    extras = {"paper_R_H_theory", "paper_R_named_top", "paper_R_all_vec", "paper_R_sentence_fragment"}
    bases = (
        RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST["theorem:Bacon_Source_Relational_Model_Existence.paper_R_BBK_model_existence"],
        RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST["theorem:Bacon_Source_Relational_Bounded_Model_Existence.paper_R_BBK_bounded_model_existence"],
    )
    for root, base in zip(expected[1:3], bases):
        permitted = RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
        if not base <= permitted or permitted != base | extras:
            raise SystemExit("H-theory model existence lost its native construction or precise closure data")
        if permitted & {"paper_R_PE_closed", "paper_R_positive_diagram", "paper_R_named_box",
                         "paper_R_logical_count_tree", "paper_R_named_count_tree",
                         "paper_R_closed_BBK_consequence", "paper_R_nat_BBK_consequence"}:
            raise SystemExit("H-theory model existence acquired PE/diagram/counting/consequence shortcut")
    models = {"paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_named_bbk_model",
              "paper_ZF_action_model", "pbbk_model", "unknown_model"}
    new_data = RELATIONAL_CLOSURE_DIAGRAM_CONSTANTS
    other_data = (RELATIONAL_NAMING_DATA_CONSTANTS | RELATIONAL_NAMING_REPLACEMENT_CONSTANTS
                  | RELATIONAL_CHOSEN_NAMING_CONSTANTS | RELATIONAL_CHART_NECESSITATION_CONSTANTS
                  | RELATIONAL_NAMING_FAMILY_CONSTANTS | RELATIONAL_IMPLICATION_LIST_CONSTANTS)
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = (relational_closure_naming_diagram_forbidden(root, models)
                   | relational_naming_modal_separation_forbidden(root, models)
                   | relational_naming_structure_stability_forbidden(root, models)
                   | relational_chosen_naming_forbidden(root, models) | relational_chart_necessitation_forbidden(root, models)
                   | relational_zeta_coordinate_forbidden(root, models) | relational_a3_forbidden(root, models)
                   | relational_a2_complete_forbidden(root, models)
                   | relational_a2_continuation_forbidden(root, models) | relational_a2_base_forbidden(root, models)
                   | relational_consistency_forbidden(root) | relational_retraction_proxy_forbidden(root)
                   | relational_witness_class_forbidden(root) | relational_henkin_data_forbidden(root)
                   | relational_closed_henkin_forbidden(root) | relational_term_env_forbidden(root)
                   | relational_rep_count_data_forbidden(root) | relational_recoding_data_forbidden(root)
                   | relational_cardinal_data_forbidden(root) | relational_model_boundary_forbidden(root, models))
        blocked -= (RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CARDINAL_AUX_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_BASE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_CONTINUATION_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A2_COMPLETE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_A3_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_ZETA_COORDINATE_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CHART_NECESSITATION_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CHOSEN_NAMING_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_NAMING_STRUCTURE_STABILITY_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_NAMING_MODAL_SEPARATION_DATA_ALLOWLIST.get(root, set())
                    | RELATIONAL_CLOSURE_NAMING_DIAGRAM_DATA_ALLOWLIST.get(root, set()))
        if root not in expected:
            if not new_data <= blocked:
                raise SystemExit("Older endpoint gained universal closure/fragment/diagram data")
            continue
        if root in ZF_FOUNDATION_ROOTS:
            raise SystemExit("Native open-theory/naming construction acquired HOL-ZF")
        allowed = expected_data.get(root, set()) | RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
        if root == expected[0]:
            allowed |= {"paper_R_named_H"}
        elif root in expected[1:3] or root == expected[6]:
            allowed |= {"paper_R_named_H", "paper_R_named_derivable"}
        # Actual constructors use the independent model predicate in their
        # conclusion. The naming/diagram leaves carry the original locale.
        model = (set() if root == expected[0] else {"paper_R_bbk_model", "paper_R_bbk_model_axioms"})
        if root in expected[1:3]:
            model = {"paper_R_bbk_model"}
        required = (ZF_PROOF_PREDICATES - allowed) | (models - model) | ((new_data | other_data) - allowed)
        if not required <= blocked or (allowed | model) & blocked:
            raise SystemExit("Closure/naming/diagram crossed its exact proof/model/data boundary")
        if not {"paper_R_classicism_proves", "paper_R_equivalence_proves"} <= blocked:
            raise SystemExit("Closure/naming/diagram acquired a C proof")
        if "named_beta_eta_in_language" not in blocked:
            raise SystemExit("Closure/naming/diagram acquired full-F conversion")
        if root in expected[3:6] and not {"paper_R_named_H", "paper_R_named_derivable", "paper_R_named_consistent"} <= blocked:
            raise SystemExit("Naming model or diagram validity acquired theoremhood/consistency")
        if root == expected[6] and not {"paper_R_closed_Henkin_theory", "paper_R_identity_domain", "paper_R_naming_denote"} <= blocked:
            raise SystemExit("Defined-diagram separation acquired an assumed construction")
    probes = {"pHct_Atom", "pHct_type_code", "pHct_future_code", "pHc_domain"}
    if not probes <= relational_cardinal_coding_forbidden(expected[2], probes):
        raise SystemExit("Bounded H-theory construction gained F counting infrastructure")


def check_relational_n73_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_Naming_Validity.paper_R_bbk_model.paper_R_naming_valid_iff",
        "theorem:Bacon_Source_Relational_H_Theory_Closed_Extension_Model.paper_R_H_theory_closed_extension_model",
        "theorem:Bacon_Source_Relational_Diagram_Open_Denotation.paper_R_diagram_target.paper_R_diagram_map_open_denote",
        "theorem:Bacon_Source_Relational_Diagram_Homomorphism.paper_R_diagram_target.paper_R_diagram_reduct_model",
        "theorem:Bacon_Source_Relational_Diagram_Homomorphism.paper_R_diagram_target.paper_R_diagram_reduct_homomorphism",
        "theorem:Bacon_Source_Relational_H_Theory_Substitution.paper_R_H_theory_substitution",
        "theorem:Bacon_Source_Relational_Theoretical_Naming_Independence.paper_R_theoretical_naming_independent",
        "theorem:Bacon_Source_Relational_Parameter_Theory.paper_R_parameter_theory_old_iff",
        "theorem:Bacon_Source_Relational_Parameter_H_Theory.paper_R_H_theory_parameter",
        "theorem:Bacon_Source_Relational_Parameter_Propositional_Closure.paper_R_parameter_theory_PE_closed",
        "theorem:Bacon_Source_Relational_Parameter_Validity.paper_R_bbk_model.paper_R_parameter_theory_valid",
        "theorem:Bacon_Source_Relational_Naming_Signature_Cardinal.paper_R_naming_signature_cardinal_bound",
        "theorem:Bacon_Source_Relational_Positive_Diagram_Separating_Model.paper_R_bbk_model.paper_R_positive_diagram_separating_model",
        "theorem:Bacon_Source_Relational_Naming_Separation.paper_R_bbk_model.paper_R_naming_proposition_separation",
        "theorem:Bacon_Source_Relational_Naming_Bounded_Separation.paper_R_bbk_model.paper_R_naming_bounded_proposition_separation",
    )
    expected_data = {
        "theorem:Bacon_Source_Relational_Naming_Validity.paper_R_bbk_model.paper_R_naming_valid_iff": {"paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support"},
        "theorem:Bacon_Source_Relational_H_Theory_Closed_Extension_Model.paper_R_H_theory_closed_extension_model": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_named_consistent", "paper_R_named_top", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Diagram_Open_Denotation.paper_R_diagram_target.paper_R_diagram_map_open_denote": {"paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_positive_diagram"},
        "theorem:Bacon_Source_Relational_Diagram_Homomorphism.paper_R_diagram_target.paper_R_diagram_reduct_model": {"paper_R_constant_pullback_denote", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_naming_signature"},
        "theorem:Bacon_Source_Relational_Diagram_Homomorphism.paper_R_diagram_target.paper_R_diagram_reduct_homomorphism": {"paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_positive_diagram"},
        "theorem:Bacon_Source_Relational_H_Theory_Substitution.paper_R_H_theory_substitution": {"paper_R_H_theory", "paper_R_named_top"},
        "theorem:Bacon_Source_Relational_Theoretical_Naming_Independence.paper_R_theoretical_naming_independent": {"paper_R_H_theory", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_mix", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support"},
        "theorem:Bacon_Source_Relational_Parameter_Theory.paper_R_parameter_theory_old_iff": {"paper_R_H_theory", "paper_R_naming_chart", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory"},
        "theorem:Bacon_Source_Relational_Parameter_H_Theory.paper_R_H_theory_parameter": {"paper_R_H_theory", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory"},
        "theorem:Bacon_Source_Relational_Parameter_Propositional_Closure.paper_R_parameter_theory_PE_closed": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory"},
        "theorem:Bacon_Source_Relational_Parameter_Validity.paper_R_bbk_model.paper_R_parameter_theory_valid": {"paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory"},
        "theorem:Bacon_Source_Relational_Naming_Signature_Cardinal.paper_R_naming_signature_cardinal_bound": {"paper_R_naming_signature"},
        "theorem:Bacon_Source_Relational_Positive_Diagram_Separating_Model.paper_R_bbk_model.paper_R_positive_diagram_separating_model": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_positive_diagram", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Naming_Separation.paper_R_bbk_model.paper_R_naming_proposition_separation": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_subst", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Naming_Bounded_Separation.paper_R_bbk_model.paper_R_naming_bounded_proposition_separation": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    }
    if (RELATIONAL_N73_ROOTS != expected
            or RELATIONAL_N73_CONSTRUCTION_ROOTS != (expected[1], *expected[12:])
            or RELATIONAL_N73_SEMANTIC_ROOTS != (*expected[:5], expected[10], *expected[12:])
            or RELATIONAL_N73_H_PROOF_ROOTS != expected[5:10]
            or RELATIONAL_N73_HOMOMORPHISM_ROOTS != (expected[4], expected[13], expected[14])
            or RELATIONAL_N73_NAMESPACE_CONSTANTS != {"paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_parameter_theory"}
            or RELATIONAL_N73_DATA_ALLOWLIST != expected_data):
        raise SystemExit("Footnote 73 root/data/model/construction scope changed")
    ordinary = RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST[
        "theorem:Bacon_Source_Relational_H_Theory_Model_Existence.paper_R_H_theory_model_existence"]
    bounded = RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST[
        "theorem:Bacon_Source_Relational_H_Theory_Bounded_Model.paper_R_H_theory_bounded_model_existence"]
    separator = {"paper_R_PE_closed", "paper_R_named_box_const", "paper_R_named_box",
                 "paper_R_imp_list", "paper_R_positive_diagram"}
    naming = {"paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support"}
    diagram = {"paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_diagram_map"}
    final_extra = naming | diagram | {"paper_R_parameter_theory"}
    constructed = {
        expected[1]: ordinary,
        expected[12]: ordinary | separator,
        expected[13]: ordinary | separator | final_extra,
        expected[14]: bounded | separator | final_extra,
    }
    for root, required in constructed.items():
        if RELATIONAL_N73_DATA_ALLOWLIST[root] != required:
            raise SystemExit("Footnote 73 existence lost its exact native construction chain")
        if required & {"paper_R_closed_BBK_consequence", "paper_R_nat_BBK_consequence",
                        "paper_R_logical_count_tree", "paper_R_named_count_tree",
                        "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_named_H"}:
            raise SystemExit("Construction data improperly exempts a predicate or counting/consequence shortcut")
    models = {"paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_named_bbk_model",
              "paper_ZF_action_model", "pbbk_model", "unknown_model", "paper_R_bbk_homomorphism"}
    universe = (RELATIONAL_N73_NAMESPACE_CONSTANTS | RELATIONAL_NAMING_DATA_CONSTANTS
                | RELATIONAL_NAMING_REPLACEMENT_CONSTANTS | RELATIONAL_CHOSEN_NAMING_CONSTANTS
                | RELATIONAL_NAMING_FAMILY_CONSTANTS | RELATIONAL_CHART_NECESSITATION_CONSTANTS
                | RELATIONAL_CLOSURE_DIAGRAM_CONSTANTS | RELATIONAL_IMPLICATION_LIST_CONSTANTS
                | RELATIONAL_CARDINAL_CODE_CONSTANTS)
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        if root not in expected:
            # None of the existing final-data exceptions may erase this
            # global namespace/proxy prohibition.
            prior = set()
            for name, table in tuple(globals().items()):
                if name.endswith("DATA_ALLOWLIST") and isinstance(table, dict):
                    payload = table.get(root, set())
                    if isinstance(payload, set):
                        prior |= payload
            required_namespace = (RELATIONAL_N73_NAMESPACE_CONSTANTS - RELATIONAL_T312_DATA_ALLOWLIST.get(root, set())
                                  - HULL_ACTION_DATA_ALLOWLIST.get(root, set())
                                  - SIGNATURE_TRANSPORT_DATA_ALLOWLIST.get(root, set()))
            if not required_namespace <= relational_n73_forbidden(root, models) - prior:
                raise SystemExit("Older endpoint gained parameter theory or diagram target/map data")
            continue
        blocked = relational_n73_forbidden(root, models)
        for deny in (relational_consistency_forbidden, relational_retraction_proxy_forbidden,
                     relational_witness_class_forbidden, relational_henkin_data_forbidden,
                     relational_closed_henkin_forbidden, relational_term_env_forbidden,
                     relational_rep_count_data_forbidden, relational_recoding_data_forbidden,
                     relational_cardinal_data_forbidden):
            blocked |= deny(root)
        for deny in (relational_a2_base_forbidden, relational_a2_continuation_forbidden,
                     relational_a2_complete_forbidden, relational_a3_forbidden,
                     relational_zeta_coordinate_forbidden, relational_chart_necessitation_forbidden,
                     relational_chosen_naming_forbidden, relational_naming_structure_stability_forbidden,
                     relational_naming_modal_separation_forbidden, relational_closure_naming_diagram_forbidden):
            blocked |= deny(root, models)
        blocked -= RELATIONAL_N73_DATA_ALLOWLIST[root]
        allowed = set(expected_data[root])
        if root in expected[5:10]:
            allowed.add("paper_R_named_H")
        elif root in constructed:
            allowed |= {"paper_R_named_H", "paper_R_named_derivable"}
        model = ({"paper_R_bbk_model", "paper_R_bbk_model_axioms"}
                 if root in (*expected[:5], expected[10], *expected[12:]) else set())
        if root in (expected[4], expected[13], expected[14]):
            model.add("paper_R_bbk_homomorphism")
        required = (ZF_PROOF_PREDICATES - allowed) | (models - model) | (universe - allowed)
        if not required <= blocked or (allowed | model) & blocked:
            raise SystemExit("Footnote 73 endpoint crossed its exact proof/model/data boundary")
        if root in ZF_FOUNDATION_ROOTS:
            raise SystemExit("Native footnote 73 endpoint acquired HOL-ZF")
        if not {"paper_R_classicism_proves", "paper_R_equivalence_proves", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("Footnote 73 endpoint acquired C/Equivalence or F conversion")
        if root not in constructed and "paper_R_named_consistent" not in blocked:
            raise SystemExit("A supplied-target or parameter lemma acquired consistency machinery")
        probes = {"pHct_Atom", "pHct_type_code", "pHct_future_code", "pHc_domain",
                  "paper_R_named_count_tree", "paper_R_logical_count_tree"}
        if not probes <= relational_n73_counting_forbidden(root, probes):
            raise SystemExit("Native n73 construction gained F/countability coding")


def check_relational_t312_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_Normalization_Formula_Validity.paper_R_bbk_normalize_formula_valid_iff",
        "theorem:Bacon_Source_Relational_Normalization_Morphisms.paper_R_bbk_data_morphism_normalize_target",
        "theorem:Bacon_Source_Relational_Bounded_Theory_Models.paper_R_bounded_theory_models_category",
        "theorem:Bacon_Source_Relational_Bounded_Theory_Separation.paper_R_bounded_theory_separating_arrow",
        "theorem:Bacon_Source_Relational_Bounded_Theory_Quasi_Fregean.paper_R_bounded_theory_quasi_fregean",
        "theorem:Bacon_Source_Relational_Box_Truth.paper_R_bbk_model.paper_R_named_box_truth",
        "theorem:Bacon_Source_Relational_Tautology_Profile.paper_R_tautology_profile",
        "theorem:Bacon_Source_Relational_Quasi_Fregean_Box.paper_R_quasi_fregean_box_truth",
        "theorem:Bacon_Source_Relational_Intensionality_Proof.paper_R_classicism_abstraction_intensionality",
        "theorem:Bacon_Source_Relational_Bounded_Theory_Inhabited.paper_R_bounded_theory_models_nonempty",
        "theorem:Bacon_Source_Relational_Bounded_Theory_Countermodel.paper_R_bounded_theory_countermodel",
        "theorem:Bacon_Source_Relational_Bounded_Theory_Common.paper_R_bounded_models_common_theory",
        "theorem:Bacon_Source_Relational_Modalized_Functionality.paper_R_classicism_modalized_functionality",
        "theorem:Bacon_Source_Relational_Quasi_Functional_From_Modal_Functionality.paper_R_quasi_functional_from_modal_functionality",
        "theorem:Bacon_Source_Relational_Classicism_Theory_Minimality.paper_R_classicism_in_H_PE_zeta",
        "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_bounded_classicism_representation",
        "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_classicism_selected_category_iff",
        "theorem:Bacon_Source_Relational_Bounded_PE_Zeta_Category.paper_R_bounded_PE_zeta_category_represents",
        "theorem:Bacon_Source_Relational_Pure_Classicism_Completeness.paper_R_pure_classicism_selected_category_iff",
        "theorem:Bacon_Source_Relational_Arbitrary_Signature_Classicism_Completeness.paper_R_arbitrary_signature_classicism_selected_category_iff",
    )
    expected_data = {
        "theorem:Bacon_Source_Relational_Normalization_Formula_Validity.paper_R_bbk_normalize_formula_valid_iff": set(),
        "theorem:Bacon_Source_Relational_Normalization_Morphisms.paper_R_bbk_data_morphism_normalize_target": set(),
        "theorem:Bacon_Source_Relational_Bounded_Theory_Models.paper_R_bounded_theory_models_category": {"paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models"},
        "theorem:Bacon_Source_Relational_Bounded_Theory_Separation.paper_R_bounded_theory_separating_arrow": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Bounded_Theory_Quasi_Fregean.paper_R_bounded_theory_quasi_fregean": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Box_Truth.paper_R_bbk_model.paper_R_named_box_truth": {"paper_R_named_box", "paper_R_named_box_const"},
        "theorem:Bacon_Source_Relational_Tautology_Profile.paper_R_tautology_profile": set(),
        "theorem:Bacon_Source_Relational_Quasi_Fregean_Box.paper_R_quasi_fregean_box_truth": {"paper_R_named_box", "paper_R_named_box_const"},
        "theorem:Bacon_Source_Relational_Intensionality_Proof.paper_R_classicism_abstraction_intensionality": {"paper_R_H_theory", "paper_R_all_vec", "paper_R_named_box", "paper_R_named_box_const"},
        "theorem:Bacon_Source_Relational_Bounded_Theory_Inhabited.paper_R_bounded_theory_models_nonempty": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_consistent", "paper_R_named_top", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Bounded_Theory_Countermodel.paper_R_bounded_theory_countermodel": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_consistent", "paper_R_named_top", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Bounded_Theory_Common.paper_R_bounded_models_common_theory": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_consistent", "paper_R_named_top", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Modalized_Functionality.paper_R_classicism_modalized_functionality": {"paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_all_vec", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_top"},
        "theorem:Bacon_Source_Relational_Quasi_Functional_From_Modal_Functionality.paper_R_quasi_functional_from_modal_functionality": {"paper_R_named_box", "paper_R_named_box_const"},
        "theorem:Bacon_Source_Relational_Classicism_Theory_Minimality.paper_R_classicism_in_H_PE_zeta": {"paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_top", "paper_R_zeta_closed"},
        "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_bounded_classicism_representation": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_classicism_selected_category_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Bounded_PE_Zeta_Category.paper_R_bounded_PE_zeta_category_represents": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature", "paper_R_zeta_closed"},
        "theorem:Bacon_Source_Relational_Pure_Classicism_Completeness.paper_R_pure_classicism_selected_category_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Arbitrary_Signature_Classicism_Completeness.paper_R_arbitrary_signature_classicism_selected_category_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
    }
    expected_models = {
        "theorem:Bacon_Source_Relational_Normalization_Formula_Validity.paper_R_bbk_normalize_formula_valid_iff": {"paper_R_bbk_data_valid", "paper_R_bbk_model", "paper_R_bbk_model_axioms"},
        "theorem:Bacon_Source_Relational_Normalization_Morphisms.paper_R_bbk_data_morphism_normalize_target": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism"},
        "theorem:Bacon_Source_Relational_Bounded_Theory_Models.paper_R_bounded_theory_models_category": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Bounded_Theory_Separation.paper_R_bounded_theory_separating_arrow": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Bounded_Theory_Quasi_Fregean.paper_R_bounded_theory_quasi_fregean": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Box_Truth.paper_R_bbk_model.paper_R_named_box_truth": {"paper_R_bbk_model", "paper_R_bbk_model_axioms"},
        "theorem:Bacon_Source_Relational_Tautology_Profile.paper_R_tautology_profile": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Quasi_Fregean_Box.paper_R_quasi_fregean_box_truth": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Intensionality_Proof.paper_R_classicism_abstraction_intensionality": set(),
        "theorem:Bacon_Source_Relational_Bounded_Theory_Inhabited.paper_R_bounded_theory_models_nonempty": {"paper_R_bbk_data_valid", "paper_R_bbk_model", "paper_R_bbk_model_axioms"},
        "theorem:Bacon_Source_Relational_Bounded_Theory_Countermodel.paper_R_bounded_theory_countermodel": {"paper_R_bbk_data_valid", "paper_R_bbk_model", "paper_R_bbk_model_axioms"},
        "theorem:Bacon_Source_Relational_Bounded_Theory_Common.paper_R_bounded_models_common_theory": {"paper_R_bbk_data_valid", "paper_R_bbk_model", "paper_R_bbk_model_axioms"},
        "theorem:Bacon_Source_Relational_Modalized_Functionality.paper_R_classicism_modalized_functionality": set(),
        "theorem:Bacon_Source_Relational_Quasi_Functional_From_Modal_Functionality.paper_R_quasi_functional_from_modal_functionality": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Classicism_Theory_Minimality.paper_R_classicism_in_H_PE_zeta": set(),
        "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_bounded_classicism_representation": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_classicism_selected_category_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Bounded_PE_Zeta_Category.paper_R_bounded_PE_zeta_category_represents": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Pure_Classicism_Completeness.paper_R_pure_classicism_selected_category_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Arbitrary_Signature_Classicism_Completeness.paper_R_arbitrary_signature_classicism_selected_category_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
    }
    if (RELATIONAL_T312_ROOTS != expected
            or RELATIONAL_T312_H_ROOTS != tuple(expected[i] for i in [3,4,8,9,10,11,12,14,15,16,17,18,19])
            or RELATIONAL_T312_C_ROOTS != tuple(expected[i] for i in [8,12,14,15,16,17,18,19])
            or RELATIONAL_T312_EQUIVALENCE_ROOTS != tuple(expected[i] for i in [16,18,19])
            or RELATIONAL_T312_NAMESPACE_CONSTANTS != {
                "paper_R_bounded_theory_models", "paper_R_bounded_theory_arrows", "paper_R_zeta_closed"}
            or RELATIONAL_T312_DATA_ALLOWLIST != expected_data
            or RELATIONAL_T312_MODEL_ALLOWLIST != expected_models):
        raise SystemExit("Theorem 3.12 root/proof/model/data policy changed exact scope")
    native = RELATIONAL_N73_DATA_ALLOWLIST[
        "theorem:Bacon_Source_Relational_Naming_Bounded_Separation.paper_R_bbk_model.paper_R_naming_bounded_proposition_separation"]
    existence = RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST[
        "theorem:Bacon_Source_Relational_H_Theory_Bounded_Model.paper_R_H_theory_bounded_model_existence"]
    bound = {"paper_R_bounded_theory_models", "paper_R_bounded_theory_arrows"}
    c_extra = {"paper_R_environment_paste", "paper_R_A3_selector", "paper_R_A3_vector_context"}
    for i in (3, 4):
        if expected_data[expected[i]] != native | bound:
            raise SystemExit("Bounded QF lost its complete separating-arrow construction")
    for i in (9, 10, 11):
        if expected_data[expected[i]] != existence | {"paper_R_bounded_theory_models"}:
            raise SystemExit("Open-theory countermodel/common result lost its native construction")
    for i in (15, 16, 17, 18, 19):
        need = native | bound | c_extra | ({"paper_R_zeta_closed"} if i == 17 else set())
        if expected_data[expected[i]] != need:
            raise SystemExit("Theorem 3.12 assembly lost a prerequisite or gained an unrelated one")
    probes = {"paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_data_valid",
              "paper_R_bbk_data_morphism", "paper_R_bbk_model_morphism", "paper_R_bbk_homomorphism",
              "paper_R_bbk_subcategory", "paper_named_bbk_model", "paper_bbk_data_valid",
              "pbbk_model", "paper_ZF_action_model", "unknown_model"}
    data_universe = (RELATIONAL_N73_NAMESPACE_CONSTANTS | RELATIONAL_NAMING_DATA_CONSTANTS
        | RELATIONAL_NAMING_REPLACEMENT_CONSTANTS | RELATIONAL_CHOSEN_NAMING_CONSTANTS
        | RELATIONAL_NAMING_FAMILY_CONSTANTS | RELATIONAL_CHART_NECESSITATION_CONSTANTS
        | RELATIONAL_CLOSURE_DIAGRAM_CONSTANTS | RELATIONAL_IMPLICATION_LIST_CONSTANTS
        | RELATIONAL_CARDINAL_CODE_CONSTANTS | RELATIONAL_T312_NAMESPACE_CONSTANTS)
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        if root not in expected:
            prior = set()
            for name, table in tuple(globals().items()):
                if name.endswith("DATA_ALLOWLIST") and isinstance(table, dict):
                    payload = table.get(root, set())
                    if isinstance(payload, set):
                        prior |= payload
            required_namespace = RELATIONAL_T312_NAMESPACE_CONSTANTS - HULL_ACTION_DATA_ALLOWLIST.get(root, set()) - SIGNATURE_TRANSPORT_DATA_ALLOWLIST.get(root, set())
            if not required_namespace <= relational_t312_forbidden(root, probes) - prior:
                raise SystemExit("Older endpoint gained bounded category or zeta-closure data")
            continue
        blocked = relational_t312_forbidden(root, probes)
        for deny in (relational_consistency_forbidden, relational_retraction_proxy_forbidden,
                     relational_witness_class_forbidden, relational_henkin_data_forbidden,
                     relational_closed_henkin_forbidden, relational_term_env_forbidden,
                     relational_rep_count_data_forbidden, relational_recoding_data_forbidden,
                     relational_cardinal_data_forbidden):
            blocked |= deny(root)
        for deny in (relational_a2_base_forbidden, relational_a2_continuation_forbidden,
                     relational_a2_complete_forbidden, relational_a3_forbidden,
                     relational_zeta_coordinate_forbidden, relational_chart_necessitation_forbidden,
                     relational_chosen_naming_forbidden, relational_naming_structure_stability_forbidden,
                     relational_naming_modal_separation_forbidden, relational_closure_naming_diagram_forbidden,
                     relational_n73_forbidden):
            blocked |= deny(root, probes)
        blocked -= RELATIONAL_T312_DATA_ALLOWLIST[root]
        allowed = set(expected_data[root])
        if root in RELATIONAL_T312_H_ROOTS:
            allowed |= {"paper_R_named_H", "paper_R_named_derivable"}
        if root in RELATIONAL_T312_C_ROOTS:
            allowed.add("paper_R_classicism_proves")
        if root in RELATIONAL_T312_EQUIVALENCE_ROOTS:
            allowed.add("paper_R_equivalence_proves")
        permitted_models = expected_models[root]
        required = (ZF_PROOF_PREDICATES - allowed) | (probes - permitted_models) | (data_universe - allowed)
        if not required <= blocked or (allowed | permitted_models) & blocked:
            raise SystemExit("Theorem 3.12 endpoint crossed its exact proof/model/data boundary")
        if root in ZF_FOUNDATION_ROOTS or "named_beta_eta_in_language" not in blocked:
            raise SystemExit("Pure Theorem 3.12 endpoint acquired HOL-ZF or F conversion")
        coding = {"pHct_Atom", "pHct_type_code", "pHct_future_code", "pHc_domain",
                  "paper_R_named_count_tree", "paper_R_logical_count_tree"}
        if not coding <= relational_t312_counting_forbidden(root, coding):
            raise SystemExit("Theorem 3.12 acquired imported F/countability coding")
        if root not in RELATIONAL_T312_EQUIVALENCE_ROOTS and "paper_R_equivalence_proves" not in blocked:
            raise SystemExit("Native Intensionality/MF or representation gained recursive Equivalence")
        if root in (expected[5], expected[6], expected[7], expected[13]):
            if not {"paper_R_named_H", "paper_R_named_derivable", "paper_R_classicism_proves",
                    "paper_R_H_theory", "paper_R_PE_closed", "paper_R_named_top"} <= blocked:
                raise SystemExit("Supplied-category modal semantics gained a proof/theory shortcut")


def check_hull_action_pipeline_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_Separating_Hull_Category.paper_R_separating_hull.paper_R_hull_subcategory",
        "theorem:Bacon_Source_Relational_Separating_Hull_Category.paper_R_separating_hull.paper_R_hull_quasi_fregean",
        "theorem:Bacon_Source_Relational_Hull_Cardinal_Stages.paper_R_separating_hull_arrows_cardinal_bound",
        "theorem:Bacon_Source_Relational_Hull_Cardinal_Stages.paper_R_separating_hull_objects_cardinal_bound",
        "theorem:Bacon_Source_Relational_Classical_Separating_Hull.paper_R_classicism_hull.paper_R_classicism_hull_intensional",
        "theorem:Bacon_Source_Relational_Rooted_Separating_Hull.paper_R_classicism_hull.paper_R_classicism_rooted_hull_category",
        "theorem:Bacon_Source_Relational_Classical_Hull_Cardinal.paper_R_classicism_hull.paper_R_classicism_rooted_cardinal_bounds",
        "theorem:Bacon_Source_Relational_Classicism_Counterexample.paper_R_bounded_classicism_counterexample",
        "theorem:Bacon_Source_ZF_Natural_Bounds.paper_ZF_nat_values_infinite",
        "theorem:Bacon_Source_ZF_Natural_Bounds.paper_ZF_cardinal_bounded_encoding",
        "theorem:Bacon_Source_ZF_Hull_Representation.paper_ZF_classicism_hull_action_representation",
        "theorem:Bacon_Source_ZF_Action_Countermodel.paper_ZF_action_countermodel",
        "theorem:Bacon_Source_ZF_Action_Completeness.paper_ZF_classicism_action_iff",
        "theorem:Bacon_Source_ZF_Pure_Action_Completeness.paper_ZF_pure_classicism_action_iff",
        "theorem:Bacon_Source_ZF_Pure_Action_Completeness.paper_ZF_countable_classicism_action_iff",
    )
    expected_data = {
        "theorem:Bacon_Source_Relational_Separating_Hull_Category.paper_R_separating_hull.paper_R_hull_subcategory": {"paper_R_arrow_endpoints", "paper_R_chosen_separator", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices"},
        "theorem:Bacon_Source_Relational_Separating_Hull_Category.paper_R_separating_hull.paper_R_hull_quasi_fregean": {"paper_R_arrow_endpoints", "paper_R_chosen_separator", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices"},
        "theorem:Bacon_Source_Relational_Hull_Cardinal_Stages.paper_R_separating_hull_arrows_cardinal_bound": {"paper_R_arrow_endpoints", "paper_R_chosen_separator", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices"},
        "theorem:Bacon_Source_Relational_Hull_Cardinal_Stages.paper_R_separating_hull_objects_cardinal_bound": {"paper_R_arrow_endpoints", "paper_R_chosen_separator", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices"},
        "theorem:Bacon_Source_Relational_Classical_Separating_Hull.paper_R_classicism_hull.paper_R_classicism_hull_intensional": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Rooted_Separating_Hull.paper_R_classicism_hull.paper_R_classicism_rooted_hull_category": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Classical_Hull_Cardinal.paper_R_classicism_hull.paper_R_classicism_rooted_cardinal_bounds": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_Relational_Classicism_Counterexample.paper_R_bounded_classicism_counterexample": {"ROriginal", "RWitness", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_add_constant", "paper_R_all_vec", "paper_R_bounded_theory_models", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_consistent", "paper_R_named_top", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_ZF_Natural_Bounds.paper_ZF_nat_values_infinite": set(),
        "theorem:Bacon_Source_ZF_Natural_Bounds.paper_ZF_cardinal_bounded_encoding": set(),
        "theorem:Bacon_Source_ZF_Hull_Representation.paper_ZF_classicism_hull_action_representation": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_ZF_Action_Countermodel.paper_ZF_action_countermodel": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature"},
        "theorem:Bacon_Source_ZF_Action_Completeness.paper_ZF_classicism_action_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature", "paper_ZF_record_action_valid"},
        "theorem:Bacon_Source_ZF_Pure_Action_Completeness.paper_ZF_pure_classicism_action_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature", "paper_ZF_record_action_valid"},
        "theorem:Bacon_Source_ZF_Pure_Action_Completeness.paper_ZF_countable_classicism_action_iff": {"ROriginal", "RWitness", "paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_retraction_support", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_add_constant", "paper_R_all_vec", "paper_R_arrow_endpoints", "paper_R_bounded_theory_arrows", "paper_R_bounded_theory_models", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_closed_Henkin_theory", "paper_R_closed_constant_witness_complete", "paper_R_closed_maximal_extension", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_closed_theory", "paper_R_constant_pullback_denote", "paper_R_diagram_map", "paper_R_diagram_target", "paper_R_diagram_target_axioms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_finite_syntax_code", "paper_R_henkin_full_premises", "paper_R_henkin_full_signature", "paper_R_henkin_premises", "paper_R_henkin_signature", "paper_R_henkin_stage_axioms", "paper_R_henkin_stage_indices", "paper_R_henkin_stage_name", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_identity_application", "paper_R_identity_class", "paper_R_identity_denote", "paper_R_identity_domain", "paper_R_identity_relation", "paper_R_identity_rep", "paper_R_identity_valuation", "paper_R_imp_list", "paper_R_local_retraction_support", "paper_R_logical_nat_code", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_consistent", "paper_R_named_top", "paper_R_naming_chart", "paper_R_naming_chart_denote", "paper_R_naming_chosen_chart", "paper_R_naming_denote", "paper_R_naming_family_support", "paper_R_naming_family_vars", "paper_R_naming_mix", "paper_R_naming_override", "paper_R_naming_replace", "paper_R_naming_signature", "paper_R_naming_support", "paper_R_parameter_theory", "paper_R_positive_diagram", "paper_R_recode_assignment", "paper_R_recode_denote", "paper_R_recode_domain", "paper_R_recode_inverse", "paper_R_recode_valuation", "paper_R_representative_assignment", "paper_R_sentence", "paper_R_sentence_fragment", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_R_term_type", "paper_R_type_nat_code", "paper_R_witness_axiom", "paper_R_witness_family_axioms", "paper_R_witness_family_signature", "paper_ZF_record_action_valid"},
    }
    expected_models = {
        "theorem:Bacon_Source_Relational_Separating_Hull_Category.paper_R_separating_hull.paper_R_hull_subcategory": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Separating_Hull_Category.paper_R_separating_hull.paper_R_hull_quasi_fregean": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Hull_Cardinal_Stages.paper_R_separating_hull_arrows_cardinal_bound": set(),
        "theorem:Bacon_Source_Relational_Hull_Cardinal_Stages.paper_R_separating_hull_objects_cardinal_bound": set(),
        "theorem:Bacon_Source_Relational_Classical_Separating_Hull.paper_R_classicism_hull.paper_R_classicism_hull_intensional": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Rooted_Separating_Hull.paper_R_classicism_hull.paper_R_classicism_rooted_hull_category": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Classical_Hull_Cardinal.paper_R_classicism_hull.paper_R_classicism_rooted_cardinal_bounds": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory"},
        "theorem:Bacon_Source_Relational_Classicism_Counterexample.paper_R_bounded_classicism_counterexample": {"paper_R_bbk_data_valid", "paper_R_bbk_model", "paper_R_bbk_model_axioms"},
        "theorem:Bacon_Source_ZF_Natural_Bounds.paper_ZF_nat_values_infinite": set(),
        "theorem:Bacon_Source_ZF_Natural_Bounds.paper_ZF_cardinal_bounded_encoding": set(),
        "theorem:Bacon_Source_ZF_Hull_Representation.paper_ZF_classicism_hull_action_representation": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory", "paper_ZF_action_model", "paper_ZF_action_premodel"},
        "theorem:Bacon_Source_ZF_Action_Countermodel.paper_ZF_action_countermodel": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory", "paper_ZF_action_model", "paper_ZF_action_premodel"},
        "theorem:Bacon_Source_ZF_Action_Completeness.paper_ZF_classicism_action_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory", "paper_ZF_action_model", "paper_ZF_action_premodel"},
        "theorem:Bacon_Source_ZF_Pure_Action_Completeness.paper_ZF_pure_classicism_action_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory", "paper_ZF_action_model", "paper_ZF_action_premodel"},
        "theorem:Bacon_Source_ZF_Pure_Action_Completeness.paper_ZF_countable_classicism_action_iff": {"paper_R_bbk_data_morphism", "paper_R_bbk_data_valid", "paper_R_bbk_homomorphism", "paper_R_bbk_model", "paper_R_bbk_model_axioms", "paper_R_bbk_model_morphism", "paper_R_bbk_subcategory", "paper_ZF_action_model", "paper_ZF_action_premodel"},
    }
    if (HULL_ACTION_PIPELINE_ROOTS != expected or PURE_HULL_ROOTS != expected[:8]
            or ZF_HULL_ROOTS != expected[8:] or ZF_HULL_CONSTRUCTION_ROOTS != expected[10:]
            or HULL_NATIVE_C_ROOTS != (*expected[4:8], *expected[10:])
            or HULL_ACTION_NAMESPACE_CONSTANTS != {"paper_R_arrow_endpoints", "paper_R_chosen_separator", "paper_R_classicism_hull", "paper_R_hull_composable_pairs", "paper_R_hull_composites", "paper_R_separating_hull", "paper_R_separating_hull_arrows", "paper_R_separating_hull_objects", "paper_R_separating_stage_arrows", "paper_R_separating_stage_objects", "paper_R_separator_choices", "paper_R_separator_indices", "paper_ZF_record_action_valid"}
            or HULL_ACTION_DATA_ALLOWLIST != expected_data or HULL_ACTION_MODEL_ALLOWLIST != expected_models):
        raise SystemExit("Hull/action-completeness root/data/model scope changed")
    if not set(ZF_HULL_ROOTS) <= set(ZF_FOUNDATION_ROOTS) or set(PURE_HULL_ROOTS) & set(ZF_FOUNDATION_ROOTS):
        raise SystemExit("Pure hull and relative HOL-ZF foundations crossed")
    classical = RELATIONAL_T312_DATA_ALLOWLIST[
        "theorem:Bacon_Source_Relational_Bounded_Classicism_Completeness.paper_R_bounded_classicism_representation"]
    complete = classical | expected_data[expected[2]] | {"paper_R_separating_hull", "paper_R_classicism_hull"}
    for i in (4, 5, 6, 10, 11, 12, 13, 14):
        need = complete | ({"paper_ZF_record_action_valid"} if i >= 12 else set())
        if HULL_ACTION_DATA_ALLOWLIST[expected[i]] != need:
            raise SystemExit("Hull/action construction lost its exact native proof chain")
    probes = set(ZF_INDEPENDENT_R_MODEL_PREDICATES) | {
        "paper_named_bbk_model", "pbbk_model", "unknown_model", "paper_ZF_action_model", "paper_ZF_action_premodel"}
    universe = (HULL_ACTION_NAMESPACE_CONSTANTS | RELATIONAL_T312_NAMESPACE_CONSTANTS
        | RELATIONAL_N73_NAMESPACE_CONSTANTS | RELATIONAL_NAMING_DATA_CONSTANTS
        | RELATIONAL_NAMING_REPLACEMENT_CONSTANTS | RELATIONAL_CHOSEN_NAMING_CONSTANTS
        | RELATIONAL_NAMING_FAMILY_CONSTANTS | RELATIONAL_CHART_NECESSITATION_CONSTANTS
        | RELATIONAL_CLOSURE_DIAGRAM_CONSTANTS | RELATIONAL_IMPLICATION_LIST_CONSTANTS
        | RELATIONAL_CARDINAL_CODE_CONSTANTS)
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        if root not in expected:
            prior = set()
            for name, table in tuple(globals().items()):
                if name.endswith("DATA_ALLOWLIST") and isinstance(table, dict):
                    payload = table.get(root, set())
                    if isinstance(payload, set):
                        prior |= payload
            if not (HULL_ACTION_NAMESPACE_CONSTANTS - SIGNATURE_TRANSPORT_DATA_ALLOWLIST.get(root, set())) <= hull_action_pipeline_forbidden(root, probes) - prior:
                raise SystemExit("Older endpoint gained hull generation or universal action validity")
            continue
        blocked = hull_action_pipeline_forbidden(root, probes) | zf_action_stage_forbidden(root)
        for deny in (relational_consistency_forbidden, relational_retraction_proxy_forbidden,
                     relational_witness_class_forbidden, relational_henkin_data_forbidden,
                     relational_closed_henkin_forbidden, relational_term_env_forbidden,
                     relational_rep_count_data_forbidden, relational_recoding_data_forbidden,
                     relational_cardinal_data_forbidden):
            blocked |= deny(root)
        for deny in (relational_a2_base_forbidden, relational_a2_continuation_forbidden,
                     relational_a2_complete_forbidden, relational_a3_forbidden,
                     relational_zeta_coordinate_forbidden, relational_chart_necessitation_forbidden,
                     relational_chosen_naming_forbidden, relational_naming_structure_stability_forbidden,
                     relational_naming_modal_separation_forbidden, relational_closure_naming_diagram_forbidden,
                     relational_n73_forbidden, relational_t312_forbidden, zf_representation_forbidden):
            blocked |= deny(root, probes)
        blocked -= HULL_ACTION_DATA_ALLOWLIST[root]
        allowed = set(expected_data[root])
        if root in HULL_NATIVE_C_ROOTS:
            allowed |= {"paper_R_named_H", "paper_R_named_derivable", "paper_R_classicism_proves"}
        model = expected_models[root]
        required = (ZF_PROOF_PREDICATES - allowed) | (probes - model) | (universe - allowed)
        if not required <= blocked or (allowed | model) & blocked:
            raise SystemExit("Hull/action endpoint crossed its exact proof/model/data boundary")
        if not {"paper_R_equivalence_proves", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("Hull/action construction acquired Equivalence or F conversion")
        if root not in expected[10:] and not {"paper_ZF_action_model", "paper_ZF_action_premodel"} <= blocked:
            raise SystemExit("Generic hull/cardinal/Nat root acquired an action-model premise")
        if root not in expected[12:] and "paper_ZF_record_action_valid" not in blocked:
            raise SystemExit("A construction/root-truth lemma acquired universal action validity")
        if not ZF_ACTION_STAGE_PREDICATES - {"paper_ZF_action_model", "paper_ZF_action_premodel"} <= blocked:
            raise SystemExit("Action construction acquired an unrelated interpretation/totality predicate")
        coding = {"pHct_Atom", "pHct_type_code", "pHct_future_code", "pHc_domain",
                  "paper_R_named_count_tree", "paper_R_logical_count_tree"}
        if not coding <= hull_action_counting_forbidden(root, coding):
            raise SystemExit("Hull/action proof acquired imported F/countability coding")


def check_signature_transport_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_Typed_Constant_Map.paper_R_typed_constant_map_language",
        "theorem:Bacon_Source_Relational_Typed_Constant_Map_Conversion.paper_R_typed_constant_map_raw_conversion",
        "theorem:Bacon_Source_Relational_H_Typed_Constant_Map.paper_R_named_H_typed_constant_map",
        "theorem:Bacon_Source_Relational_Classicism_Typed_Constant_Map.paper_R_classicism_typed_constant_map",
        "theorem:Bacon_Source_Relational_Signature_Compression_Section.paper_R_compression_formula_roundtrip",
        "theorem:Bacon_Source_Relational_Signature_Compression_Proof.paper_R_finite_formula_compression",
        "theorem:Bacon_Source_ZF_Action_Constant_Pullback.paper_ZF_action_eval_typed_constants",
        "theorem:Bacon_Source_ZF_Action_Constant_Pullback.paper_ZF_action_model_typed_constant_pullback",
        "theorem:Bacon_Source_ZF_Action_Validity_On.paper_ZF_record_action_valid_as_valid_on",
        "theorem:Bacon_Source_ZF_Arbitrary_Signature_Action_Countermodel.paper_ZF_arbitrary_signature_action_countermodel",
        "theorem:Bacon_Source_ZF_Arbitrary_Signature_Action_Completeness.paper_ZF_arbitrary_signature_action_iff",
    )
    if SIGNATURE_ACTION_TRANSPORT_ROOTS != expected:
        raise SystemExit("Signature transport root scope changed")
    namespace = {"paper_R_typed_constant_map", "paper_R_compress_name", "paper_R_compressed_signature", "paper_R_compression_section", "paper_ZF_action_valid_on"}
    if SIGNATURE_TRANSPORT_NAMESPACE_CONSTANTS != namespace:
        raise SystemExit("Signature transport namespace changed")
    construction = HULL_ACTION_DATA_ALLOWLIST[
        "theorem:Bacon_Source_ZF_Action_Countermodel.paper_ZF_action_countermodel"]
    expected_data = {r: {"paper_R_typed_constant_map"} for r in expected}
    expected_data[expected[4]] = {"paper_R_typed_constant_map", "paper_R_compress_name", "paper_R_compression_section"}
    expected_data[expected[5]] = namespace - {"paper_ZF_action_valid_on"}
    expected_data[expected[8]] = {"paper_ZF_record_action_valid", "paper_ZF_action_valid_on"}
    expected_data[expected[9]] = construction | (namespace - {"paper_ZF_action_valid_on"})
    expected_data[expected[10]] = construction | namespace
    expected_models = {r: set() for r in expected}
    for i in (7, 8):
        expected_models[expected[i]] = {"paper_ZF_action_model", "paper_ZF_action_premodel"}
    for i in (9, 10):
        expected_models[expected[i]] = set(ZF_INDEPENDENT_R_MODEL_PREDICATES) | {"paper_ZF_action_model", "paper_ZF_action_premodel"}
    expected_proofs = {r: set() for r in expected}
    expected_proofs[expected[2]] = {"paper_R_named_H"}
    for i in (3, 5):
        expected_proofs[expected[i]] = {"paper_R_named_H", "paper_R_classicism_proves"}
    for i in (9, 10):
        expected_proofs[expected[i]] = {"paper_R_named_H", "paper_R_named_derivable", "paper_R_classicism_proves"}
    if (SIGNATURE_TRANSPORT_DATA_ALLOWLIST != expected_data
            or SIGNATURE_TRANSPORT_MODEL_ALLOWLIST != expected_models
            or SIGNATURE_TRANSPORT_PROOF_ALLOWLIST != expected_proofs
            or PURE_SIGNATURE_TRANSPORT_ROOTS != expected[:6]
            or ZF_SIGNATURE_TRANSPORT_ROOTS != expected[6:]
            or SIGNATURE_TRANSPORT_C_ROOTS != (expected[3], expected[5], *expected[9:])):
        raise SystemExit("Signature transport exact permissions changed")
    if (not set(expected[6:]) <= set(ZF_FOUNDATION_ROOTS)
            or set(expected[:6]) & set(ZF_FOUNDATION_ROOTS)):
        raise SystemExit("Signature transport crossed the pure/HOL-ZF boundary")
    if (len(construction) != 83 or not {"ROriginal", "paper_R_closed_Henkin_theory",
            "paper_R_identity_domain", "paper_R_separating_hull"} <= construction):
        raise SystemExit("Arbitrary-signature construction lost its native construction base")
    probes = set(ZF_INDEPENDENT_R_MODEL_PREDICATES) | {
        "paper_named_bbk_model", "unknown_model", "paper_ZF_action_model", "paper_ZF_action_premodel"}
    all_data = namespace | construction | {"paper_ZF_record_action_valid",
        "paper_R_closed_BBK_consequence", "paper_R_nat_BBK_consequence"}
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = signature_transport_forbidden(root, probes)
        if root not in expected:
            if not namespace <= blocked:
                raise SystemExit("Older root gained typed compression or generic world validity")
            continue
        for deny in (relational_consistency_forbidden, relational_retraction_proxy_forbidden,
                     relational_witness_class_forbidden, relational_henkin_data_forbidden,
                     relational_closed_henkin_forbidden, relational_term_env_forbidden,
                     relational_rep_count_data_forbidden, relational_recoding_data_forbidden,
                     relational_cardinal_data_forbidden):
            blocked |= deny(root)
        for deny in (relational_a2_base_forbidden, relational_a2_continuation_forbidden,
                     relational_a2_complete_forbidden, relational_a3_forbidden,
                     relational_zeta_coordinate_forbidden, relational_chart_necessitation_forbidden,
                     relational_chosen_naming_forbidden, relational_naming_structure_stability_forbidden,
                     relational_naming_modal_separation_forbidden, relational_closure_naming_diagram_forbidden,
                     relational_n73_forbidden, relational_t312_forbidden, hull_action_pipeline_forbidden,
                     zf_representation_forbidden):
            blocked |= deny(root, probes)
        blocked |= zf_action_stage_forbidden(root) | {
            "paper_R_closed_BBK_consequence", "paper_R_nat_BBK_consequence"}
        blocked -= SIGNATURE_TRANSPORT_DATA_ALLOWLIST[root]
        allowed = expected_data[root] | expected_proofs[root] | expected_models[root]
        required = (ZF_PROOF_PREDICATES | probes | all_data) - allowed
        if not required <= blocked or allowed & blocked:
            raise SystemExit(f"Signature transport proof/model/data boundary failed: {root}")
        if not {"paper_R_equivalence_proves", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("Signature transport acquired foreign conversion or Equivalence")
        if not {"pHct_probe", "pHc_probe", "paper_R_named_count_tree"} <= signature_transport_counting_forbidden(root, {"pHct_probe", "pHc_probe"}):
            raise SystemExit("Signature transport acquired legacy F counting")


def check_figure3_modal_policy_controls():
    expected = (
        "theorem:Bacon_Source_Relational_Figure3_Syntax.paper_R_figure3_axiom_closed",
        "theorem:Bacon_Source_Relational_Figure3_Language.paper_R_figure3_axiom_language",
        "theorem:Bacon_Source_Relational_Figure3_Certificates.paper_R_classicism_figure3_member",
        "theorem:Bacon_Source_Relational_Modal_T.paper_R_named_H_modal_T",
        "theorem:Bacon_Source_Relational_Modal_Four.paper_R_classicism_modal_4",
    )
    namespace = {"RCommAnd", "RCommOr", "RDissolveAndOr", "RDissolveOrAnd", "RDistAndOr", "RDistOrAnd", "paper_R_figure3_axiom", "paper_R_figure3_axioms", "paper_R_figure3_bodies", "paper_R_figure3_laws", "paper_R_figure3_prefix", "paper_R_figure3_template", "paper_R_figure3_variables"}
    expected_data = {
        "theorem:Bacon_Source_Relational_Figure3_Syntax.paper_R_figure3_axiom_closed": {"RCommAnd", "RCommOr", "RDissolveAndOr", "RDissolveOrAnd", "RDistAndOr", "RDistOrAnd", "paper_R_figure3_axiom", "paper_R_figure3_bodies", "paper_R_figure3_prefix"},
        "theorem:Bacon_Source_Relational_Figure3_Language.paper_R_figure3_axiom_language": {"RCommAnd", "RCommOr", "RDissolveAndOr", "RDissolveOrAnd", "RDistAndOr", "RDistOrAnd", "paper_R_figure3_axiom", "paper_R_figure3_bodies", "paper_R_figure3_prefix", "paper_R_figure3_variables"},
        "theorem:Bacon_Source_Relational_Figure3_Certificates.paper_R_classicism_figure3_member": {"RCommAnd", "RCommOr", "RDissolveAndOr", "RDissolveOrAnd", "RDistAndOr", "RDistOrAnd", "paper_R_figure3_axiom", "paper_R_figure3_axioms", "paper_R_figure3_bodies", "paper_R_figure3_laws", "paper_R_figure3_prefix", "paper_R_figure3_template", "paper_R_figure3_variables"},
        "theorem:Bacon_Source_Relational_Modal_T.paper_R_named_H_modal_T": {"paper_R_named_box", "paper_R_named_box_const"},
        "theorem:Bacon_Source_Relational_Modal_Four.paper_R_classicism_modal_4": {"paper_R_A3_selector", "paper_R_A3_vector_context", "paper_R_H_theory", "paper_R_PE_closed", "paper_R_closed_term_assignment", "paper_R_closed_terms", "paper_R_environment_paste", "paper_R_environment_subst", "paper_R_named_box", "paper_R_named_box_const", "paper_R_named_top"},
    }
    expected_proofs = {
        "theorem:Bacon_Source_Relational_Figure3_Syntax.paper_R_figure3_axiom_closed": set(),
        "theorem:Bacon_Source_Relational_Figure3_Language.paper_R_figure3_axiom_language": set(),
        "theorem:Bacon_Source_Relational_Figure3_Certificates.paper_R_classicism_figure3_member": {"paper_R_classicism_proves", "paper_R_named_H"},
        "theorem:Bacon_Source_Relational_Modal_T.paper_R_named_H_modal_T": {"paper_R_named_H", "paper_R_named_derivable"},
        "theorem:Bacon_Source_Relational_Modal_Four.paper_R_classicism_modal_4": {"paper_R_classicism_proves", "paper_R_named_H", "paper_R_named_derivable"},
    }
    if (FIGURE3_MODAL_ROOTS != expected or FIGURE3_NAMESPACE_CONSTANTS != namespace
            or FIGURE3_MODAL_DATA_ALLOWLIST != expected_data
            or FIGURE3_MODAL_PROOF_ALLOWLIST != expected_proofs
            or FIGURE3_MODAL_C_ROOTS != (expected[2], expected[4])):
        raise SystemExit("Figure 3/modal exact root permissions changed")
    if set(expected) & set(ZF_FOUNDATION_ROOTS):
        raise SystemExit("Figure 3/modal pure roots acquired HOL-ZF")
    probes = set(ZF_INDEPENDENT_R_MODEL_PREDICATES) | {
        "paper_named_bbk_model", "unknown_model", "paper_ZF_action_model", "paper_ZF_action_premodel"}
    extra_data = set().union(*expected_data.values()) | {
        "paper_R_named_consistent", "paper_R_closed_Henkin_theory", "paper_R_identity_domain",
        "paper_R_typed_constant_map", "paper_ZF_action_valid_on"}
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = figure3_modal_forbidden(root, probes)
        if root not in expected:
            if not namespace <= blocked:
                raise SystemExit("Older root gained literal Figure 3 syntax/certificates")
            continue
        for deny in (relational_consistency_forbidden, relational_retraction_proxy_forbidden,
                     relational_witness_class_forbidden, relational_henkin_data_forbidden,
                     relational_closed_henkin_forbidden, relational_term_env_forbidden,
                     relational_rep_count_data_forbidden, relational_recoding_data_forbidden,
                     relational_cardinal_data_forbidden):
            blocked |= deny(root)
        for deny in (relational_a2_base_forbidden, relational_a2_continuation_forbidden,
                     relational_a2_complete_forbidden, relational_a3_forbidden,
                     relational_zeta_coordinate_forbidden, relational_chart_necessitation_forbidden,
                     relational_chosen_naming_forbidden, relational_naming_structure_stability_forbidden,
                     relational_naming_modal_separation_forbidden, relational_closure_naming_diagram_forbidden,
                     relational_n73_forbidden, relational_t312_forbidden, hull_action_pipeline_forbidden,
                     signature_transport_forbidden):
            blocked |= deny(root, probes)
        blocked |= zf_action_stage_forbidden(root)
        blocked -= FIGURE3_MODAL_DATA_ALLOWLIST[root]
        allowed = expected_data[root] | expected_proofs[root]
        required = (ZF_PROOF_PREDICATES | probes | extra_data) - allowed
        if not required <= blocked or allowed & blocked:
            raise SystemExit(f"Figure 3/modal proof/data/model boundary failed: {root}")
        if not {"paper_R_equivalence_proves", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("Figure 3/modal root acquired reverse presentation or F conversion")


def check_book_modal_structure_policy_controls():
    expected = (
        "theorem:Bacon_Book_Preorder_Powerset.book_preorder.book_preorder_powerset_action",
        "theorem:Bacon_Book_Preorder_Powerset.book_preorder_powerset_bijection",
        "theorem:Bacon_Book_Preorder_Powerset.book_preorder_powerset_transport_correspondence",
        "theorem:Bacon_Book_Modal_Implication_Typing.book_printed_implication_future_iff",
        "theorem:Bacon_Book_Modal_Implication_Typing.book_printed_implication_two_world_failure",
        "theorem:Bacon_Book_Modal_Implication_Naturality.book_preorder.book_future_implication_naturality",
        "theorem:Bacon_Book_Modal_Implication_Typing.book_printed_implication_restriction",
        "theorem:Bacon_Book_Modalized_Set.book_preorder.book_modalized_set_iff_action",
        "theorem:Bacon_Book_Modalized_Map.book_modalized_map_iff_action_map",
    )
    namespace = {"book_future_implication_set", "book_modalized_map", "book_modalized_set", "book_modalized_set_axioms", "book_pointed_preorder", "book_pointed_preorder_axioms", "book_preorder", "book_preorder_arrows", "book_preorder_compose", "book_preorder_future", "book_preorder_identity", "book_preorder_powerset", "book_preorder_powerset_decode", "book_preorder_powerset_encode", "book_preorder_powerset_transport", "book_preorder_truncate", "book_printed_implication_set"}
    expected_data = {
        "theorem:Bacon_Book_Preorder_Powerset.book_preorder.book_preorder_powerset_action": {"book_preorder", "book_preorder_arrows", "book_preorder_compose", "book_preorder_future", "book_preorder_identity", "book_preorder_powerset", "book_preorder_powerset_transport", "book_preorder_truncate"},
        "theorem:Bacon_Book_Preorder_Powerset.book_preorder_powerset_bijection": {"book_preorder_arrows", "book_preorder_future", "book_preorder_powerset", "book_preorder_powerset_decode", "book_preorder_powerset_encode"},
        "theorem:Bacon_Book_Preorder_Powerset.book_preorder_powerset_transport_correspondence": {"book_preorder_arrows", "book_preorder_compose", "book_preorder_future", "book_preorder_powerset", "book_preorder_powerset_encode", "book_preorder_powerset_transport", "book_preorder_truncate"},
        "theorem:Bacon_Book_Modal_Implication_Typing.book_printed_implication_future_iff": {"book_preorder_future", "book_preorder_powerset", "book_printed_implication_set"},
        "theorem:Bacon_Book_Modal_Implication_Typing.book_printed_implication_two_world_failure": {"book_pointed_preorder", "book_pointed_preorder_axioms", "book_preorder", "book_preorder_future", "book_preorder_powerset", "book_printed_implication_set"},
        "theorem:Bacon_Book_Modal_Implication_Naturality.book_preorder.book_future_implication_naturality": {"book_future_implication_set", "book_preorder", "book_preorder_future", "book_preorder_powerset", "book_preorder_truncate"},
        "theorem:Bacon_Book_Modal_Implication_Typing.book_printed_implication_restriction": {"book_future_implication_set", "book_printed_implication_set"},
        "theorem:Bacon_Book_Modalized_Set.book_preorder.book_modalized_set_iff_action": {"book_modalized_set", "book_modalized_set_axioms", "book_preorder", "book_preorder_arrows", "book_preorder_compose", "book_preorder_identity"},
        "theorem:Bacon_Book_Modalized_Map.book_modalized_map_iff_action_map": {"book_modalized_map", "book_preorder_arrows"},
    }
    if (BOOK_MODAL_STRUCTURE_ROOTS != expected
            or BOOK_MODAL_STRUCTURE_CONSTANTS != namespace
            or BOOK_MODAL_STRUCTURE_DATA_ALLOWLIST != expected_data):
        raise SystemExit("Book modal structure exact root/namespace permissions changed")
    if set(expected) & set(ZF_FOUNDATION_ROOTS):
        raise SystemExit("Book modal structure acquired HOL-ZF")
    if any({"book_modalized_set", "book_modalized_set_axioms", "book_modalized_map"} & expected_data[r]
           for r in expected[:7]):
        raise SystemExit("Raw preorder/implication endpoints acquired modalized-family premises")
    probes = set(ZF_INDEPENDENT_R_MODEL_PREDICATES) | {
        "paper_named_bbk_model", "book_full_minimal_model", "book_modal_model",
        "unknown_model", "paper_ZF_action_model", "paper_ZF_action_premodel"}
    syntax_and_construction = namespace | {
        "paper_R_named_consistent", "paper_R_closed_Henkin_theory", "paper_R_identity_domain",
        "paper_R_typed_constant_map", "paper_ZF_action_valid_on", "paper_R_figure3_axiom",
        "paper_R_named_top", "paper_R_named_box", "paper_R_named_box_const"}
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = book_modal_structure_forbidden(root, probes)
        if root not in expected:
            if not namespace <= blocked:
                raise SystemExit("Older endpoint gained book preorder/modalized-family infrastructure")
            continue
        for deny in (relational_consistency_forbidden, relational_retraction_proxy_forbidden,
                     relational_witness_class_forbidden, relational_henkin_data_forbidden,
                     relational_closed_henkin_forbidden, relational_term_env_forbidden,
                     relational_rep_count_data_forbidden, relational_recoding_data_forbidden,
                     relational_cardinal_data_forbidden):
            blocked |= deny(root)
        for deny in (relational_a2_base_forbidden, relational_a2_continuation_forbidden,
                     relational_a2_complete_forbidden, relational_a3_forbidden,
                     relational_zeta_coordinate_forbidden, relational_chart_necessitation_forbidden,
                     relational_chosen_naming_forbidden, relational_naming_structure_stability_forbidden,
                     relational_naming_modal_separation_forbidden, relational_closure_naming_diagram_forbidden,
                     relational_n73_forbidden, relational_t312_forbidden, hull_action_pipeline_forbidden,
                     signature_transport_forbidden, figure3_modal_forbidden):
            blocked |= deny(root, probes)
        blocked |= zf_action_stage_forbidden(root)
        blocked -= BOOK_MODAL_STRUCTURE_DATA_ALLOWLIST[root]
        allowed = expected_data[root]
        required = (ZF_PROOF_PREDICATES | probes | syntax_and_construction) - allowed
        if not required <= blocked or allowed & blocked:
            raise SystemExit(f"Book modal structure crossed proof/model/data boundary: {root}")
        if not {"paper_R_equivalence_proves", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("Book modal structure acquired an alternative calculus/conversion")


def check_book_exponential_policy_controls():
    expected = (
        "theorem:Bacon_Book_Modalized_Exponential_Homomorphisms.book_preorder.book_modalized_exponential_iff_future_map",
        "theorem:Bacon_Book_Modalized_Exponential_Codec.book_modalized_exponential_bijection",
        "theorem:Bacon_Book_Modalized_Exponential_Transport.book_modalized_exponential_transport_correspondence",
        "theorem:Bacon_Book_Modalized_Exponential_Transport.book_modalized_exponential_is_modalized_set",
        "theorem:Bacon_Book_Modalized_Exponential_Nonextension.book_ex17_4_transport_not_surjective",
        "theorem:Bacon_Book_Modalized_Evaluation.book_modalized_evaluation_source",
        "theorem:Bacon_Book_Modalized_Evaluation.book_modalized_evaluation_map",
    )
    namespace = {"book_ex17_4_counterpart", "book_ex17_4_domain", "book_ex17_4_future_map", "book_ex17_4_le", "book_modalized_evaluate", "book_modalized_exponential", "book_modalized_exponential_decode", "book_modalized_exponential_encode", "book_modalized_exponential_pairs", "book_modalized_exponential_transport"}
    expected_data = {
        "theorem:Bacon_Book_Modalized_Exponential_Homomorphisms.book_preorder.book_modalized_exponential_iff_future_map": {"book_modalized_exponential", "book_modalized_exponential_pairs", "book_modalized_map", "book_preorder", "book_preorder_future"},
        "theorem:Bacon_Book_Modalized_Exponential_Codec.book_modalized_exponential_bijection": {"book_modalized_exponential", "book_modalized_exponential_decode", "book_modalized_exponential_encode", "book_modalized_exponential_pairs", "book_preorder_arrows", "book_preorder_compose"},
        "theorem:Bacon_Book_Modalized_Exponential_Transport.book_modalized_exponential_transport_correspondence": {"book_modalized_exponential_encode", "book_modalized_exponential_pairs", "book_modalized_exponential_transport", "book_preorder_arrows", "book_preorder_compose"},
        "theorem:Bacon_Book_Modalized_Exponential_Transport.book_modalized_exponential_is_modalized_set": {"book_modalized_exponential", "book_modalized_exponential_decode", "book_modalized_exponential_encode", "book_modalized_exponential_pairs", "book_modalized_exponential_transport", "book_modalized_set", "book_modalized_set_axioms", "book_preorder", "book_preorder_arrows", "book_preorder_compose", "book_preorder_identity"},
        "theorem:Bacon_Book_Modalized_Exponential_Nonextension.book_ex17_4_transport_not_surjective": {"book_ex17_4_counterpart", "book_ex17_4_domain", "book_ex17_4_future_map", "book_ex17_4_le", "book_modalized_exponential", "book_modalized_exponential_pairs", "book_modalized_exponential_transport"},
        "theorem:Bacon_Book_Modalized_Evaluation.book_modalized_evaluation_source": {"book_modalized_exponential", "book_modalized_exponential_decode", "book_modalized_exponential_encode", "book_modalized_exponential_pairs", "book_modalized_exponential_transport", "book_modalized_set", "book_modalized_set_axioms", "book_preorder", "book_preorder_arrows", "book_preorder_compose", "book_preorder_identity"},
        "theorem:Bacon_Book_Modalized_Evaluation.book_modalized_evaluation_map": {"book_modalized_evaluate", "book_modalized_exponential", "book_modalized_exponential_pairs", "book_modalized_exponential_transport", "book_modalized_map", "book_modalized_set", "book_modalized_set_axioms", "book_preorder"},
    }
    if (BOOK_EXPONENTIAL_ROOTS != expected or BOOK_EXPONENTIAL_CONSTANTS != namespace
            or BOOK_EXPONENTIAL_DATA_ALLOWLIST != expected_data):
        raise SystemExit("Book exponential exact root/namespace permissions changed")
    if set(expected) & set(ZF_FOUNDATION_ROOTS):
        raise SystemExit("Book exponential pure roots acquired HOL-ZF")
    for i in (0, 1, 2, 4):
        if {"book_modalized_set", "book_modalized_set_axioms"} & expected_data[expected[i]]:
            raise SystemExit("Raw exponential endpoint acquired modalized-set assumptions")
    probes = set(ZF_INDEPENDENT_R_MODEL_PREDICATES) | {
        "paper_named_bbk_model", "book_full_minimal_model", "book_modal_model",
        "unknown_model", "paper_ZF_action_model", "paper_ZF_action_premodel"}
    all_data = namespace | BOOK_MODAL_STRUCTURE_CONSTANTS | {
        "paper_R_named_consistent", "paper_R_closed_Henkin_theory", "paper_R_identity_domain",
        "paper_R_typed_constant_map", "paper_ZF_action_valid_on", "paper_R_figure3_axiom",
        "paper_R_named_top", "paper_R_named_box"}
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        blocked = book_exponential_forbidden(root, probes)
        if root not in expected:
            if not namespace <= blocked:
                raise SystemExit("Older endpoint gained future exponential or nonextension data")
            continue
        for deny in (relational_consistency_forbidden, relational_retraction_proxy_forbidden,
                     relational_witness_class_forbidden, relational_henkin_data_forbidden,
                     relational_closed_henkin_forbidden, relational_term_env_forbidden,
                     relational_rep_count_data_forbidden, relational_recoding_data_forbidden,
                     relational_cardinal_data_forbidden):
            blocked |= deny(root)
        for deny in (relational_a2_base_forbidden, relational_a2_continuation_forbidden,
                     relational_a2_complete_forbidden, relational_a3_forbidden,
                     relational_zeta_coordinate_forbidden, relational_chart_necessitation_forbidden,
                     relational_chosen_naming_forbidden, relational_naming_structure_stability_forbidden,
                     relational_naming_modal_separation_forbidden, relational_closure_naming_diagram_forbidden,
                     relational_n73_forbidden, relational_t312_forbidden, hull_action_pipeline_forbidden,
                     signature_transport_forbidden, figure3_modal_forbidden, book_modal_structure_forbidden):
            blocked |= deny(root, probes)
        blocked |= zf_action_stage_forbidden(root)
        blocked -= BOOK_EXPONENTIAL_DATA_ALLOWLIST[root]
        allowed = expected_data[root]
        if not ((ZF_PROOF_PREDICATES | probes | all_data) - allowed) <= blocked or allowed & blocked:
            raise SystemExit(f"Book exponential proof/model/namespace boundary failed: {root}")
        if not {"paper_R_equivalence_proves", "named_beta_eta_in_language"} <= blocked:
            raise SystemExit("Book exponential acquired a foreign proof/conversion shortcut")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("graph", type=Path)
    args = parser.parse_args()
    check_zf_action_policy_controls()
    check_relational_consistency_policy_controls()
    check_relational_retraction_policy_controls()
    check_relational_witness_class_policy_controls()
    check_relational_constant_map_policy_controls()
    check_relational_henkin_stage_policy_controls()
    check_relational_closed_henkin_policy_controls()
    check_relational_term_env_policy_controls()
    check_relational_model_boundary_policy_controls()
    check_relational_model_existence_policy_controls()
    check_relational_representative_counting_policy_controls()
    check_relational_recoding_policy_controls()
    check_relational_cardinal_c_preparation_policy_controls()
    check_relational_a2_base_policy_controls()
    check_relational_a2_continuation_policy_controls()
    check_relational_a2_complete_policy_controls()
    check_relational_a3_substitution_policy_controls()
    check_relational_zeta_coordinate_policy_controls()
    check_relational_chart_necessitation_policy_controls()
    check_relational_chosen_naming_policy_controls()
    check_relational_naming_structure_stability_policy_controls()
    check_relational_naming_modal_separation_policy_controls()
    check_relational_closure_naming_diagram_policy_controls()
    check_relational_n73_policy_controls()
    check_relational_t312_policy_controls()
    check_hull_action_pipeline_policy_controls()
    check_signature_transport_policy_controls()
    check_figure3_modal_policy_controls()
    check_book_modal_structure_policy_controls()
    check_book_exponential_policy_controls()
    graph = json.loads(args.graph.read_text(encoding="utf-8"))
    nodes = {node["id"]: node for node in graph["nodes"]}
    model_predicates = {
        node.get("name", node_id).rsplit(".", 1)[-1]
        for node_id, node in nodes.items()
        if node_id.startswith("constant:")
        and node.get("name", node_id).rsplit(".", 1)[-1].endswith(("_model", "_model_axioms"))
    }
    all_constant_names = {
        node.get("name", node_id).rsplit(".", 1)[-1]
        for node_id, node in nodes.items() if node_id.startswith("constant:")
    }
    dependencies = defaultdict(set)
    constants = defaultdict(set)
    for edge in graph["edges"]:
        if edge["kind"] == "DEPENDS_ON":
            dependencies[edge["source"]].add(edge["target"])
        elif edge["kind"] == "USES_CONSTANT":
            constants[edge["source"]].add(edge["target"])

    reports = []
    for root in ROOTS + H_ONLY_ROOTS + SOURCE_PROOF_ROOTS:
        forbidden = FORBIDDEN
        if (root not in RELATIONAL_C_PROOF_ROOTS and root not in CLASSICISM_SEMANTIC_R_C_SOUNDNESS_ROOTS
                and root not in CLASSICISM_SEMANTIC_R_DIRECT_C_ROOTS
                and root not in RELATIONAL_C_PREPARATION_C_ROOTS
                and root not in RELATIONAL_A2_BASE_C_ROOTS
                and root not in RELATIONAL_A2_CONTINUATION_C_ROOTS
                and root not in RELATIONAL_A2_COMPLETE_C_ROOTS
                and root not in RELATIONAL_A3_ROOTS
                and root not in RELATIONAL_ZETA_ROOTS
                and root not in RELATIONAL_C_NECESSITATION_ROOTS
                and root not in RELATIONAL_T312_C_ROOTS
                and root not in HULL_NATIVE_C_ROOTS
                and root not in SIGNATURE_TRANSPORT_C_ROOTS
                and root not in FIGURE3_MODAL_C_ROOTS
                and root not in ZF_NATIVE_R_C_MODEL_ROOTS):
            forbidden = forbidden | {"paper_R_equivalence_proves", "paper_R_classicism_proves"}
        if root in H_ONLY_ROOTS or root in SOURCE_PROOF_ROOTS:
            forbidden = forbidden | {"C_proves", "HE_proves"}
        if root in SOURCE_PROOF_ROOTS:
            forbidden = forbidden | {"HLE_proves"}
        forbidden = forbidden | relational_consistency_forbidden(root)
        forbidden = forbidden | relational_retraction_proxy_forbidden(root)
        forbidden = forbidden | relational_witness_class_forbidden(root)
        forbidden = forbidden | relational_henkin_data_forbidden(root)
        forbidden = forbidden | relational_closed_henkin_forbidden(root)
        forbidden = forbidden | relational_term_env_forbidden(root)
        forbidden = forbidden | relational_rep_count_data_forbidden(root)
        forbidden = forbidden | relational_recoding_data_forbidden(root)
        forbidden = forbidden | relational_cardinal_data_forbidden(root)
        forbidden = forbidden | relational_cardinal_coding_forbidden(root, all_constant_names)
        forbidden = forbidden | relational_c_preparation_forbidden(root, model_predicates)
        forbidden = forbidden | relational_a2_base_forbidden(root, model_predicates)
        forbidden = forbidden | relational_a2_continuation_forbidden(root, model_predicates)
        forbidden = forbidden | relational_a2_complete_forbidden(root, model_predicates)
        forbidden = forbidden | relational_a3_forbidden(root, model_predicates)
        forbidden = forbidden | relational_zeta_coordinate_forbidden(root, model_predicates)
        forbidden = forbidden | relational_chart_necessitation_forbidden(root, model_predicates)
        forbidden = forbidden | relational_chosen_naming_forbidden(root, model_predicates)
        forbidden = forbidden | relational_naming_structure_stability_forbidden(root, model_predicates)
        forbidden = forbidden | relational_naming_modal_separation_forbidden(root, model_predicates)
        forbidden = forbidden | relational_closure_naming_diagram_forbidden(root, model_predicates)
        forbidden = forbidden | relational_n73_forbidden(root, model_predicates)
        forbidden = forbidden | relational_t312_forbidden(root, model_predicates)
        forbidden = forbidden | hull_action_pipeline_forbidden(root, model_predicates)
        forbidden = forbidden | signature_transport_forbidden(root, model_predicates)
        forbidden = forbidden | figure3_modal_forbidden(root, model_predicates)
        forbidden = forbidden | book_modal_structure_forbidden(root, model_predicates)
        forbidden = forbidden | book_exponential_forbidden(root, model_predicates)
        forbidden = forbidden | signature_transport_counting_forbidden(root, all_constant_names)
        forbidden = forbidden | hull_action_counting_forbidden(root, all_constant_names)
        forbidden = forbidden | relational_t312_counting_forbidden(root, all_constant_names)
        forbidden = forbidden | relational_n73_counting_forbidden(root, all_constant_names)
        forbidden = forbidden | relational_counting_coding_forbidden(root, all_constant_names)
        forbidden = forbidden | relational_model_boundary_forbidden(root, model_predicates)
        forbidden = forbidden | book_conversion_forbidden(root)
        forbidden = forbidden | book_conjunction_forbidden(root, model_predicates)
        forbidden = forbidden | classicism_semantic_forbidden(root, model_predicates)
        forbidden = forbidden | zf_representation_forbidden(root, model_predicates)
        forbidden = forbidden | zf_action_stage_forbidden(root)
        if root in BOOK_PRINTED_INDEPENDENT_ROOTS:
            forbidden = forbidden | BOOK_PRINTED_INDEPENDENT_FORBIDDEN
        if root.endswith(("paper_db_bbk_structure.paper_db_rename_derived",
                          "paper_db_bbk_structure.paper_db_imp_truth")):
            forbidden = forbidden | {"pbbk_model", "paper_db_bbk_model", "paper_db_bbk_model_axioms"}
        if root in NAMED_SYNTAX_ROOTS:
            forbidden = forbidden | {"H_proves", "pH_proves", "paper_global_H",
                "paper_global_derivable", "pbbk_model", "paper_db_bbk_structure",
                "paper_db_bbk_model", "paper_db_bbk_model_axioms", "paper_named_bbk_model"}
        if root in NAMED_MODEL_ROOTS:
            forbidden = forbidden | {"H_proves", "pH_proves", "paper_global_H",
                "paper_global_derivable", "pbbk_model", "paper_db_bbk_structure",
                "paper_db_bbk_model", "paper_db_bbk_model_axioms"}
        if root in NAMED_REVERSE_MODEL_ROOTS:
            # The weak structure occurs in the constructed conclusion.
            # Its absence as an added premise is checked in the source audit;
            # here exclude proof-calculus and stronger-model dependencies.
            forbidden = forbidden | {"H_proves", "pH_proves", "paper_global_H",
                "paper_global_derivable", "pbbk_model", "paper_db_bbk_model",
                "paper_db_bbk_model_axioms"}
        if root in NAMED_PROOF_ROOTS:
            forbidden = forbidden | {"H_proves", "pH_proves", "pbbk_model",
                "paper_db_bbk_structure", "paper_db_bbk_model",
                "paper_db_bbk_model_axioms", "paper_named_bbk_model"}
        if root in NATIVE_H_ROOTS:
            forbidden = forbidden | {"H_proves", "pH_proves", "paper_global_H",
                "paper_global_derivable", "pbbk_model", "paper_db_bbk_structure",
                "paper_db_bbk_model", "paper_db_bbk_model_axioms", "paper_named_bbk_model"}
        if root.endswith("Bacon_Source_Named_Consistent_Negation.paper_named_consistent_insert_not"):
            forbidden = forbidden | {"pbbk_model", "paper_db_bbk_structure",
                "paper_db_bbk_model", "paper_db_bbk_model_axioms", "paper_named_bbk_model"}
        if root in BOOK_ENV_ROOTS or root in BOOK_THEORY_ROOTS or root in BOOK_BBK_SYNTAX_ROOTS or root in BOOK_HENKIN_SYNTAX_ROOTS:
            forbidden = forbidden | {"H_proves", "pH_proves", "paper_global_H",
                "paper_global_derivable", "paper_named_H", "paper_named_derivable",
                "pbbk_model", "bbk_model", "paper_db_bbk_structure", "paper_db_bbk_model",
                "paper_db_bbk_model_axioms", "paper_named_bbk_model", "bacon_general_model"}
        if root in BOOK_ENV_ROOTS:
            forbidden = forbidden | {"book_theory_derivable", "book_higher_order_theory"}
        if root in BOOK_THEORY_PURE_ROOTS or root in BOOK_BBK_SYNTAX_ROOTS or root in BOOK_HENKIN_SYNTAX_ROOTS:
            forbidden = forbidden | {"book_full_minimal_model", "book_full_environment",
                "book_environment_conditions", "book_formula_valid", "book_env_typed"}
        if root in BOOK_HENKIN_SYNTAX_ROOTS:
            forbidden = forbidden | {"book_theory_derivable", "book_higher_order_theory",
                "book_H", "book_higher_order_logic", "book_theory_consistent",
                "book_prop_certificate", "book_closed_maximal_extension",
                "book_closed_constant_witness_complete"}
        if root in BOOK_BBK_CONSTRUCTION_ROOTS:
            forbidden = forbidden | {"H_proves", "pH_proves", "paper_global_H",
                "paper_global_derivable", "paper_named_H", "paper_named_derivable",
                "book_theory_derivable", "bacon_general_model"}
        if root in BOOK_INHABITATION_ROOTS:
            # The independent seed legitimately uses the earlier H consistency
            # proof; it must not use a stronger Classicism judgment.
            forbidden = forbidden | {"bacon_general_model"}
        if root.endswith(("book_leibniz_valuation_from_negation",
                          "book_implication_false_point_witnesses",
                          "book_leibniz_valuation_from_implication")):
            forbidden = forbidden | {"book_full_environment", "book_environment_conditions",
                "book_interpretation_structure", "book_env_typed"}
        # Exact complete-construction roots may use their enumerated native
        # data. No older proof/semantic endpoint inherits this allowance.
        forbidden = (forbidden | {"paper_R_closed_BBK_consequence", "paper_R_nat_BBK_consequence"}) - RELATIONAL_MODEL_EXISTENCE_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_CARDINAL_AUX_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_A2_BASE_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_A2_CONTINUATION_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_A2_COMPLETE_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_A3_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_ZETA_COORDINATE_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_CHART_NECESSITATION_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_CHOSEN_NAMING_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_NAMING_STRUCTURE_STABILITY_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_NAMING_MODAL_SEPARATION_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_CLOSURE_NAMING_DIAGRAM_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_N73_DATA_ALLOWLIST.get(root, set())
        forbidden -= RELATIONAL_T312_DATA_ALLOWLIST.get(root, set())
        forbidden -= HULL_ACTION_DATA_ALLOWLIST.get(root, set())
        forbidden -= SIGNATURE_TRANSPORT_DATA_ALLOWLIST.get(root, set())
        forbidden -= FIGURE3_MODAL_DATA_ALLOWLIST.get(root, set())
        forbidden -= BOOK_MODAL_STRUCTURE_DATA_ALLOWLIST.get(root, set())
        forbidden -= BOOK_EXPONENTIAL_DATA_ALLOWLIST.get(root, set())
        if root not in nodes or not dependencies[root]:
            raise SystemExit(f"Missing root or exported proof dependencies: {root}")
        reached = set()
        pending = [root]
        while pending:
            current = pending.pop()
            if current in reached:
                continue
            reached.add(current)
            pending.extend(dependencies[current] - reached)

        violations = []
        referenced_nodes = reached | set().union(*(constants[t] for t in reached))
        foundation_references = sorted(
            node_id for node_id in referenced_nodes
            if node_id.split(":", 1)[-1].startswith(("HOLZF.", "Zet.", "MainZF."))
            or nodes.get(node_id, {}).get("name", "").startswith(("HOLZF.", "Zet.", "MainZF."))
        )
        if root not in ZF_FOUNDATION_ROOTS and foundation_references:
            raise SystemExit(f"Pure-HOL certificate reaches HOL-ZF foundation: {root}: {foundation_references[:5]}")
        if root.endswith(".paper_ZF_function_graph_bijection") and not foundation_references:
            raise SystemExit("Foundation positive control failed: function graph bijection lost its HOL-ZF references")
        for theorem in sorted(reached):
            for constant in constants[theorem]:
                name = nodes.get(constant, {}).get("name", constant)
                if name.rsplit(".", 1)[-1] in forbidden:
                    violations.append({"theorem": theorem, "constant": constant})
        external_project = sorted(
            node_id for node_id in reached
            if nodes.get(node_id, {}).get("external")
            and node_id.startswith("theorem:Bacon_")
        )
        reports.append({
            "root": root,
            "forbidden_judgments": sorted(forbidden),
            "reachable_theorem_nodes": len(reached),
            "forbidden_judgment_uses": violations,
            "external_project_theorems": external_project,
            "foundation": "standard HOL-ZF" if root in ZF_FOUNDATION_ROOTS else "pure HOL",
            "zf_dependency_tier": (
                "source-R-action-model-construction" if root in ZF_MODEL_CONCLUSION_ALLOWLIST
                else "source-R-premodel-construction" if root in ZF_PREMODEL_CONCLUSION_ALLOWLIST
                else "source-R-derived-premodel-use" if root in ZF_R_DERIVED_PREMODEL_ROOTS
                else "action-model-to-R-BBK-construction" if root in ZF_ACTION_TO_R_MODEL_ROOTS
                else "native-R-H-via-derived-BBK" if root in ZF_NATIVE_R_H_MODEL_ROOTS
                else "native-R-C-via-derived-BBK" if root in ZF_NATIVE_R_C_MODEL_ROOTS
                else "generic-action-model-deduction" if root in ZF_ACTION_MODEL_DEDUCTION_ROOTS
                else "generic-premodel-regression" if root in ZF_PREMODEL_REGRESSION_ROOTS
                else "generic-premodel-deduction" if root in ZF_PREMODEL_DEDUCTION_ROOTS
                else "source-R-model-aware" if root in ZF_SOURCE_R_MODEL_ROOTS
                else "generic-representation" if root in ZF_REPRESENTATION_ROOTS else None
            ),
            "set_theoretic_foundation_references": foundation_references,
        })
    print(json.dumps({"graph": str(args.graph), "checks": reports}, indent=2))
    if any(report["forbidden_judgment_uses"] for report in reports):
        raise SystemExit("A proof certificate reaches a forbidden calculus or semantic predicate")
    if any(report["external_project_theorems"] for report in reports):
        raise SystemExit("Project dependency bodies missing; separation check is incomplete")
    print("C-PROOF-DEPENDENCIES-CLEAN: no reachable CE/CEV judgment uses")
    print("H-CERTIFICATES-CLEAN: no reachable C/CE/CEV/HE judgment uses")
    print("SOURCE-H-CORRESPONDENCE-CLEAN: no reachable Classicism judgment uses")
    print("BOOK-CONVERSION-DEPENDENCIES-CLEAN: syntax, structure, and valuation exclusions passed")
    print("BOOK-PRINTED-INDEPENDENCE-CLEAN: strict proofs exclude old conversion, calculi, and models")
    print("BOOK-CONJUNCTION-DEPENDENCIES-CLEAN: syntax, native rules, fixed-background proofs, and semantic layers separated")
    print("CLASSICISM-SEMANTIC-GROUNDWORK-CLEAN: valuation-free mappings and action laws exclude proof-calculus shortcuts")
    print("FOUNDATION-SEPARATION-CLEAN: pure-HOL certificates exclude HOL-ZF; graph/subset representation is separately labelled")
    print("ZF-SOURCE-R-SEPARATION-CLEAN: model-aware coding permits only R models and excludes H/C proof judgments")
    print("ZF-MODEL-STAGE-GUARD-CLEAN: three exact R-to-action-model conclusions; generic supplied-model deductions, premodel regressions, and derived-premodel uses are separately guarded")


if __name__ == "__main__":
    main()
