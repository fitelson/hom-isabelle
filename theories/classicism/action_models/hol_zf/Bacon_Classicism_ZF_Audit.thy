theory Bacon_Classicism_ZF_Audit
  imports Bacon_Source_ZF_Subset_Carriers
    Bacon_Source_ZF_Exponential_Action Bacon_Source_ZF_Powerset_Action
    Bacon_Source_ZF_Individual_Action Bacon_Source_ZF_Reindexed_Action
    Bacon_Source_ZF_Identity_Individual_Base Bacon_Source_ZF_R_Proposition_Range
    Bacon_Source_ZF_R_All_Type_Representation
    Bacon_Source_ZF_R_Constructed_Premodel Bacon_Source_ZF_R_Canonical_Application
    Bacon_Source_ZF_R_Representation_Assignments
    Bacon_Source_ZF_Logical_Value_Evaluation Bacon_Source_ZF_Premodel_Evaluation
    Bacon_Source_ZF_R_Eval_Basic_Correspondence Bacon_Source_ZF_R_Assignment_Naturality
    Bacon_Source_ZF_R_Eval_Lambda_Correspondence Bacon_Source_ZF_R_Negation_Correspondence
    Bacon_Source_ZF_R_Represented_Category_Action_Model Bacon_Source_ZF_Evaluation_Locality
    Bacon_Source_ZF_Action_BBK_Domains Bacon_Source_ZF_Premodel_Naturality_Regression
    Bacon_Source_ZF_Model_Evaluation_Naturality
    Bacon_Source_ZF_Model_Evaluation_Contexts Bacon_Source_ZF_Model_Beta_Conversion
    Bacon_Source_ZF_Model_Eta_Conversion
    Bacon_Source_ZF_Model_Conversion Bacon_Source_ZF_Action_BBK_Interpretation
    Bacon_Source_ZF_Action_BBK_Model Bacon_Source_ZF_Model_Vector_Equality
    Bacon_Source_ZF_Action_Logical_Equivalence
    Bacon_Source_ZF_Action_BBK_Representation
    Bacon_Source_ZF_Action_Classicism_Soundness
    Bacon_Source_ZF_Pure_Action_Completeness
    Bacon_Source_ZF_Arbitrary_Signature_Action_Completeness
begin

section \<open>Separate audit of the HOL-ZF representation groundwork\<close>

text \<open>
  These endpoints are checked relative to the standard HOL-ZF
  set axioms. Their clean kernel objects do not turn that metalogic
  into pure HOL, establish its consistency, or discharge the
  representability of arbitrary source categories.
  The pure-HOL H/C audit remains a separate session and export.
  The source-model-aware entries below permit the independent R model
  predicates as inputs; unlike the generic codecs, they construct actual
  profile ranges. Neither tier permits an F model shortcut or an H/C
  proof judgment. The recursive all-R invariant now supplies actual
  subactions, root constants and the independent action premodel.
  Application closure and typed adequate-assignment roundtrips are also
  covered. The two premodel-construction endpoints retain their exact
  conclusion allowance. A separate generic tier permits premodel-only
  deductions, and the R application step may use its derived premodel.
  Model-free entries check literal logical graphs, strict partial
  evaluator equations and free-variable locality. All six logical families
  and the complete R term induction are now covered. Exact assignment
  roundtrips establish definedness and selected-domain membership for every
  typed adequate partial assignment. The independent action-model criterion
  is proved for the bounded construction, and root truth agrees at the
  actual identity arrow, including open formulas.
  Within the represented-input tier, only the two direct model constructions
  and the reachable-category construction receive a model allowance. Full term
  correspondence and its truth descendants may use the derived premodel,
  but not an assumed action model. Primitive logical cases receive neither
  exception. The original ZF-valued source category, explicit arrow and
  individual bounds, and default-R scope remain essential. These endpoints
  do not establish Proposition 3.21, Classicism completeness, or arbitrary
  HOL-carrier representability.
  A separate generic action-model deduction tier now checks all-R domain
  nonemptiness, logical naturality and the complete model-level C.1
  theorem. It permits the independent action-model and premodel predicates
  but excludes both R/F BBK models and H/C proof judgments; it cannot use
  the earlier representation construction as an extra premise.
  Guarded premodel application and abstraction laws are checked separately.
  Exactly two generic regression roots certify a genuine degenerate
  premodel: defined logical evaluation need not be selected, so source
  partial transport may be undefined. A legal total HOL extension falsifies
  the unguarded equation. This does not refute model-level C.1.
  C.2 contextual congruence now has both raw and typed-adequate guarded
  certificates. C.3 literal capture-free substitution, C.4 beta and C.5 eta
  are checked for the supplied independent action model. The eta proof
  tests every target argument and the complete outgoing-pair graph; no
  arrow-transport surjectivity or BBK semantic conversion is assumed.
  C.6 now retracts raw R conversion into the declared signature, uses
  a derived typed R-only completion for intermediate terms, and restores
  endpoint assignments by raw locality. Candidate J_h structural facts
  include heterogeneous application congruence with potentially overlapping
  domains and the direct action-truth comparison. None assumes a BBK
  validator, transport surjectivity, or middle-term adequacy of the original
  assignment. All six primitive truth clauses and the independent R-BBK
  model certificate at every root arrow are now checked. Exactly one
  reverse-construction root may conclude the R-BBK predicate from a supplied
  ActionModel; this is not a generic BBK assumption allowance or an
  R-source-model input root. Uniform truth over every root-arrow input
  separates proposition values and yields equality under arbitrary binder
  vectors with abstraction-only adequacy. Identity truth at just one input
  is not asserted to suffice. C.7 now obtains uniform truth from a native
  R-H certificate, separates proposition values, lifts equality under the
  binder vector, and applies actual identity truth. The final assignment
  need be adequate only for the concluding vector identity; empty and
  repeated binder lists retain their literal meaning.
  Exactly six H-dependent endpoints permit native paper_R_named_H and
  the derived R-BBK predicate together with a supplied ActionModel. They
  do not assume that BBK model, permit F-H or C judgments, or broaden the
  generic model-deduction tier. Model-only vector identity still forbids H.
  Proposition 3.21 now packages the same fixed R-BBK model at each root
  arrow with both same-assignment truth and validity of every H-certified
  Logical Equivalence instance. No BBK model is an extra package premise.
  Three further exact endpoints prove native R-C soundness in a supplied
  action model through that derived BBK model and the direct five-rule C
  induction. This tier permits native R-C and R-H only, and explicitly
  forbids the separate general R Equivalence-rule judgment as well as
  F/other-C calculi. Root soundness requires only the action model and
  native C derivation, with truth quantified over every typed adequate
  partial assignment. It does not assume the opposite representation's
  carrier bounds, category, or a uniqueness condition on root arrows.
  The construction and C.7 results do not alone establish Classicism
  completeness or eliminate the earlier carrier-representability bounds.
  A separate five-root construction/completeness tier now obtains the
  arrow encoder from the actual size-controlled classical hull, constructs
  an action model and a genuine root counterassignment, and proves the
  Theorem 3.23 iff. Its validity predicate ranges over ALL independent
  action models on the displayed world-index carrier, not just constructed
  BBK labels. In those earlier statements, general signatures retain a represented infinite-set
  bound; pure and countably declared signatures discharge it with Nat.
  The two new Nat/cardinal-code roots remain model/proof-free. None of
  these additions makes HOL-ZF pure HOL, introduces a model premise into
  the actual countermodel theorem, or represents arbitrary HOL carriers.

  The final five endpoints add typed constant pullback and generic validity
  on an explicit world-label type. Finite compression of one formula now
  removes the signature-cardinality premise from the actual countermodel
  and iff on the padded ('c+unit,ZF) record-label carrier. Only constants
  are pulled back; frames, domains, actions and counterassignments stay
  fixed. The quantification still covers all independent action models,
  and the old record-indexed validity is unchanged. No compression of an
  arbitrary infinite theory or embedding of every HOL carrier is claimed.
\<close>

ML_file "../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets = [
    ("graph encoding has the specified function-space type", "paper_ZF_encode_function_type"),
    ("graph decoding has the specified normalized-function type", "paper_ZF_decode_function_type"),
    ("function decode after encode is identity", "paper_ZF_decode_encode_function"),
    ("function encode after decode is identity", "paper_ZF_encode_decode_function"),
    ("actual function graph bijection", "paper_ZF_function_graph_bijection"),
    ("subset decode after encode is identity", "paper_ZF_decode_encode_subset"),
    ("subset encode after decode is identity", "paper_ZF_encode_decode_subset"),
    ("actual powerset carrier bijection", "paper_ZF_subset_carrier_bijection"),
    ("the entire HOL ZF type is not an internal ZF set", "UNIV_is_not_in_ZF"),
    ("actual dependent pair carrier bijection", "paper_ZF_sigma_bijection"),
    ("dependent pair projections reconstruct valid codes", "paper_ZF_sigma_projections"),
    ("dependent function graph bijection", "paper_ZF_dependent_function_graph_bijection"),
    ("dependent function decode after encode", "paper_ZF_decode_encode_dependent_function"),
    ("dependent function encode after decode", "paper_ZF_encode_decode_dependent_function"),
    ("bounded carrier image has an actual bijective code", "paper_ZF_image_code_bijection"),
    ("bounded carrier image decoder is bijective", "paper_ZF_image_inverse_bijection"),
    ("identity arrows give bounded object encoding", "paper_ZF_identity_object_encoding"),
    ("outgoing pair code matches the generic exponential domain", "paper_ZF_pair_code_bijection"),
    ("pair-function graphs have an actual dependent-product bijection", "paper_ZF_pair_function_graph_bijection"),
    ("pair-function decode after encode", "paper_ZF_decode_encode_pair_function"),
    ("pair-function encode after decode", "paper_ZF_encode_decode_pair_function"),
    ("coherent exponential graphs match the generic full fiber", "paper_ZF_action_pair.paper_ZF_exponential_code_bijection"),
    ("exponential decode after encode", "paper_ZF_action_pair.paper_ZF_decode_encode_exponential"),
    ("exponential encode after decode", "paper_ZF_action_pair.paper_ZF_encode_decode_exponential"),
    ("exponential encoding preserves typing and coherence", "paper_ZF_action_pair.paper_ZF_encode_exponential_type"),
    ("exponential decoding preserves typing and coherence", "paper_ZF_action_pair.paper_ZF_decode_exponential_type"),
    ("pair precomposition leaves the target argument unchanged", "paper_ZF_pair_precompose"),
    ("pair advancement transports the target argument", "paper_ZF_pair_advance"),
    ("exponential encoding commutes with precomposition", "paper_ZF_encode_exponential_transport"),
    ("exponential decoding commutes with graph transport", "paper_ZF_action_pair.paper_ZF_decode_exponential_transport"),
    ("coded exponential transport is an actual action", "paper_ZF_action_pair.paper_ZF_exponential_action"),
    ("coded powerset fiber has an actual bijection", "paper_ZF_powerset_fiber_bijection"),
    ("powerset decoding commutes with separation transport", "paper_ZF_decode_powerset_transport"),
    ("coded powerset is an actual action", "paper_ZF_powerset_action"),
    ("coded individual fibers have actual bijections", "paper_ZF_individual_fiber_bijection"),
    ("bounded individual encoding constructs an actual action", "paper_ZF_individual_action"),
    ("individual decoding commutes with transport on fibers", "paper_ZF_individual_decode_transport_on_fiber"),
    ("individual-fiber nonemptiness is preserved", "paper_ZF_individual_fiber_nonempty"),
    ("bounded arrow recoding constructs an actual category", "paper_ZF_recode_category"),
    ("arrow recoding reindexes actions without changing values", "paper_ZF_reindex_action"),
    ("identity-base fiber code retains exactly the original values", "paper_ZF_identity_fiber_elements"),
    ("identity-base value map is an actual fiber bijection", "paper_ZF_identity_base_bijection"),
    ("identity-base fibers retain the original action maps", "paper_ZF_identity_base_action"),
    ("bounded range code contains exactly the image", "paper_ZF_range_code_explode"),
    ("injective bounded family is bijective onto its range code", "paper_ZF_range_fiber_bijection"),
    ("range decode after encode preserves original values", "paper_ZF_range_decode_encode"),
    ("range encode after decode preserves coded values", "paper_ZF_range_encode_decode"),
    ("equivariant bounded range is an actual action", "paper_ZF_range_action"),
    ("equivariant bounded range is an ambient subaction", "paper_ZF_range_subaction"),
    ("range encoding is an equivariant action map", "paper_ZF_range_forward_action_map"),
    ("injective range decoding is an equivariant action map", "paper_ZF_range_inverse_action_map"),
    ("bounded arrow encoding commutes with powerset transport", "paper_ZF_category_encoding.paper_ZF_powerset_reindex"),
    ("R proposition code contains exactly the encoded truth profile", "paper_ZF_R_profile_encoding.paper_ZF_R_truth_profile_code_elements"),
    ("R proposition code reflects membership of original arrows", "paper_ZF_R_profile_encoding.paper_ZF_R_truth_profile_code_on"),
    ("R proposition code lies in the coded outgoing powerset", "paper_ZF_R_profile_encoding.paper_ZF_R_truth_profile_code_type"),
    ("quasi-Fregeanness makes R proposition coding injective", "paper_ZF_R_profile_encoding.paper_ZF_R_truth_profile_code_injective"),
    ("R proposition coding commutes with coded powerset transport", "paper_ZF_R_profile_encoding.paper_ZF_R_truth_profile_code_naturality"),
    ("R proposition coding is an actual action map", "paper_ZF_R_profile_encoding.paper_ZF_R_truth_profile_action_map"),
    ("old R proposition action is reindexed without value changes", "paper_ZF_R_profile_encoding.paper_ZF_R_reindexed_proposition_action"),
    ("R proposition stock is exactly its own encoded profile range", "paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_elements"),
    ("R proposition range is an actual action", "paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_action"),
    ("R proposition range is a coded powerset subaction", "paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_subaction"),
    ("R proposition map targets its own range action", "paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_forward_map"),
    ("quasi-Fregean R proposition fiber is bijective with its range", "paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_bijection"),
    ("R proposition range decoding returns an original typed value", "paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_decode_type"),
    ("R proposition range encode after decode", "paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_encode_decode"),
    ("quasi-Fregean R proposition range decode after encode", "paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_decode_encode"),
    ("quasi-Fregean R proposition inverse is equivariant", "paper_ZF_R_profile_encoding.paper_ZF_R_proposition_range_inverse_map"),
    ("raw R recursion leaves individual values literally unchanged", "paper_ZF_R_type_representation_Ind_encode"),
    ("raw R proposition domain is its specified own-profile range", "paper_ZF_R_type_representation_Prop_domain"),
    ("raw arrow graph encoding evaluates on legitimate pair inputs", "paper_ZF_R_arrow_encode_value"),
    ("representation invariant derives the left inverse on original values", "paper_ZF_R_type_invariant_decode_encode"),
    ("representation invariant derives the right inverse on coded values", "paper_ZF_R_type_invariant_encode_decode"),
    ("representation invariant derives inverse equivariance from the source action", "paper_ZF_R_type_invariant_inverse_map"),
    ("recursive individual fiber is literally the bounded original fiber", "paper_ZF_R_type_encoding.paper_ZF_R_Ind_elements"),
    ("actual individual recursion base satisfies the representation invariant", "paper_ZF_R_type_encoding.paper_ZF_R_Ind_invariant"),
    ("actual proposition recursion base has exactly its encoded range", "paper_ZF_R_type_encoding.paper_ZF_R_Prop_range"),
    ("actual proposition recursion base is a powerset subaction", "paper_ZF_R_type_encoding.paper_ZF_R_Prop_subaction"),
    ("quasi-Fregean proposition base satisfies the representation invariant", "paper_ZF_R_type_encoding.paper_ZF_R_Prop_invariant"),
    ("arrow body coherence follows from the child action maps", "paper_ZF_R_arrow_step.paper_ZF_R_arrow_body_coherent"),
    ("every encoded original arrow value belongs to its exponential bound", "paper_ZF_R_arrow_step.paper_ZF_R_arrow_code_type"),
    ("arrow range contains every encoded original value without truncation", "paper_ZF_R_arrow_step.paper_ZF_R_arrow_range_elements"),
    ("arrow body naturality retains all target-domain tests", "paper_ZF_R_arrow_body_naturality"),
    ("arrow graph encoding commutes with canonical exponential transport", "paper_ZF_R_arrow_encode_naturality"),
    ("child injectivity and quasi-functionality imply new arrow injectivity", "paper_ZF_R_arrow_encode_injective_from_children"),
    ("the actual arrow range inherits an action", "paper_ZF_R_arrow_step.paper_ZF_R_arrow_range_action"),
    ("arrow constructor preserves the representation invariant", "paper_ZF_R_arrow_invariant"),
    ("actual structural recursion satisfies the invariant at every R type", "paper_ZF_R_type_encoding.paper_ZF_R_all_type_invariant"),
    ("root-arrow recoding retains the complete root-arrow fiber", "paper_ZF_category_encoding.paper_ZF_root_arrows_bijection"),
    ("bounded arrow recoding preserves weak rootedness", "paper_ZF_category_encoding.paper_ZF_encoded_rooted_category"),
    ("forward representation assignment preserves its domain", "paper_ZF_R_encode_assignment_domain"),
    ("inverse representation assignment preserves its domain", "paper_ZF_R_decode_assignment_domain"),
    ("forward representation assignment preserves adequacy exactly", "paper_ZF_R_encode_assignment_adequate_iff"),
    ("inverse representation assignment preserves adequacy exactly", "paper_ZF_R_decode_assignment_adequate_iff"),
    ("actual recursive domains are empty outside R", "paper_ZF_R_type_representation_domain_nonR"),
    ("constructed proposition domain satisfies the premodel subaction clause", "paper_ZF_R_type_encoding.paper_ZF_R_premodel_Prop_subaction"),
    ("constructed arrow domains are subactions of actual child exponentials", "paper_ZF_R_type_encoding.paper_ZF_R_premodel_arrow_subaction"),
    ("bounded original individuals give nonempty constructed individual fibers", "paper_ZF_R_type_encoding.paper_ZF_R_Ind_nonempty"),
    ("declared root constants belong to their actual constructed domains", "paper_ZF_R_type_encoding.paper_ZF_R_root_constant_type"),
    ("root constants transport through every encoded original arrow", "paper_ZF_R_type_encoding.paper_ZF_R_root_constant_transport"),
    ("recursive domains and root constants construct an independent action premodel", "paper_ZF_R_type_encoding.paper_ZF_R_constructed_premodel"),
    ("an intensional represented rooted R category gives an actual premodel", "paper_ZF_R_type_encoding.paper_ZF_R_intensional_constructed_premodel"),
    ("canonical identity-arrow application preserves original R application", "paper_ZF_R_type_encoding.paper_ZF_R_application_correspondence"),
    ("application is closed on every pair of constructed-domain values", "paper_ZF_R_type_encoding.paper_ZF_R_application_closed"),
    ("forward assignment coding preserves typing at all assigned R slots", "paper_ZF_R_type_encoding.paper_ZF_R_encode_assignment_typed"),
    ("inverse assignment coding recovers original typing without non-R inverses", "paper_ZF_R_type_encoding.paper_ZF_R_decode_assignment_typed"),
    ("typed original partial assignments survive decode after encode", "paper_ZF_R_type_encoding.paper_ZF_R_decode_encode_assignment"),
    ("typed constructed partial assignments survive encode after decode", "paper_ZF_R_type_encoding.paper_ZF_R_encode_decode_assignment"),
    ("graph application succeeds exactly on a functional graph and domain input", "paper_ZF_graph_apply_Some_iff"),
    ("graph application explicitly fails outside its guards", "paper_ZF_graph_apply_None_iff"),
    ("guarded graph application returns its actual value", "paper_ZF_graph_apply_defined_value"),
    ("literal negation graph evaluates to outgoing complement", "paper_ZF_logical_not_apply"),
    ("literal conjunction graph evaluates to transported intersection", "paper_ZF_logical_and_apply"),
    ("literal disjunction graph evaluates to transported union", "paper_ZF_logical_or_apply"),
    ("literal universal graph tests every target-domain argument", "paper_ZF_logical_forall_apply"),
    ("literal existential graph tests some target-domain argument", "paper_ZF_logical_exists_apply"),
    ("literal identity graph tests equal transported values", "paper_ZF_logical_identity_apply"),
    ("quantifier tests are typed when their predicate is an actual dependent graph", "paper_ZF_logical_quantifier_test_type"),
    ("strict abstraction is defined when every outgoing body evaluation succeeds", "paper_ZF_action_abstract_defined"),
    ("strict abstraction failure is witnessed by an undefined body input", "paper_ZF_action_abstract_None_iff"),
    ("a returned abstraction is a function graph with the exact pair domain", "paper_ZF_action_abstract_graph"),
    ("returned abstraction evaluates after transport then binder update", "paper_ZF_action_abstract_apply"),
    ("partial evaluator application has exact success and graph-domain guards", "paper_ZF_action_eval_application_Some_iff"),
    ("partial evaluator abstraction obeys the literal outgoing-pair equation", "paper_ZF_action_eval_abstraction_apply"),
    ("partial evaluator abstraction retains strict failure semantics", "paper_ZF_action_eval_abstraction_None_iff"),
    ("typed adequate variable evaluation needs no premodel assumption", "paper_ZF_action_eval_variable_typed"),
    ("action transport preserves explicitly R-supported assignment typing", "paper_ZF_action_transport_env_typed"),
    ("an independent premodel supplies application graph definedness and closure", "paper_ZF_premodel_application_info"),
    ("declared constants evaluate with the premodel root type", "paper_ZF_action_eval_constant_typed"),
    ("premodel application evaluation is typed from defined typed subterms", "paper_ZF_action_eval_application_typed"),
    ("constructed R evaluator has the original encoded variable value", "paper_ZF_R_type_encoding.paper_ZF_R_eval_Var"),
    ("constructed R evaluator has the original encoded constant value", "paper_ZF_R_type_encoding.paper_ZF_R_eval_Const"),
    ("constructed R evaluator application step uses only its two induction hypotheses", "paper_ZF_R_type_encoding.paper_ZF_R_eval_App"),
    ("forward representation assignments commute with every coded arrow", "paper_ZF_R_type_encoding.paper_ZF_R_encode_assignment_naturality"),
    ("inverse representation assignments commute with every coded arrow", "paper_ZF_R_type_encoding.paper_ZF_R_decode_assignment_naturality"),
    ("Lambda body input is the encoding of the transported updated old assignment", "paper_ZF_R_type_encoding.paper_ZF_R_lambda_input_assignment"),
    ("Lambda body preimage assignment is typed and adequate", "paper_ZF_R_type_encoding.paper_ZF_R_lambda_old_input"),
    ("encoded old abstraction has the required value at every outgoing pair", "paper_ZF_R_type_encoding.paper_ZF_R_lambda_graph_value"),
    ("independent evaluator Lambda step uses only the uniform strict-body induction hypothesis", "paper_ZF_R_type_encoding.paper_ZF_R_eval_Lam"),
    ("coded R negation profile is exactly the outgoing complement", "paper_ZF_R_profile_encoding.paper_ZF_R_negation_profile_code"),
    ("encoded empty-assignment negation equals the independent literal graph", "paper_ZF_R_type_encoding.paper_ZF_R_Not_empty_correspondence"),
    ("encoded negation at every typed assignment equals the literal graph", "paper_ZF_R_type_encoding.paper_ZF_R_Not_correspondence"),
    ("independent evaluator Not case equals the encoded original value", "paper_ZF_R_type_encoding.paper_ZF_R_eval_Not"),
    ("coded arrows preserve original R application", "paper_ZF_R_profile_encoding.paper_ZF_R_coded_application_transport"),
    ("encoded arrow application has its actual pair-domain value", "paper_ZF_R_type_encoding.paper_ZF_R_type_encode_pair_value"),
    ("partial binary logical graphs cover every inner pair", "paper_ZF_R_type_encoding.paper_ZF_R_binary_partial_graph"),
    ("binary logical graphs cover both complete nested pair domains", "paper_ZF_R_type_encoding.paper_ZF_R_binary_logical_graph"),
    ("conjunction profile coding preserves the actual set operation", "paper_ZF_R_profile_encoding.paper_ZF_R_conjunction_profile_code"),
    ("conjunction original value equals the independent literal graph", "paper_ZF_R_type_encoding.paper_ZF_R_And_empty_correspondence"),
    ("independent evaluator And case has the original encoded value", "paper_ZF_R_type_encoding.paper_ZF_R_eval_And"),
    ("disjunction profile coding preserves the actual set operation", "paper_ZF_R_profile_encoding.paper_ZF_R_disjunction_profile_code"),
    ("disjunction original value equals the independent literal graph", "paper_ZF_R_type_encoding.paper_ZF_R_Or_empty_correspondence"),
    ("independent evaluator Or case has the original encoded value", "paper_ZF_R_type_encoding.paper_ZF_R_eval_Or"),
    ("identity profile coding tests original transported equality", "paper_ZF_R_profile_encoding.paper_ZF_R_identity_profile_code"),
    ("identity codes reflect equality using child encoding injectivity", "paper_ZF_R_type_encoding.paper_ZF_R_identity_code_at_values"),
    ("identity equals the literal doubly transported equality graph", "paper_ZF_R_type_encoding.paper_ZF_R_Eq_empty_correspondence"),
    ("independent evaluator identity case holds at every R type", "paper_ZF_R_type_encoding.paper_ZF_R_eval_Eq"),
    ("encoded predicate tests recover original application truth", "paper_ZF_R_type_encoding.paper_ZF_R_predicate_source_test"),
    ("quantifier tests cover every represented target-domain value", "paper_ZF_R_type_encoding.paper_ZF_R_quantifier_tests"),
    ("quantified truth profiles equal the literal target-test subset", "paper_ZF_R_type_encoding.paper_ZF_R_quantifier_profile_code"),
    ("both quantifier values equal their independent literal graphs", "paper_ZF_R_type_encoding.paper_ZF_R_quantifier_empty_correspondence"),
    ("independent evaluator handles universal and existential families", "paper_ZF_R_type_encoding.paper_ZF_R_eval_quantifier"),
    ("identity membership in a proposition code is original truth", "paper_ZF_R_profile_encoding.paper_ZF_R_proposition_identity_truth"),
    ("all six independent logical families have encoded original values", "paper_ZF_R_type_encoding.paper_ZF_R_eval_Logical"),
    ("structural R typing induction discharges every evaluator case", "paper_ZF_R_type_encoding.paper_ZF_R_eval_typed_correspondence"),
    ("every R-language term has its encoded original interpretation", "paper_ZF_R_type_encoding.paper_ZF_R_eval_correspondence"),
    ("every new adequate assignment is covered by exact decoding", "paper_ZF_R_type_encoding.paper_ZF_R_eval_decoded"),
    ("every adequate evaluation is defined and in the selected domain", "paper_ZF_R_type_encoding.paper_ZF_R_eval_total_typed"),
    ("bounded quasi-Fregean quasi-functional construction is an action model", "paper_ZF_R_type_encoding.paper_ZF_R_constructed_model"),
    ("bounded intensional construction satisfies the independent model criterion", "paper_ZF_R_type_encoding.paper_ZF_R_intensional_constructed_model"),
    ("truth agrees at every encoded adequate assignment", "paper_ZF_R_type_encoding.paper_ZF_R_holds_encoded"),
    ("truth agrees at every new adequate assignment", "paper_ZF_R_type_encoding.paper_ZF_R_holds_decoded"),
    ("all-assignment truth agrees at every root arrow", "paper_ZF_R_type_encoding.paper_ZF_R_arrow_validity_iff"),
    ("truth in the original root model equals truth at the coded identity", "paper_ZF_R_type_encoding.paper_ZF_R_root_validity_iff"),
    ("reachable restriction gives an actual bounded action model with the same root truth", "paper_ZF_R_type_encoding.paper_ZF_R_represented_category_action_model"),
    ("raw partial evaluation depends only on free-variable assignments", "paper_ZF_action_eval_locality"),
    ("normalized R BBK-domain typing is exactly supported action typing", "paper_ZF_action_bbk_env_iff"),
    ("the degenerate logical example has legitimate typed adequate inputs", "paper_ZF_degenerate_regression_guards"),
    ("unguarded premodel naturality fails for a legal off-domain extension", "paper_ZF_degenerate_totalized_naturality_fails"),
    ("defined negation has undefined selected-fiber partial transport", "paper_ZF_degenerate_partial_transport_undefined"),
    ("target-dependent pair graphs commute with canonical precomposition", "paper_ZF_pair_lambda_target_naturality"),
    ("all six literal logical graphs commute with canonical precomposition", "paper_ZF_logical_value_precompose"),
    ("R-supported partial assignments satisfy identity transport", "paper_ZF_action_assignment_transport_identity"),
    ("R-supported partial assignments satisfy composed transport", "paper_ZF_action_assignment_transport_compose"),
    ("canonical exponential transport evaluates by precomposition", "paper_ZF_exponential_transport_apply"),
    ("a premodel supplies the assignment identity law", "paper_ZF_premodel_assignment_transport_identity"),
    ("a premodel supplies the assignment composition law", "paper_ZF_premodel_assignment_transport_compose"),
    ("premodel application naturality retains both selected-value guards", "paper_ZF_premodel_application_naturality"),
    ("defined abstraction commutes with canonical exponential transport", "paper_ZF_action_abstract_naturality"),
    ("own-action abstraction naturality requires selected membership", "paper_ZF_premodel_eval_Lam_naturality"),
    ("own-action logical naturality requires selected logical membership", "paper_ZF_premodel_logical_naturality"),
    ("one-object empty-relational-stock construction is an actual premodel", "paper_ZF_degenerate_premodel"),
    ("an actual premodel can define a logical value outside its selected stock", "paper_ZF_premodel_defined_value_need_not_be_selected"),
    ("a supplied action model produces typed values through actual root arrows", "paper_ZF_action_model_value_at_object"),
    ("a supplied action model has nonempty domains at every R type", "paper_ZF_action_model_R_domain_nonempty"),
    ("normalized R domains of a supplied action model are nonempty", "paper_ZF_action_bbk_domain_nonempty"),
    ("a supplied model discharges selected logical-value membership", "paper_ZF_action_model_logical_value_member"),
    ("logical naturality follows from the independent action-model criterion", "paper_ZF_action_model_logical_naturality"),
    ("C.1 holds for every typed adequate interpretation in a supplied action model", "paper_ZF_action_model_eval_naturality"),
    ("abstraction congruence preserves both strict definedness and graph values", "paper_ZF_action_abstract_cong"),
    ("uniform raw evaluator equality lifts through every named context", "paper_ZF_action_eval_compatible"),
    ("typed adequate contextual equality preserves all premodel input guards", "paper_ZF_premodel_eval_compatible"),
    ("C.3 literal capture-free substitution holds for partial adequate assignments", "paper_ZF_action_model_substitution"),
    ("C.4 beta follows from graph application and literal substitution", "paper_ZF_action_model_beta"),
    ("C.5 eta compares every outgoing pair without transport surjectivity", "paper_ZF_action_model_eta"),
    ("transported application tests arbitrary target arguments at identity", "paper_ZF_premodel_transport_identity_application"),
    ("every dependent function graph equals Lambda of its actual applications", "paper_ZF_Pi_as_application_graph"),
    ("contextual beta preserves evaluation with both endpoint guards", "paper_ZF_action_model_beta_step"),
    ("contextual eta preserves evaluation with both endpoint guards", "paper_ZF_action_model_eta_step"),
    ("signature conversion preserves evaluation under R-total assignments", "paper_ZF_action_model_signature_conversion_total"),
    ("signature conversion needs adequacy only for its endpoints", "paper_ZF_action_model_signature_conversion"),
    ("C.6 raw R conversion is retracted into the declared signature", "paper_ZF_action_model_raw_conversion"),
    ("the candidate root-arrow denotation has an actual selected value", "paper_ZF_action_bbk_denote_total"),
    ("candidate application has its actual graph and valid identity-pair input", "paper_ZF_action_bbk_denote_application_data"),
    ("candidate application congruence allows heterogeneous overlapping domains", "paper_ZF_action_bbk_denote_application_cong"),
    ("candidate valuation matches the independent action-model truth predicate", "paper_ZF_action_bbk_holds_iff"),
    ("candidate denotation locality follows from raw partial-evaluator locality", "paper_ZF_action_bbk_denote_locality"),
    ("selected proposition values contain only legitimate outgoing arrows", "paper_ZF_premodel_proposition_member"),
    ("identity truth after proposition transport is original arrow membership", "paper_ZF_premodel_proposition_transport_test"),
    ("formula truth after each outgoing arrow tests the original proposition value", "paper_ZF_action_model_formula_outgoing_truth"),
    ("uniform truth at all root inputs separates proposition values", "paper_ZF_action_model_uniform_truth_equal"),
    ("candidate logical denotation is the independently defined literal graph", "paper_ZF_action_bbk_denote_logical"),
    ("unary logical application uses the actual graph at a guarded identity pair", "paper_ZF_action_bbk_unary_logical_denote"),
    ("binary logical application uses both guarded identity pairs", "paper_ZF_action_bbk_binary_logical_denote"),
    ("fresh-variable updates realize every target predicate argument", "paper_ZF_action_bbk_fresh_predicate_test"),
    ("candidate negation truth is outgoing complement", "paper_ZF_action_bbk_valuation_neg"),
    ("candidate conjunction truth is transported intersection", "paper_ZF_action_bbk_valuation_conj"),
    ("candidate disjunction truth is transported union", "paper_ZF_action_bbk_valuation_disj"),
    ("candidate identity truth is actual equality at every R type", "paper_ZF_action_bbk_valuation_identity"),
    ("candidate universal truth ranges over every target-domain value", "paper_ZF_action_bbk_valuation_forall"),
    ("candidate existential truth ranges over every target-domain value", "paper_ZF_action_bbk_valuation_exists"),
    ("uniform body equality lifts under arbitrary literal binder vectors", "paper_ZF_premodel_vector_equality"),
    ("uniform truth yields vector equality with abstraction-only adequacy", "paper_ZF_action_model_uniform_truth_vector_equal"),
    ("candidate denotation respects raw R conversion by the proved C6 theorem", "paper_ZF_action_bbk_denote_beta_eta"),
    ("each root arrow of a supplied action model yields an actual independent R BBK model", "paper_ZF_action_to_R_bbk_model"),
    ("uniform truth validates literal vector identity without H or C assumptions", "paper_ZF_action_model_uniform_truth_vector_identity"),
    ("native R H truth follows through the derived R BBK model at every root arrow", "paper_ZF_action_model_H_truth"),
    ("an H-certified literal biconditional gives uniform truth agreement", "paper_ZF_action_model_H_iff_truth"),
    ("C7 validates H-certified Logical Equivalence with abstraction-only adequacy", "paper_ZF_action_model_logical_equivalence"),
    ("C7 holds at every typed assignment adequate for the final identity formula", "paper_ZF_action_model_logical_equivalence_at_assignment"),
    ("every H-certified Logical Equivalence instance is valid in the same constructed R BBK model", "paper_ZF_action_bbk_logical_equivalence_valid"),
    ("Proposition3.21 packages one R BBK model with same truth and all Logical Equivalence instances", "paper_ZF_action_bbk_representation"),
    ("native R Classicism is valid in the derived root-arrow R BBK model", "paper_ZF_action_classicism_BBK_valid"),
    ("native R Classicism holds at every typed adequate root-arrow input", "paper_ZF_action_classicism_truth"),
    ("native R Classicism is sound at the root identity of every supplied action model", "paper_ZF_action_classicism_soundness"),
    ("the actual HOL-ZF set Nat has an infinite decoded carrier", "paper_ZF_nat_values_infinite"),
    ("a proved cardinal bound yields an actual bounded injection without a global carrier assumption", "paper_ZF_cardinal_bounded_encoding"),
    ("the size-controlled classical hull constructs an action model and preserves all root truth", "paper_ZF_classicism_hull_action_representation"),
    ("a native C non-theorem has an actual action model and a typed adequate root counterassignment", "paper_ZF_action_countermodel"),
    ("native C equals validity in all actual action models on the fixed world carrier under the represented signature bound", "paper_ZF_classicism_action_iff"),
    ("pure Classicism has action completeness using the actual HOL-ZF set Nat", "paper_ZF_pure_classicism_action_iff"),
    ("countably many declared names suffice for action completeness without ambient name-type countability", "paper_ZF_countable_classicism_action_iff"),
    ("typed constant pullback preserves the full partial evaluator including undefined results", "paper_ZF_action_eval_typed_constants"),
    ("pulling back only constants preserves an actual independent action model", "paper_ZF_action_model_typed_constant_pullback"),
    ("old record-indexed validity is exactly generic validity at its original world-label type", "paper_ZF_record_action_valid_as_valid_on"),
    ("arbitrary-signature C non-theorems have actual action countermodels on the explicit padded label carrier", "paper_ZF_arbitrary_signature_action_countermodel"),
    ("arbitrary-signature C equals validity in all independent action models on the padded label carrier", "paper_ZF_arbitrary_signature_action_iff")
  ]
  val checked = Bacon_Core_Audit_Check.run @{context} "HOL-ZF-representation"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF set axioms, not pure HOL\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "zf-representation-audit.txt")) [XML.Text report]
  val _ = writeln ("HOL-ZF-REPRESENTATION-AUDIT-CLEAN: " ^ string_of_int (length targets)
    ^ " endpoints; standard HOL-ZF foundation")
end
\<close>

end
