session Bacon_Base in "theories/base" = HOL +
  description "
    Bacon's base higher-order language and the context-indexed proof
    theory H_proves with IndividualExistence (an intermediate variant; the
    exact source calculi are in the source-vocabulary session).
  "
  sessions
    "HOL-Library"
  theories
    Bacon_Deduction

session Bacon_Source_Vocabulary_Development in "theories/base/source_vocabulary" = Bacon_Base +
  description "
    Exact first-class logical vocabularies for Bacon--Dorr and Bacon's
    minimal book basis, with source-to-core translation developed in leaves.
  "
  options [timeout = 60, export_theory = true]
  sessions
    Bacon_Parametric_Signature_Development
  theories
    Bacon_Source_Proof_Connectives
    Bacon_Source_Finite_Typing
    Bacon_Source_Global_Existence
    Bacon_Source_Conversion_Axioms
    Bacon_Source_Closed_Proof_Preservation
    Bacon_Source_Closing_Proof_Transport
    Bacon_Source_Axiom_Guards
    Bacon_Source_Reverse_Binding
    Bacon_Source_Variable_Embedding
    Bacon_Source_Conversion_Contexts
    Bacon_Source_Roundtrip
    Bacon_Source_Reverse_PC
    Bacon_Source_Renaming_Conversion
    Bacon_Source_Reverse_Conversion
    Bacon_Source_Global_PC_Embedding
    Bacon_Source_Reverse_Identity_Axioms
    Bacon_Source_Global_Proof_Basics
    Bacon_Source_Reverse_Quantifier_Axioms
    Bacon_Source_Reverse_Quantifier_Rules
    Bacon_Source_Reverse_Proof_Preservation
    Bacon_Source_Proof_Correspondence
    Bacon_Source_Local_Deduction
    Bacon_Source_Target_Local_Conversion
    Bacon_Source_Closed_Set_Preservation
    Bacon_Source_Local_Conversion_Transport
    Bacon_Source_Reverse_Set_Preservation
    Bacon_Source_Set_Correspondence
    Bacon_Source_Consistency_Correspondence
    Bacon_Source_BBK_Interface
    Bacon_Source_BBK_Pullback_Truth
    Bacon_Source_Reverse_Guarded_Conversion
    Bacon_Source_BBK_Pullback_Model
    Bacon_Source_BBK_Binding
    Bacon_Source_BBK_Roundtrip
    Bacon_Source_Vector_Syntax
    Bacon_Source_Vector_Beta
    Bacon_Source_Vector_Mapped_Beta
    Bacon_Source_BBK_Vector_Congruence
    Bacon_Source_BBK_Renaming_Derived
    Bacon_Source_BBK_Reverse_Booleans
    Bacon_Source_BBK_Reverse_Quantifiers
    Bacon_Source_BBK_Reverse_Model
    Bacon_Source_Named_Syntax
    Bacon_Source_Named_Representation
    Bacon_Source_Named_Alpha
    Bacon_Source_Named_Alpha_Representation
    Bacon_Source_Named_Alpha_Characterization
    Bacon_Source_Named_Assignments
    Bacon_Source_Named_Substitution
    Bacon_Source_Named_Substitution_Representation
    Bacon_Source_Named_Eta_Representation
    Bacon_Source_Named_Conversion
    Bacon_Source_Named_Alpha_Conversion
    Bacon_Source_Named_Raw_Conversion
    Bacon_Source_Named_Signature_Conservativity
    Bacon_Source_Named_Decoder
    Bacon_Source_Named_Decoder_Roundtrip
    Bacon_Source_Named_Decoder_Beta
    Bacon_Source_Named_Decoder_Eta
    Bacon_Source_Named_Decoder_Conversion
    Bacon_Source_Named_Chart_Prefix
    Bacon_Source_Minimal_Frame
    Bacon_Source_Named_Coherent_Charts
    Bacon_Source_Named_Closed_Roundtrip
    Bacon_Source_Named_Prefix_Roundtrip
    Bacon_Source_Named_H
    Bacon_Source_Named_Local_Forward
    Bacon_Source_Named_H_Alpha
    Bacon_Source_Named_H_Reverse_Rules
    Bacon_Source_Named_H_Reverse_Conversion
    Bacon_Source_Named_H_Correspondence
    Bacon_Source_Named_Existence
    Bacon_Source_Named_Local_Correspondence
    Bacon_Source_Named_Consistency_Correspondence
    Bacon_Source_Named_Sentence_Sets
    Bacon_Source_Named_Consistent_Negation
    Bacon_Source_Named_Representation_Reflection
    Bacon_Source_Named_Vectors
    Bacon_Source_Named_Vector_Encoding
    Bacon_Source_BBK_Global_Assignments

session Bacon_Book_Environment_Development in "theories/base/book_models" = Bacon_Source_Vocabulary_Development +
  description "
    Source-first book language, typed applicative structures, total named
    assignments, exact environment condition, and the full minimal-basis
    Leibnizian quotient with witnessed logical values; the exact book
    theory calculus, substitution admissibility (Bacon_Book_Logic), general
    models, the Henkin construction and printed completeness
    (Bacon_Book_Printed_Completeness). General-language scope remains
    separate; the relevant (λI) language has its own session.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_Book_Environment
    Bacon_Book_Full_Environment
    Bacon_Book_Environment_Equivalence
    Bacon_Book_Closed_Values
    Bacon_Book_Identity_Predicate
    Bacon_Book_Leibniz_Valuation
    Bacon_Book_Implication_Valuation
    Bacon_Book_Leibniz_Application_Tests
    Bacon_Book_Head_Test
    Bacon_Book_Leibniz_Application
    Bacon_Book_Quotient_Application
    Bacon_Book_Leibniz_Assignments
    Bacon_Book_Quotient_Separation
    Bacon_Book_Quotient_Environment
    Bacon_Book_Full_Minimal_Model
    Bacon_Book_Quotient_Logical_Clauses
    Bacon_Book_Full_Minimal_Quotient
    Bacon_Book_Quotient_Truth
    Bacon_Book_Quotient_Theorem
    Bacon_Book_Minimal_Formula_Syntax
    Bacon_Book_Theory_Derivation
    Bacon_Book_Minimal_Validity
    Bacon_Book_Theory_Axiom_Soundness
    Bacon_Book_Theory_Soundness
    Bacon_Book_Model_Class_Theory
    Bacon_Book_Minimal_Boolean_Truth
    Bacon_Book_Open_Deduction_Boundary
    Bacon_Book_BBK_False_Value
    Bacon_Book_BBK_Logical_Values
    Bacon_Book_Named_Translation
    Bacon_Book_BBK_Environment
    Bacon_Book_BBK_Model
    Bacon_Book_Theory_Conversion
    Bacon_Book_Swap_Abbreviations
    Bacon_Book_Theory_Variable_Substitution
    Bacon_Book_Minimal_Existential_Truth
    Bacon_Book_Minimal_Leibniz_Truth
    Bacon_Book_Theory_Signature_Monotonicity
    Bacon_Book_Theory_Retraction
    Bacon_Book_Theory_Signature_Conservativity
    Bacon_Book_Theory_Constant_Substitution
    Bacon_Book_Finite_Fresh_Variables
    Bacon_Book_Simultaneous_Substitution_Syntax
    Bacon_Book_Simultaneous_Substitution_Language
    Bacon_Book_Simultaneous_Substitution_Singleton
    Bacon_Book_Substitution_Freshness
    Bacon_Book_Simultaneous_Substitution_Peeling
    Bacon_Book_Simultaneous_Substitution_Peeling_Free_For
    Bacon_Book_Theory_Simultaneous_Substitution
    Bacon_Book_Logic
    Bacon_Book_H_Soundness
    Bacon_Book_Propositional_Certificates
    Bacon_Book_Negation_Conversion
    Bacon_Book_Propositional_Explosion
    Bacon_Book_Propositional_Negation
    Bacon_Book_Conjunction_Certificates
    Bacon_Book_Conjunction_Currying
    Bacon_Book_Closed_Deduction
    Bacon_Book_Universal_Closure
    Bacon_Book_Universal_Closure_Truth
    Bacon_Book_Universal_Closure_Theories
    Bacon_Book_Open_Propositional_Decision
    Bacon_Book_Theory_Consistency
    Bacon_Book_Consistency_Unions
    Bacon_Book_Existential_Conversion
    Bacon_Book_Fresh_Constant_Generalization
    Bacon_Book_Constant_Renaming
    Bacon_Book_Theory_Constant_Renaming
    Bacon_Book_Negative_Predicate_Generalization
    Bacon_Book_Closed_Witness_Choice
    Bacon_Book_Closed_Maximal_Extension
    Bacon_Book_Constant_Renaming_Reflection
    Bacon_Book_Closed_Negation_Complete
    Bacon_Book_Fresh_Witness_Name
    Bacon_Book_Conditional_Witness
    Bacon_Book_Fresh_Conditional_Witness
    Bacon_Book_Henkin_Name_Stages
    Bacon_Book_Finite_Image_Cover
    Bacon_Book_Witness_Family_Syntax
    Bacon_Book_Finite_Witness_Family
    Bacon_Book_Infinite_Witness_Family
    Bacon_Book_Henkin_Stage_Witnesses
    Bacon_Book_Henkin_Full_Signature
    Bacon_Book_Henkin_Stage_Consistency
    Bacon_Book_Henkin_Premise_Stages
    Bacon_Book_Henkin_Witness_Coverage
    Bacon_Book_Henkin_Union
    Bacon_Book_Closed_Witness_Completeness
    Bacon_Book_Closed_Henkin_Extension
    Bacon_Book_Henkin_Closed_Terms
    Bacon_Book_Conversion_Classes
    Bacon_Book_Closed_Environment_Substitution
    Bacon_Book_Closed_Maximal_Truth
    Bacon_Book_Conversion_Application
    Bacon_Book_Conversion_Valuation
    Bacon_Book_Conversion_Domain_Inhabitation
    Bacon_Book_Environment_Substitution_Beta_Syntax
    Bacon_Book_Environment_Substitution_Contractions
    Bacon_Book_Conversion_Denotation
    Bacon_Book_Conversion_Logical_Values
    Bacon_Book_Environment_Substitution_Conversion
    Bacon_Book_Quantifier_Proof_Basics
    Bacon_Book_Conversion_Environment
    Bacon_Book_Closed_Universal_Instances
    Bacon_Book_Closed_Quantifier_Duality
    Bacon_Book_Conversion_Closed_Values
    Bacon_Book_Closed_Universal_Truth
    Bacon_Book_Conversion_Truth_Projection
    Bacon_Book_Conversion_Universal_Valuation
    Bacon_Book_Conversion_Model
    Bacon_Book_Conversion_Expanded_Model_Existence
    Bacon_Book_Constant_Renaming_Conversion
    Bacon_Book_Constant_Model_Pullback
    Bacon_Book_Canonical_Model_Existence
    Bacon_Book_Canonical_Countermodel
    Bacon_Book_Canonical_Completeness
    Bacon_Book_Closed_Value_Convention
    Bacon_Book_General_Environment
    Bacon_Book_General_Application
    Bacon_Book_Variable_Substitution_Language
    Bacon_Book_Reduction_Language
    Bacon_Book_Logical_Substitution_Syntax
    Bacon_Book_Contextual_Reduction_Language
    Bacon_Book_Alpha_Language
    Bacon_Book_Printed_Free_For
    Bacon_Book_Source_Reduction
    Bacon_Book_Variable_Relettering_Syntax
    Bacon_Book_General_Lambda_Language
    Bacon_Book_General_Interpretation
    Bacon_Book_Printed_Binder_Freshening
    Bacon_Book_Printed_Beta_Simulation
    Bacon_Book_Full_General_Language
    Bacon_Book_Printed_Conversion
    Bacon_Book_Printed_Conversion_Contexts
    Bacon_Book_Printed_Binder_Conversion
    Bacon_Book_Printed_Alpha_Alignment
    Bacon_Book_Printed_Alpha_Conversion
    Bacon_Book_Source_Reduction_Contexts
    Bacon_Book_Printed_Contextual_Beta_Simulation
    Bacon_Book_Source_Reduction_Conversion
    Bacon_Book_Printed_Conversion_Correspondence
    Bacon_Book_Printed_Theory_Derivation
    Bacon_Book_Printed_Theory_Propositional_Basics
    Bacon_Book_Printed_Theory_Conversion
    Bacon_Book_Printed_Theory_Correspondence
    Bacon_Book_Printed_Completeness
    Bacon_Book_Primitive_Conjunction_Syntax
    Bacon_Book_Primitive_Conjunction_Encoding
    Bacon_Book_Primitive_Conjunction_Decoding
    Bacon_Book_Conjunction_Axiom_Truth
    Bacon_Book_Primitive_Conjunction_Axiom_Theory
    Bacon_Book_Conjunction_Binding_Transport
    Bacon_Book_Conjunction_Step_Transport
    Bacon_Book_Conjunction_Conversion_Transport
    Bacon_Book_Primitive_Conjunction_Formula_Syntax
    Bacon_Book_Primitive_Conjunction_Theory_Derivation
    Bacon_Book_Conjunction_Background_Decoding
    Bacon_Book_Conjunction_Proof_Encoding
    Bacon_Book_Conjunction_Proof_Decoding
    Bacon_Book_Primitive_Conjunction_Model
    Bacon_Book_Conjunction_Proof_Correspondence
    Bacon_Book_Conjunction_Raw_Conversion_Transport
    Bacon_Book_Conjunction_Encoding_Environment
    Bacon_Book_Conjunction_Background_Truth
    Bacon_Book_Conjunction_Decoding_Environment
    Bacon_Book_Conjunction_Model_From_Background
    Bacon_Book_Conjunction_Decoded_Model
    Bacon_Book_Conjunction_Decoded_Background_Truth
    Bacon_Book_Conjunction_Model_Existence
    Bacon_Book_Conjunction_Theory_Soundness
    Bacon_Book_Conjunction_Countermodel
    Bacon_Book_Conjunction_Completeness
    Bacon_Book_Conjunction_Constant_Substitution_Transport
    Bacon_Book_Conjunction_Variable_Substitution
    Bacon_Book_Conjunction_Background_Retraction
    Bacon_Book_Conjunction_Background_Fresh_Constant
    Bacon_Book_Conjunction_Constant_Substitution
    Bacon_Book_Conjunction_Theory
    Bacon_Book_Conjunction_Theory_Clauses
    Bacon_Book_Conjunction_Simultaneous_Substitution_Singleton
    Bacon_Book_Conjunction_Simultaneous_Substitution
    Bacon_Book_Conjunction_Logic
    Bacon_Book_Conjunction_Logic_Completeness
    Bacon_Book_Disjunction_Axiom_Truth
    Bacon_Book_Primitive_Disjunction_Syntax
    Bacon_Book_Primitive_Disjunction_Encoding
    Bacon_Book_Primitive_Disjunction_Decoding
    Bacon_Book_Disjunction_Formula_Syntax
    Bacon_Book_Primitive_Disjunction_Axiom_Theory
    Bacon_Book_Primitive_Disjunction_Theory_Derivation
    Bacon_Book_Disjunction_Background_Truth
    Bacon_Book_Disjunction_Formula_Transport
    Bacon_Book_Disjunction_Binding_Transport
    Bacon_Book_Disjunction_Step_Transport
    Bacon_Book_Disjunction_Conversion_Transport
    Bacon_Book_Disjunction_Background_Decoding
    Bacon_Book_Disjunction_Proof_Encoding
    Bacon_Book_Disjunction_Proof_Decoding
    Bacon_Book_Disjunction_Proof_Correspondence
    Bacon_Book_Primitive_Disjunction_Model
    Bacon_Book_Disjunction_Raw_Conversion_Transport

session Bacon_Book_Lambda_I_Development in "theories/base/book_lambda_I" = Bacon_Book_Environment_Development +
  description "
    Bacon's relevant (λI) language as an instance of Definition 9.1, the
    independently defined λI theory calculus with both Gen presentations,
    internal βη/α conversion with derivability transport, λI models under
    the internal conversion clause with soundness, λI retraction and
    signature conservativity, Henkin witness stages over closed λI
    predicates, the term model on internal conversion classes of closed λI
    terms, and original-signature model existence and global strong
    completeness for the internal-clause model class, under the minimal
    logical basis, a rich variable stock for the main endpoints, and an
    actual typed assignment required of every model. Still open and
    separate: identification with HJ (Definitions 9.9–9.10), conservativity
    of full H over the fragment, the λI printed/exact β correspondence, and
    internalization of raw βη-conversion (completeness for the raw-invariant
    subclass).
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_Book_Lambda_I_Syntax
    Bacon_Book_Lambda_I_Calculus
    Bacon_Book_Lambda_I_Conversion
    Bacon_Book_Lambda_I_Presentations
    Bacon_Book_Lambda_I_Models
    Bacon_Book_Lambda_I_Henkin_Name_Stages
    Bacon_Book_Lambda_I_Henkin_Full_Signature
    Bacon_Book_Lambda_I_Theory_Retraction
    Bacon_Book_Lambda_I_Theory_Variable_Substitution
    Bacon_Book_Lambda_I_Fresh_Constant_Generalization
    Bacon_Book_Lambda_I_Existential_Conversion
    Bacon_Book_Lambda_I_Negation_Conversion
    Bacon_Book_Lambda_I_Open_Propositional_Decision
    Bacon_Book_Lambda_I_Negative_Predicate_Generalization
    Bacon_Book_Lambda_I_Propositional_Certificates
    Bacon_Book_Lambda_I_Propositional_Negation
    Bacon_Book_Lambda_I_Propositional_Explosion
    Bacon_Book_Lambda_I_Conjunction_Certificates
    Bacon_Book_Lambda_I_Conjunction_Currying
    Bacon_Book_Lambda_I_Closed_Deduction
    Bacon_Book_Lambda_I_Finite_Support
    Bacon_Book_Lambda_I_Theory_Closure
    Bacon_Book_Lambda_I_Universal_Closure
    Bacon_Book_Lambda_I_Theory_Consistency
    Bacon_Book_Lambda_I_Theory_Signature_Monotonicity
    Bacon_Book_Lambda_I_Theory_Signature_Conservativity
    Bacon_Book_Lambda_I_Closed_Witness_Choice
    Bacon_Book_Lambda_I_Consistency_Unions
    Bacon_Book_Lambda_I_Closed_Maximal_Extension
    Bacon_Book_Lambda_I_Closed_Negation_Complete
    Bacon_Book_Lambda_I_Conditional_Witness
    Bacon_Book_Lambda_I_Witness_Family_Syntax
    Bacon_Book_Lambda_I_Henkin_Stage_Witnesses
    Bacon_Book_Lambda_I_Finite_Witness_Family
    Bacon_Book_Lambda_I_Finite_Image_Cover
    Bacon_Book_Lambda_I_Infinite_Witness_Family
    Bacon_Book_Lambda_I_Henkin_Stage_Consistency
    Bacon_Book_Lambda_I_Theory_Constant_Renaming
    Bacon_Book_Lambda_I_Constant_Renaming_Reflection
    Bacon_Book_Lambda_I_Henkin_Premise_Stages
    Bacon_Book_Lambda_I_Henkin_Witness_Coverage
    Bacon_Book_Lambda_I_Henkin_Union
    Bacon_Book_Lambda_I_Universal_Closure_Theories
    Bacon_Book_Lambda_I_Universal_Closure_Consistency
    Bacon_Book_Lambda_I_Closed_Witness_Completeness
    Bacon_Book_Lambda_I_Closed_Henkin_Extension
    Bacon_Book_Lambda_I_Conversion_Classes
    Bacon_Book_Lambda_I_Conversion_Application
    Bacon_Book_Lambda_I_Conversion_Denotation
    Bacon_Book_Lambda_I_Henkin_Closed_Terms
    Bacon_Book_Lambda_I_Conversion_Domain_Inhabitation
    Bacon_Book_Lambda_I_Closed_Maximal_Truth
    Bacon_Book_Lambda_I_Conversion_Valuation
    Bacon_Book_Lambda_I_Conversion_Logical_Values
    Bacon_Book_Lambda_I_Environment_Substitution_Conversion
    Bacon_Book_Lambda_I_Conversion_Environment
    Bacon_Book_Lambda_I_Conversion_Closed_Values
    Bacon_Book_Lambda_I_Closed_Universal_Instances
    Bacon_Book_Lambda_I_Quantifier_Proof_Basics
    Bacon_Book_Lambda_I_Closed_Quantifier_Duality
    Bacon_Book_Lambda_I_Closed_Universal_Truth
    Bacon_Book_Lambda_I_Conversion_Universal_Valuation
    Bacon_Book_Lambda_I_Conversion_Model
    Bacon_Book_Lambda_I_Conversion_Truth_Projection
    Bacon_Book_Lambda_I_Universal_Closure_Truth
    Bacon_Book_Lambda_I_Conversion_Expanded_Model_Existence
    Bacon_Book_Lambda_I_Constant_Renaming_Conversion
    Bacon_Book_Lambda_I_Constant_Model_Pullback
    Bacon_Book_Lambda_I_Canonical_Model_Existence
    Bacon_Book_Lambda_I_Canonical_Countermodel
    Bacon_Book_Lambda_I_Canonical_Completeness
    Bacon_Book_Lambda_I_Audit

session Bacon_Source_Model_Development in "theories/base/source_models" = Bacon_Source_Vocabulary_Development +
  description "
    Models for the independently defined first-class paper language,
    with the proved named-variable representation bridges
    (Bacon_Source_Named_Tagged_Model, Bacon_Source_Named_Reverse_Model).
  "
  options [timeout = 60, export_theory = true]
  sessions
    Bacon_Parametric_Canonical_Development
    Bacon_Parametric_Countable_Development
  theories
    Bacon_Source_BBK_Model_Existence
    Bacon_Source_BBK_Countermodels
    Bacon_Source_BBK_Closed_Soundness
    Bacon_Source_BBK_Strong_Completeness
    Bacon_Source_BBK_Global_Soundness
    Bacon_Source_Named_Completion_Denotation
    Bacon_Source_Named_BBK_Interface
    Bacon_Source_Named_Conversion_Denotation
    Bacon_Source_Named_Denotation_Basics
    Bacon_Source_Named_Type_Tags
    Bacon_Source_Named_Tagged_Application
    Bacon_Source_Named_Denotation_Quantifiers
    Bacon_Source_Named_Tagged_Quantifiers
    Bacon_Source_Named_Tagged_Model
    Bacon_Source_Named_Forward_Validity
    Bacon_Source_Named_Model_Existence
    Bacon_Source_Named_Closed_Countermodel
    Bacon_Source_Named_Closed_Strong_Completeness
    Bacon_Source_Chart_Assignments
    Bacon_Source_Chart_Denotation
    Bacon_Source_Chart_Independence
    Bacon_Source_Chart_Cross_Context
    Bacon_Source_Chart_Prefix_Denotation
    Bacon_Source_Chart_Truth_Basics
    Bacon_Source_Framed_Denotation
    Bacon_Source_Framed_Application
    Bacon_Source_Framed_Truth
    Bacon_Source_Tagged_Frames
    Bacon_Source_Erased_Denotation
    Bacon_Source_Erased_Structure
    Bacon_Source_Erased_Truth
    Bacon_Source_Named_Reverse_Model
    Bacon_Source_Named_Reverse_Closed_Truth
    Bacon_Source_Named_Reverse_Open_Truth
    Bacon_Source_Named_Reverse_Completion_Truth
    Bacon_Source_Named_Reverse_Open_Validity
    Bacon_Source_Named_Encoded_H_Soundness
    Bacon_Source_Named_Encoded_Local_Soundness
    Bacon_Source_Named_H_Soundness
    Bacon_Source_Chart_Truth_Quantifiers
    Bacon_Source_Named_Model_Vector_Denotation
    Bacon_Source_Named_Model_Type_Tagging_Model
    Bacon_Source_Named_Recoding_Structure
    Bacon_Source_Named_Recoding_Validity
    Bacon_Source_Named_Nat_Coding
    Bacon_Source_Named_Countable_Model_Existence
    Bacon_Source_Named_Nat_Strong_Completeness

session Bacon_Parametric_Signature_Development in "theories/base/parametric_signature" = Bacon_Base +
  description "
    Arbitrary-cardinality signatures, H soundness, local consequence,
    Henkinization, and semantic name transport.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_Parametric_H_Soundness
    Bacon_Parametric_Set_Soundness
    Bacon_Parametric_Refutation_Consistency
    Bacon_Parametric_String_Bridge
    Bacon_Parametric_Henkin_Names
    Bacon_Parametric_Fresh_Constant
    Bacon_Parametric_Existential_Witness_Theorem
    Bacon_Parametric_Local_Quantifiers
    Bacon_Parametric_Lindenbaum
    Bacon_Parametric_Henkin_Existence
    Bacon_Parametric_BBK_Name_Transport

session Bacon_Parametric_Canonical_Development in "theories/base/parametric_canonical" = Bacon_Parametric_Signature_Development +
  description "
    Exact canonical BBK models, model existence, countermodels, and strong
    completeness for H over arbitrary signatures.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_Parametric_Henkin_Bridge
    Bacon_Parametric_BBK_Strong_Completeness
    Bacon_Parametric_Raw_Strong_Completeness

session Bacon_Parametric_Countable_Development in "theories/base/parametric_countable" = Bacon_Parametric_Canonical_Development +
  description "
    Countable-signature coding and natural-number-domain transport for the
    exact arbitrary-signature BBK construction.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_Parametric_Countable_Model_Existence
    Bacon_Parametric_Declared_Signature_Model_Existence
    Bacon_Parametric_Countable_Raw_Model_Existence

session Bacon_Book_Classicism_Development in "theories/classicism/book" = Bacon_Book_Environment_Development +
  description "Native full-F minimal-basis Classicism for the book canonical completeness construction."
  options [timeout = 60, export_theory = true]
  sessions "HOL-Cardinals"
  theories
    Bacon_Book_Classicism_Syntax
    Bacon_Book_Classicism_Derivation
    Bacon_Book_Classicism_Least_Theory
    Bacon_Book_Classicism_Theory_Consistency
    Bacon_Book_Classicism_Closed_Refutation
    Bacon_Book_Classicism_Propositional_Equivalence
    Bacon_Book_Classicism_Audit
    Bacon_Book_Box_Truth
    Bacon_Book_H_Modal_Certificates
    Bacon_Book_Classicism_Necessitation
    Bacon_Book_Implication_Leibniz_Congruence
    Bacon_Book_Normal_K_Truth
    Bacon_Book_H_Normal_K_Certificate
    Bacon_Book_Classicism_Normal_K
    Bacon_Book_Classicism_Modal_T
    Bacon_Book_Classicism_Theory_Rules
    Bacon_Book_Classicism_Closed_Lists
    Bacon_Book_Classicism_Boxed_Lists
    Bacon_Book_Classicism_Boxed_Consequence
    Bacon_Book_Classicism_Closed_Fragment
    Bacon_Book_Classicism_Closed_Maximal
    Bacon_Book_Classicism_Closed_Successor
    Bacon_Book_Modal_Four_Truth
    Bacon_Book_Classicism_Modal_Four
    Bacon_Book_Classicism_Closed_Accessibility
    Bacon_Book_Classicism_Retraction_Syntax
    Bacon_Book_Classicism_Retraction
    Bacon_Book_Classicism_Signature_Conservativity
    Bacon_Book_Classicism_Theory_Retraction
    Bacon_Book_Classicism_Fresh_Background
    Bacon_Book_Classicism_Conditional_Witness
    Bacon_Book_Classicism_Finite_Witness_Family
    Bacon_Book_Classicism_Infinite_Witness_Family
    Bacon_Book_Classicism_Constant_Renaming
    Bacon_Book_Classicism_Theory_Renaming
    Bacon_Book_Classicism_Henkin_Stages
    Bacon_Book_Classicism_Henkin_Union
    Bacon_Book_Classicism_Universal_Closure
    Bacon_Book_Classicism_Henkin_Extension
    Bacon_Book_Classicism_Henkin_Reserve
    Bacon_Book_Typed_Name_Map
    Bacon_Book_Typed_Name_Conversion
    Bacon_Book_H_Typed_Name_Map
    Bacon_Book_C_Typed_Name_Map
    Bacon_Book_C_Theory_Typed_Name_Map
    Bacon_Book_Typed_Name_Inverse
    Bacon_Book_Name_Countability
    Bacon_Book_Named_Syntax_Cardinal
    Bacon_Book_Ambient_Signature
    Bacon_Book_Ambient_Name_Embedding
    Bacon_Book_Typed_Witness_Transport
    Bacon_Book_Henkin_Image_Premises
    Bacon_Book_Henkin_Image_Extension
    Bacon_Book_Ambient_Henkin_Extension
    Bacon_Book_Ambient_Henkin_Successor
    Bacon_Book_Countable_Signature_Recoding
    Bacon_Book_Canonical_Language_Inclusion
    Bacon_Book_Canonical_Worlds
    Bacon_Book_Canonical_World_Existence
    Bacon_Book_Canonical_Successor
    Bacon_Book_Canonical_Frame
    Bacon_Book_Identity_Stability_Truth
    Bacon_Book_Classicism_Identity_Stability
    Bacon_Book_Canonical_Identity_Persistence
    Bacon_Book_H_Identity_Certificates
    Bacon_Book_Identity_World_Algebra
    Bacon_Book_Modal_Term_Classes
    Bacon_Book_Modal_Term_Application
    Bacon_Book_Modal_Term_Transport
    Bacon_Book_Modal_Term_Action
    Bacon_Book_Boxed_PE_Identities
    Bacon_Book_Boxed_PE_Truth
    Bacon_Book_Classicism_Boxed_PE
    Bacon_Book_Canonical_Biconditional
    Bacon_Book_Proposition_Identity_Membership
    Bacon_Book_Proposition_Profiles
    Bacon_Book_Proposition_Representation
    Bacon_Book_Modal_Term_Inhabitation
    Bacon_Book_Full_Modalized_Functionality
    Bacon_Book_Full_Classicism_Calculus
    Bacon_Book_Full_Classicism_Least_Theory
    Bacon_Book_Full_Classicism_Necessitation
    Bacon_Book_Full_Classicism_Structural
    Bacon_Book_Full_Classicism_Name_Map
    Bacon_Book_Full_Classicism_Theory_Consistency
    Bacon_Book_Full_Classicism_Theory_Name_Map
    Bacon_Book_Full_Classicism_Name_Inverse
    Bacon_Book_Full_Classicism_Audit
    Bacon_Book_MF_Term_Syntax
    Bacon_Book_Full_MF_Closed_Instances
    Bacon_Book_MF_Free_For
    Bacon_Book_Full_MF_Fresh_Instances
    Bacon_Book_MF_Binder_Conversion
    Bacon_Book_MF_Argument_Renaming
    Bacon_Book_Full_MF_Instances
    Bacon_Book_Full_Vector_Equivalence
    Bacon_Book_Full_Equivalence_Presentation
    Bacon_Book_Full_Classicism_Base_Bridge
    Bacon_Book_Full_Classicism_Retraction
    Bacon_Book_Full_Classicism_Signature_Conservativity
    Bacon_Book_Full_Classicism_Theory_Retraction
    Bacon_Book_Full_Classicism_Fresh_Background
    Bacon_Book_Full_Classicism_Conditional_Witness
    Bacon_Book_Full_Classicism_Uniform_Name_Map
    Bacon_Book_Full_Classicism_Finite_Witness_Family
    Bacon_Book_Full_Classicism_Infinite_Witness_Family
    Bacon_Book_Full_Classicism_Henkin_Stages
    Bacon_Book_Full_Classicism_Henkin_Union
    Bacon_Book_Full_Classicism_Theory_Rules
    Bacon_Book_Full_Classicism_Universal_Closure
    Bacon_Book_Full_Classicism_Closed_Fragment
    Bacon_Book_Full_Classicism_Closed_Maximal
    Bacon_Book_Full_Classicism_Henkin_Extension
    Bacon_Book_Full_Henkin_Image_Extension
    Bacon_Book_Full_Ambient_Henkin_Extension
    Bacon_Book_Full_Classicism_Modal_Transfer
    Bacon_Book_Full_Classicism_Closed_Refutation
    Bacon_Book_Full_Classicism_Closed_Lists
    Bacon_Book_Full_Classicism_Boxed_Lists
    Bacon_Book_Full_Classicism_Boxed_Consequence
    Bacon_Book_Full_Classicism_Closed_Successor
    Bacon_Book_Full_Ambient_Henkin_Successor
    Bacon_Book_Full_Canonical_Worlds
    Bacon_Book_Full_Countable_Signature_Recoding
    Bacon_Book_Full_Canonical_World_Existence
    Bacon_Book_Full_Canonical_Successor
    Bacon_Book_Full_Canonical_Frame
    Bacon_Book_Full_Term_World_Bridge
    Bacon_Book_Full_Proposition_Profiles
    Bacon_Book_Full_Proposition_Representation
    Bacon_Book_Function_Identity_Predicate
    Bacon_Book_Full_Term_Quasi_Functionality

session Bacon_Book_Modal_Representation in "theories/classicism/book/representation" = Bacon_Book_Classicism_Development +
  description "Source-faithful Chapter 18 representations of the full-C modal term structure."
  options [timeout = 60, export_theory = true]
  sessions Bacon_Classicism_Action_Development
  theories
    Bacon_Book_Full_Term_Modalized_Sets
    Bacon_Book_Full_Term_Application_Map
    Bacon_Book_Modalized_Bijection
    Bacon_Book_Function_Representation
    Bacon_Book_Function_Representation_Natural
    Bacon_Book_Function_Representation_Inverse
    Bacon_Book_Function_Representation_Transport
    Bacon_Book_Full_Individual_Functions
    Bacon_Book_Full_Proposition_Modalized
    Bacon_Book_Full_Function_Step
    Bacon_Book_Function_Representation_Characterization
    Bacon_Book_Modal_Representation_Audit
    Bacon_Book_Identity_Conversion
    Bacon_Book_Term_Denotation
    Bacon_Book_Term_Environment
    Bacon_Book_Representative_Substitution
    Bacon_Book_Representative_One_Change
    Bacon_Book_Representative_Independence
    Bacon_Book_Term_Interpretation_Naturality
    Bacon_Book_Term_Interpretation_Audit
    Bacon_Book_Term_Valuation
    Bacon_Book_Term_Logical_Clauses
    Bacon_Book_Term_General_Model
    Bacon_Book_Term_Logical_Audit
    Bacon_Book_Term_Actual_Identity
    Bacon_Book_Term_Identity_Audit
    Bacon_Book_Canonical_Combinator_Syntax
    Bacon_Book_Combinator_Syntax_Audit

session Bacon_Book_ZF_Modal_Semantics in "theories/classicism/book/modal_semantics/hol_zf" = "HOL-ZF" +
  description "Independent set-theoretic modal-model definition for Bacon's full-type Classicism."
  options [timeout = 60, export_theory = true]
  sessions Bacon_Classicism_ZF_Representation Bacon_Classicism_Action_Development Bacon_Source_Vocabulary_Development
  theories
    Bacon_Book_ZF_Model_Data
    Bacon_Book_ZF_Model_Graph_Regression
    Bacon_Book_ZF_Model_Operations
    Bacon_Book_ZF_Modal_Structure
    Bacon_Book_ZF_Model_Function_Extensionality
    Bacon_Book_ZF_Model_Curried_Graphs
    Bacon_Book_ZF_Modal_Model
    Bacon_Book_ZF_Model_Operator_Restriction
    Bacon_Book_ZF_Model_Definition_Audit
    Bacon_Book_ZF_Nontrivial_Model

session Bacon_Book_ZF_Modal_Interpretation in "theories/classicism/book/modal_semantics/interpretation" = Bacon_Book_ZF_Modal_Semantics +
  description "Independent typed interpretation clauses and semantic proofs for Bacon's modal models."
  options [timeout = 60, export_theory = true]
  sessions Bacon_Book_Environment_Development Bacon_Book_Classicism_Development
  theories
    Bacon_Book_ZF_Model_Assignments
    Bacon_Book_ZF_Generic_Combinators
    Bacon_Book_Combinatory_Translation
    Bacon_Book_ZF_Combinatory_Evaluation
    Bacon_Book_ZF_Generic_Abstraction
    Bacon_Book_ZF_Interpretation_Clauses
    Bacon_Book_ZF_Model_Interpretation_Uniqueness
    Bacon_Book_ZF_Generic_Interpretation_Existence
    Bacon_Book_ZF_Interpretation_Existence_Audit
    Bacon_Book_ZF_Model_Truth
    Bacon_Book_ZF_Signature_Pullback
    Bacon_Book_ZF_Generic_Interpretation_Audit
    Bacon_Book_ZF_Nontrivial_Interpretation

session Bacon_Book_ZF_Model_Regressions in "theories/classicism/book/modal_semantics/regressions" = Bacon_Book_ZF_Modal_Interpretation +
  description "Checked semantic regressions distinguishing structural and nontrivial book modal models."
  options [timeout = 60, export_theory = true]
  sessions Bacon_Book_Classicism_Development
  theories
    Bacon_Book_ZF_Singleton_Regression

session Bacon_Book_ZF_Modal_Soundness in "theories/classicism/book/modal_semantics/soundness" = Bacon_Book_ZF_Modal_Interpretation +
  description "Generic soundness of full-type Classicism for the independent book modal models, and the completeness assembly."
  options [timeout = 60, export_theory = true]
  sessions Bacon_Book_Environment_Development Bacon_Book_Classicism_Development Bacon_Book_ZF_Modal_Representation
  theories
    Bacon_Book_ZF_Modal_Naturality
    Bacon_Book_ZF_Modal_Truth_Clauses
    Bacon_Book_ZF_Modal_Identity_Clauses
    Bacon_Book_ZF_Modal_Conversion
    Bacon_Book_ZF_Modal_H_Soundness
    Bacon_Book_ZF_Full_C_Soundness
    Bacon_Book_ZF_Full_C_Completeness
    Bacon_Book_ZF_Full_C_Small_Carrier_Completeness
    Bacon_Book_ZF_Full_C_Declared_Names_Completeness
    Bacon_Book_ZF_Modal_Soundness_Audit

session Bacon_Book_ZF_Modal_Representation in "theories/classicism/book/representation/hol_zf" = Bacon_Book_Modal_Representation +
  description "Explicit HOL-ZF universe assembly for the source-faithful full-C canonical modal model."
  options [timeout = 60, export_theory = true]
  sessions Bacon_Classicism_ZF_Representation "HOL-ZF" Bacon_Book_ZF_Modal_Semantics Bacon_Book_ZF_Modal_Interpretation
  theories
    Bacon_Book_ZF_Countable_Codes
    Bacon_Book_ZF_Coded_Frame
    Bacon_Book_ZF_World_Codes
    Bacon_Book_ZF_Term_Class_Codes
    Bacon_Book_ZF_Represented_Images
    Bacon_Book_ZF_Future_Pairs
    Bacon_Book_ZF_Type_Recursion
    Bacon_Book_ZF_Recursion_Base
    Bacon_Book_ZF_Arrow_Values
    Bacon_Book_ZF_All_Type_Inverses
    Bacon_Book_ZF_Modalized_Family
    Bacon_Book_ZF_Arrow_Restriction
    Bacon_Book_ZF_Proposition_Restriction
    Bacon_Book_ZF_Arrow_Homomorphisms
    Bacon_Book_ZF_Representation_Audit
    Bacon_Book_ZF_Interpretation_Assignments
    Bacon_Book_ZF_Term_Interpretation
    Bacon_Book_ZF_Interpretation_Naturality
    Bacon_Book_ZF_Future_Abstraction
    Bacon_Book_ZF_Interpretation_Audit
    Bacon_Book_ZF_Characteristic_Truth
    Bacon_Book_ZF_Logical_Values
    Bacon_Book_ZF_Primitive_Truth
    Bacon_Book_ZF_General_Model
    Bacon_Book_ZF_Logical_Audit
    Bacon_Book_ZF_Actual_Identity
    Bacon_Book_ZF_Future_Truth_Sets
    Bacon_Book_ZF_Closed_Values
    Bacon_Book_ZF_Application_Naturality
    Bacon_Book_ZF_Equality_Value
    Bacon_Book_ZF_Equality_Future_Value
    Bacon_Book_ZF_Identity_Audit
    Bacon_Book_ZF_Logical_Future_Results
    Bacon_Book_ZF_Logical_Future_Values
    Bacon_Book_ZF_Implication_Future_Set
    Bacon_Book_ZF_K_Value
    Bacon_Book_ZF_S_Body
    Bacon_Book_ZF_S_Future_Value
    Bacon_Book_ZF_Operators_Audit
    Bacon_Book_ZF_Reindexed_Frame
    Bacon_Book_ZF_Reindexed_Functions
    Bacon_Book_ZF_Reindexed_Structure
    Bacon_Book_ZF_Reindexed_Structure_Audit
    Bacon_Book_ZF_Reindexed_Collect
    Bacon_Book_ZF_Reindexed_Combinators
    Bacon_Book_ZF_Reindexed_Logical_Operators
    Bacon_Book_ZF_Reindexed_Identity_Operator
    Bacon_Book_ZF_Root_Constants
    Bacon_Book_ZF_Canonical_Modal_Model
    Bacon_Book_ZF_Canonical_Model_Audit
    Bacon_Book_ZF_Canonical_Evaluation
    Bacon_Book_ZF_Canonical_Interpretation
    Bacon_Book_ZF_Original_Theory_Truth
    Bacon_Book_ZF_Ambient_Model_Existence
    Bacon_Book_ZF_Ambient_Existence_Audit
    Bacon_Book_ZF_Countable_Model_Existence
    Bacon_Book_ZF_Model_Existence_Audit
    Bacon_Book_ZF_Canonical_Nontrivial_Model
    Bacon_Book_ZF_Ambient_Nontrivial_Existence
    Bacon_Book_ZF_Countable_Nontrivial_Existence
    Bacon_Book_ZF_Nontrivial_Audit
    Bacon_Book_ZF_Small_Carrier_Existence
    Bacon_Book_ZF_Small_Carrier_Audit
    Bacon_Book_ZF_Declared_Names_Existence
    Bacon_Book_ZF_Declared_Names_Audit

session Bacon_Classicism_Action_Development in "theories/classicism/action_models" = Bacon_Source_Model_Development +
  description "
    Exact Bacon-Dorr homomorphisms, categories and actions over the independent
    named BBK interface. No book primitive-extension prerequisite.
  "
  options [timeout = 60, export_theory = true]
  sessions "HOL-Cardinals"
  theories
    Bacon_Source_Homomorphism_Assignments
    Bacon_Source_BBK_Homomorphism
    Bacon_Source_BBK_Model_Morphism
    Bacon_Source_Category
    Bacon_Source_Action
    Bacon_Source_Powerset_Action
    Bacon_Source_Typed_Map_Normalization
    Bacon_Source_Subcategory
    Bacon_Source_BBK_Model_Data
    Bacon_Source_Typed_Arrows
    Bacon_Source_Typed_Map_Category
    Bacon_Source_BBK_Arrows
    Bacon_Source_BBK_Model_Normalization
    Bacon_Source_BBK_Category
    Bacon_Source_BBK_Normalization_Inputs
    Bacon_Source_BBK_Normalization_Validity
    Bacon_Source_BBK_Truth_Profile
    Bacon_Source_BBK_Normalized_Category
    Bacon_Source_BBK_Subcategory
    Bacon_Source_BBK_Selected_Truth_Profile
    Bacon_Source_BBK_Application
    Bacon_Source_BBK_Category_Interface
    Bacon_Source_BBK_Application_Morphism
    Bacon_Source_Exponential_Domain
    Bacon_Source_Exponential_Transport
    Bacon_Source_Exponential_Action
    Bacon_Source_Subaction
    Bacon_Source_Image_Action
    Bacon_Source_Relational_Types
    Bacon_Source_BBK_Application_Profile
    Bacon_Source_BBK_Application_Profile_Action
    Bacon_Source_BBK_Profile_Subactions
    Bacon_Source_Image_Action_Inverse
    Bacon_Source_Relational_Syntax
    Bacon_Source_BBK_Vector_Application
    Bacon_Source_Relational_Conversion
    Bacon_Source_Relational_Signature_Conversion
    Bacon_Source_Relational_Signature_Conservativity
    Bacon_Source_Relational_BBK_Interface
    Bacon_Source_Relational_Model_Restriction
    Bacon_Source_Relational_Homomorphism
    Bacon_Source_Relational_Model_Morphism
    Bacon_Source_Relational_Application_Graph
    Bacon_Source_Relational_Application
    Bacon_Source_Relational_Model_Data
    Bacon_Source_Relational_Arrows
    Bacon_Source_Relational_Category
    Bacon_Source_Relational_Model_Normalization
    Bacon_Source_Relational_Normalization_Inputs
    Bacon_Source_Relational_Normalization_Validity
    Bacon_Source_Relational_Application_Morphism
    Bacon_Source_Relational_Vector_Syntax
    Bacon_Source_Relational_Vector_Application
    Bacon_Source_Relational_Subcategory
    Bacon_Source_Relational_Category_Interface
    Bacon_Source_Relational_Truth_Profile
    Bacon_Source_Relational_Intension
    Bacon_Source_Relational_Application_Profile
    Bacon_Source_Relational_Application_Profile_Action
    Bacon_Source_Relational_Negation_Profile
    Bacon_Source_Relational_Quantifier_Profile
    Bacon_Source_Relational_Binary_Logical_Application
    Bacon_Source_Relational_Boolean_Profiles
    Bacon_Source_Relational_Identity_Profile
    Bacon_Source_Relational_Profile_Subactions
    Bacon_Source_Relational_Intension_Tail
    Bacon_Source_Relational_Intensional_Forward
    Bacon_Source_Relational_Intensional_Reverse
    Bacon_Source_Relational_Quasi_Fregean_Denotation
    Bacon_Source_Relational_Common_Theory
    Bacon_Source_Relational_Quasi_Functional_Denotation
    Bacon_Source_Relational_Logical_Language
    Bacon_Source_Relational_H
    Bacon_Source_Relational_H_Embedding
    Bacon_Source_Relational_Common_Functionality
    Bacon_Source_Relational_Binary_Lambda_Conversion
    Bacon_Source_Relational_Binary_Lambda_Denotation
    Bacon_Source_Relational_Logical_Truth
    Bacon_Source_Relational_Binder_Truth
    Bacon_Source_Relational_Assignment_Extension
    Bacon_Source_Relational_Assignment_Denotation
    Bacon_Source_Relational_Common_Propositional_Equivalence
    Bacon_Source_Relational_Conversion_Truth
    Bacon_Source_Relational_Local_Consequence
    Bacon_Source_Relational_Deduction
    Bacon_Source_Relational_Explosion
    Bacon_Source_Relational_Consistency
    Bacon_Source_Relational_Consequence_Closure
    Bacon_Source_Relational_Closed_Theory
    Bacon_Source_Relational_Lindenbaum
    Bacon_Source_Relational_Maximal_Theory
    Bacon_Source_Relational_Existence
    Bacon_Source_Relational_Retraction_Syntax
    Bacon_Source_Relational_H_Retraction_Support
    Bacon_Source_Relational_H_Retraction
    Bacon_Source_Relational_H_Signature_Conservativity
    Bacon_Source_Relational_Constant_Map
    Bacon_Source_Relational_Constant_Map_Binding
    Bacon_Source_Relational_Constant_Map_Logical
    Bacon_Source_Relational_H_Constant_Map
    Bacon_Source_Relational_Local_Constant_Map
    Bacon_Source_Relational_Constant_Map_Consistency
    Bacon_Source_Relational_Local_Retraction
    Bacon_Source_Relational_Local_Signature_Conservativity
    Bacon_Source_Relational_Identity_Proof_Basics
    Bacon_Source_Relational_Identity_Derivations
    Bacon_Source_Relational_Application_Identity_Tests
    Bacon_Source_Relational_Application_Congruence
    Bacon_Source_Relational_Local_Exchange
    Bacon_Source_Relational_Local_Inst
    Bacon_Source_Relational_Witness_Syntax
    Bacon_Source_Relational_Witness_Propositional
    Bacon_Source_Relational_Witness_Eta
    Bacon_Source_Relational_Witness_Consistency
    Bacon_Source_Relational_Witness_Family_Syntax
    Bacon_Source_Relational_Finite_Witness_Family
    Bacon_Source_Relational_Witness_Family_Consistency
    Bacon_Source_Relational_Henkin_Name_Stages
    Bacon_Source_Relational_Henkin_Stage_Signature
    Bacon_Source_Relational_Henkin_Premise_Stages
    Bacon_Source_Relational_Henkin_Stage_Consistency
    Bacon_Source_Relational_Henkin_Full_Signature
    Bacon_Source_Relational_Henkin_Full_Premises
    Bacon_Source_Relational_Henkin_Union_Consistency
    Bacon_Source_Relational_Henkin_Witness_Coverage
    Bacon_Source_Relational_Closed_Witness_Completeness
    Bacon_Source_Relational_Closed_Henkin_Theory
    Bacon_Source_Relational_Closed_Henkin_Extension
    Bacon_Source_Relational_Henkin_Domain_Inhabitation
    Bacon_Source_Relational_Identity_Representatives
    Bacon_Source_Relational_Identity_Application
    Bacon_Source_Relational_Conversion_Identity_Steps
    Bacon_Source_Relational_Conversion_Identity
    Bacon_Source_Relational_Term_Type
    Bacon_Source_Relational_Representative_Assignments
    Bacon_Source_Relational_Environment_Substitution
    Bacon_Source_Relational_Environment_Substitution_Typing
    Bacon_Source_Relational_Propositional_Identity_Derivations
    Bacon_Source_Relational_Identity_Valuation
    Bacon_Source_Relational_Identity_Interpretation
    Bacon_Source_Relational_Identity_Application_Congruence
    Bacon_Source_Relational_Boolean_PC
    Bacon_Source_Relational_Henkin_Boolean_Membership
    Bacon_Source_Relational_Identity_Boolean_Valuation
    Bacon_Source_Relational_Identity_Propositional_Truth
    Bacon_Source_Relational_Identity_Identity_Truth
    Bacon_Source_Relational_Environment_Beta_Syntax
    Bacon_Source_Relational_Environment_Contractions
    Bacon_Source_Relational_Environment_Conversion
    Bacon_Source_Relational_Identity_Conversion
    Bacon_Source_Relational_Quantifier_PC
    Bacon_Source_Relational_Quantifier_Duality
    Bacon_Source_Relational_Henkin_Existential_Membership
    Bacon_Source_Relational_Henkin_Universal_Membership
    Bacon_Source_Relational_Identity_Quantifier_Valuation
    Bacon_Source_Relational_Identity_Fresh_Application
    Bacon_Source_Relational_Identity_Quantifier_Truth
    Bacon_Source_Relational_Identity_Model
    Bacon_Source_Relational_BBK_Constant_Pullback
    Bacon_Source_Relational_Model_Existence
    Bacon_Source_Relational_Admitted_Terms_Countable
    Bacon_Source_Relational_Finite_Syntax_Code
    Bacon_Source_Relational_Admitted_Syntax_Cardinal
    Bacon_Source_Relational_Henkin_Cardinal_Signature
    Bacon_Source_Relational_Identity_Cardinal_Domains
    Bacon_Source_Relational_Bounded_Model_Existence
    Bacon_Source_Relational_Naming_Syntax
    Bacon_Source_Relational_Naming_Charts
    Bacon_Source_Relational_Naming_Replacement
    Bacon_Source_Relational_Naming_Assignments
    Bacon_Source_Relational_Naming_Coordinate_Syntax
    Bacon_Source_Relational_Naming_Coordinate_Assignments
    Bacon_Source_Relational_Naming_Coordinate_Denotation
    Bacon_Source_Relational_Naming_Chart_Mixing
    Bacon_Source_Relational_Naming_Chart_Independence
    Bacon_Source_Relational_Naming_Larger_Support
    Bacon_Source_Relational_Naming_Chosen_Chart
    Bacon_Source_Relational_Naming_Interpretation
    Bacon_Source_Relational_Naming_Finite_Family
    Bacon_Source_Relational_Naming_Structure
    Bacon_Source_Relational_Naming_Logical_Chart
    Bacon_Source_Relational_Naming_Boolean_Truth
    Bacon_Source_Relational_Naming_Quantifier_Chart
    Bacon_Source_Relational_Naming_Quantifier_Truth
    Bacon_Source_Relational_Substitution_Syntax
    Bacon_Source_Relational_Substitution_Denotation
    Bacon_Source_Relational_Henkin_Countable_Signature
    Bacon_Source_Relational_Identity_Countable_Domains
    Bacon_Source_Relational_Countable_Model_Existence
    Bacon_Source_Relational_Recoding_Assignments
    Bacon_Source_Relational_Recoding_Denotation
    Bacon_Source_Relational_Recoding_Structure
    Bacon_Source_Relational_Recoding_Truth
    Bacon_Source_Relational_Recoding_Quantifiers
    Bacon_Source_Relational_Recoding_Model
    Bacon_Source_Relational_Recoding_Validity
    Bacon_Source_Relational_Nat_Model_Existence
    Bacon_Source_Relational_Nat_Countermodel
    Bacon_Source_Relational_Nat_Completeness
    Bacon_Source_Relational_Vector_Proof_Syntax
    Bacon_Source_Relational_Conversion_Congruence
    Bacon_Source_Relational_Vector_Identity_Recovery
    Bacon_Source_Relational_Closed_LE_Generators
    Bacon_Source_Relational_Classicism_A2_H
    Bacon_Source_Relational_Closed_Identity_Vector
    Bacon_Source_Relational_Classicism_A2_Closed_Identity
    Bacon_Source_Relational_A2_MP_Environment_Syntax
    Bacon_Source_Relational_A2_MP_Closed_Updates
    Bacon_Source_Relational_A2_MP_Beta
    Bacon_Source_Relational_Classicism_A2_MP_Closed
    Bacon_Source_Relational_Classicism_A2_MP
    Bacon_Source_Relational_Classicism_A2_Local
    Bacon_Source_Relational_Classicism_A2_LE
    Bacon_Source_Relational_Universal_Proof_Basics
    Bacon_Source_Relational_Distribution_PC
    Bacon_Source_Relational_Forall_Disjunction_Proof
    Bacon_Source_Relational_Existential_Proof_Basics
    Bacon_Source_Relational_Existential_Duality_Proof
    Bacon_Source_Relational_Inst_Gen_Certificate
    Bacon_Source_Relational_Classicism_Identity_Consequences
    Bacon_Source_Relational_Universal_Biconditionals
    Bacon_Source_Relational_Gen_Distribution_Proof
    Bacon_Source_Relational_Gen_Closed_Context
    Bacon_Source_Relational_Gen_Vector_Beta
    Bacon_Source_Relational_Classicism_A2_Gen_Closed
    Bacon_Source_Relational_Classicism_A2_Gen
    Bacon_Source_Relational_Classicism_A2_Inst
    Bacon_Source_Relational_Classicism_A2
    Bacon_Source_Relational_A3_Selector
    Bacon_Source_Relational_A3_Closed_Context
    Bacon_Source_Relational_Classicism_A3_Closed
    Bacon_Source_Relational_Classicism_A3
    Bacon_Source_Relational_Classicism_Equivalence_Iff
    Bacon_Source_Relational_Fresh_Typed_Vectors
    Bacon_Source_Relational_Identity_To_Biconditional
    Bacon_Source_Relational_Vector_Eta_Recovery
    Bacon_Source_Relational_Classicism_Zeta
    Bacon_Source_Relational_H_Theory
    Bacon_Source_Relational_Box_Syntax
    Bacon_Source_Relational_H_Theory_Necessitation
    Bacon_Source_Relational_Classicism_H_Theory
    Bacon_Source_Relational_Identity_Stability
    Bacon_Source_Relational_Box_Unfolding
    Bacon_Source_Relational_Boolean_Identity_Congruence
    Bacon_Source_Relational_H_Theory_Normal_K
    Bacon_Source_Relational_H_Theory_Modal_PE
    Bacon_Source_Relational_Implication_Lists
    Bacon_Source_Relational_H_Theory_Boxed_Lists
    Bacon_Source_Relational_H_Theory_Boxed_Consequences
    Bacon_Source_Relational_Separating_Consistency
    Bacon_Source_Relational_Positive_Diagram
    Bacon_Source_Relational_Positive_Diagram_Consistency
    Bacon_Source_Relational_Positive_Diagram_Separating_Model
    Bacon_Source_Relational_H_Theory_Closed_Extension_Bounded
    Bacon_Source_Relational_Positive_Diagram_Separating_Bounded
    Bacon_Source_Relational_Naming_Separating_Reduct
    Bacon_Source_Relational_Naming_Separation
    Bacon_Source_Relational_Naming_Bounded_Separation
    Bacon_Source_Relational_Normalization_Formula_Validity
    Bacon_Source_Relational_Normalization_Morphisms
    Bacon_Source_Relational_Bounded_Theory_Models
    Bacon_Source_Relational_Bounded_Theory_Separation
    Bacon_Source_Relational_Bounded_Theory_Quasi_Fregean
    Bacon_Source_Relational_Bounded_Theory_Inhabited
    Bacon_Source_Relational_Universal_Closure_Language
    Bacon_Source_Relational_Universal_Closure_Validity_Converse
    Bacon_Source_Relational_Bounded_Theory_Countermodel
    Bacon_Source_Relational_Bounded_Theory_Common
    Bacon_Source_Relational_Modal_Functionality_Semantics
    Bacon_Source_Relational_Quasi_Functional_Modal_Antecedent
    Bacon_Source_Relational_Quasi_Functional_From_Modal_Functionality
    Bacon_Source_Relational_Box_Truth
    Bacon_Source_Relational_Tautology_Profile
    Bacon_Source_Relational_Quasi_Fregean_Box
    Bacon_Source_Relational_Intensionality_Syntax
    Bacon_Source_Relational_Intensionality_Guarded_Replacement
    Bacon_Source_Relational_Intensionality_Certificates
    Bacon_Source_Relational_Intensionality_Proof
    Bacon_Source_Relational_Universal_Consequent
    Bacon_Source_Relational_Functionality_Saturation
    Bacon_Source_Relational_Classicism_Box_Monotonicity
    Bacon_Source_Relational_Modalized_Functionality
    Bacon_Source_Relational_Zeta_Theory
    Bacon_Source_Relational_Global_Abstraction_Beta
    Bacon_Source_Relational_Global_Abstraction_Identity
    Bacon_Source_Relational_Classicism_Theory_Minimality
    Bacon_Source_Relational_Bounded_Classicism_Category
    Bacon_Source_Relational_Bounded_Classicism_Completeness
    Bacon_Source_Relational_Bounded_PE_Zeta_Category
    Bacon_Source_Relational_Pure_Classicism_Completeness
    Bacon_Source_Relational_Arbitrary_Signature_Classicism_Completeness
    Bacon_Source_Relational_Separating_Hull_Syntax
    Bacon_Source_Relational_Separating_Hull_Monotonicity
    Bacon_Source_Relational_Separating_Hull_Stages
    Bacon_Source_Relational_Separating_Hull_Category
    Bacon_Source_Relational_Hull_Cardinal_Basics
    Bacon_Source_Relational_Hull_Cardinal_Stages
    Bacon_Source_Relational_Hull_Cardinal_Bounds
    Bacon_Source_Relational_Classicism_Counterexample
    Bacon_Source_Relational_Classical_Separating_Hull
    Bacon_Source_Relational_Rooted_Separating_Hull
    Bacon_Source_Relational_Classical_Hull_Cardinal
    Bacon_Source_Relational_Typed_Constant_Map
    Bacon_Source_Relational_Typed_Constant_Map_Binding
    Bacon_Source_Relational_Typed_Constant_Map_Conversion
    Bacon_Source_Relational_Typed_Constant_Map_Logical
    Bacon_Source_Relational_H_Typed_Constant_Map
    Bacon_Source_Relational_Classicism_Typed_Constant_Map
    Bacon_Source_Relational_Signature_Compression_Syntax
    Bacon_Source_Relational_Signature_Compression_Section
    Bacon_Source_Relational_Signature_Compression_Proof
    Bacon_Source_Relational_Figure3_Syntax
    Bacon_Source_Relational_Figure3_Language
    Bacon_Source_Relational_Figure3_Certificates
    Bacon_Source_Relational_Modal_T
    Bacon_Source_Relational_Modal_Four
    Bacon_Book_Preorder_Category
    Bacon_Book_Preorder_Powerset
    Bacon_Book_Modal_Implication_Typing
    Bacon_Book_Modal_Implication_Naturality
    Bacon_Book_Modalized_Set
    Bacon_Book_Modalized_Map
    Bacon_Book_Modalized_Exponential_Domain
    Bacon_Book_Modalized_Exponential_Homomorphisms
    Bacon_Book_Modalized_Exponential_Codec
    Bacon_Book_Modalized_Exponential_Transport
    Bacon_Book_Modalized_Exponential_Nonextension
    Bacon_Book_Modalized_Product
    Bacon_Book_Modalized_Evaluation
    Bacon_Source_Relational_Diagram_Mapping
    Bacon_Source_Relational_Diagram_Application
    Bacon_Source_Relational_Diagram_Open_Denotation
    Bacon_Source_Relational_Diagram_Homomorphism
    Bacon_Source_Relational_Universal_Closure_Syntax
    Bacon_Source_Relational_H_Theory_Universal_Closure
    Bacon_Source_Relational_H_Theory_Sentence_Fragment
    Bacon_Source_Relational_Universal_Closure_Validity
    Bacon_Source_Relational_H_Theory_Model_Existence
    Bacon_Source_Relational_H_Theory_Closed_Extension_Model
    Bacon_Source_Relational_H_Theory_Bounded_Model
    Bacon_Source_Relational_H_Theory_Substitution
    Bacon_Source_Relational_Theoretical_Naming_Coordinate
    Bacon_Source_Relational_Theoretical_Naming_Independence
    Bacon_Source_Relational_Parameter_Theory
    Bacon_Source_Relational_Theoretical_Naming_Logical_Syntax
    Bacon_Source_Relational_Parameter_Finite_Charts
    Bacon_Source_Relational_Parameter_Propositional_Closure
    Bacon_Source_Relational_Parameter_Quantified_Closure
    Bacon_Source_Relational_Parameter_Validity
    Bacon_Source_Relational_Parameter_Logical_Axioms
    Bacon_Source_Relational_Parameter_Conversion_Axioms
    Bacon_Source_Relational_Parameter_H_Theory
    Bacon_Source_Relational_Naming_Signature_Cardinal
    Bacon_Source_Relational_Naming_Substitution
    Bacon_Source_Relational_Naming_Contractions
    Bacon_Source_Relational_Naming_Conversion_Steps
    Bacon_Source_Relational_Naming_Step_Denotation
    Bacon_Source_Relational_Naming_Conversion
    Bacon_Source_Relational_Naming_Model
    Bacon_Source_Relational_Naming_Validity
    Bacon_Source_Relational_Environment_Update_Syntax
    Bacon_Source_Relational_Environment_Update_Identity
    Bacon_Source_Relational_Environment_Finite_Identity
    Bacon_Source_Relational_Arbitrary_Representatives
    Bacon_Source_Relational_Identity_Class_Relation
    Bacon_Source_Relational_Identity_Classes
    Bacon_Source_Relational_Language_Inversion
    Bacon_Source_Relational_Validity_Basics
    Bacon_Source_Relational_Validity_Rules
    Bacon_Source_Relational_Quantifier_Axiom_Truth
    Bacon_Source_Relational_Identity_Axiom_Truth
    Bacon_Source_Relational_Propositional_Inversion
    Bacon_Source_Relational_Propositional_Truth
    Bacon_Source_Relational_Basic_Axiom_Validity
    Bacon_Source_Relational_H_Soundness
    Bacon_Source_Relational_Local_Validity
    Bacon_Source_Relational_Closed_Countermodel
    Bacon_Source_Relational_Closed_Completeness
    Bacon_Source_Relational_Common_H
    Bacon_Source_Relational_Local_Supported_Soundness
    Bacon_Source_Relational_Local_Soundness
    Bacon_Source_Relational_Abstraction_Application
    Bacon_Source_Relational_Binder_Vectors
    Bacon_Source_Relational_Vector_Assignments
    Bacon_Source_Relational_Vector_Abstraction_Denotation
    Bacon_Source_Relational_Intensional_Abstraction
    Bacon_Source_Relational_Common_Equivalence
    Bacon_Source_Relational_Equivalence_Presentation
    Bacon_Source_Relational_Common_Quantifier_Rules
    Bacon_Source_Relational_Equivalence_Soundness
    Bacon_Source_Relational_Classicism_Presentation
    Bacon_Source_Relational_Classicism_Soundness
    Bacon_Source_Relational_Classicism_BBK_Soundness
    Bacon_Source_Rooted_Category
    Bacon_Source_Reachable_Subcategory
    Bacon_Source_Reachable_Category
    Bacon_Source_Relational_Profile_Restriction
    Bacon_Source_Relational_Intensional_Restriction
    Bacon_Source_Relational_Reachable_Subcategory
    Bacon_Source_Relational_Reachable_Intensional

session Bacon_Classicism_ZF_Representation in "theories/classicism/action_models/hol_zf" = "HOL-ZF" +
  description "
    Concrete set/function-graph representation for the action-model carrier
    program. Relative to the standard HOL-ZF set axioms; separate from the
    pure-HOL H/C soundness development. No Goodman imports.
  "
  options [timeout = 60, export_theory = true]
  sessions
    "HOL-Cardinals"
    Bacon_Classicism_Action_Development
  theories
    Bacon_Source_ZF_Function_Graphs
    Bacon_Source_ZF_Natural_Bounds
    Bacon_Source_ZF_Subset_Carriers
    Bacon_Source_ZF_Dependent_Pairs
    Bacon_Source_ZF_Dependent_Function_Graphs
    Bacon_Source_ZF_Embedded_Carriers
    Bacon_Source_ZF_Outgoing_Pairs
    Bacon_Source_ZF_Pair_Function_Graphs
    Bacon_Source_ZF_Exponential_Code
    Bacon_Source_ZF_Exponential_Codec
    Bacon_Source_ZF_Pair_Transport
    Bacon_Source_ZF_Exponential_Transport
    Bacon_Source_ZF_Exponential_Action
    Bacon_Source_ZF_Powerset_Coding
    Bacon_Source_ZF_Powerset_Action
    Bacon_Source_ZF_Individual_Action
    Bacon_Source_ZF_Category_Encoding
    Bacon_Source_ZF_Encoded_Category
    Bacon_Source_ZF_Reindexed_Action
    Bacon_Source_ZF_Identity_Individual_Base
    Bacon_Source_ZF_Range_Carriers
    Bacon_Source_ZF_Range_Action
    Bacon_Source_ZF_Powerset_Reindexing
    Bacon_Source_ZF_R_Truth_Profile_Coding
    Bacon_Source_ZF_R_Truth_Profile_Action
    Bacon_Source_ZF_R_Proposition_Range
    Bacon_Source_ZF_R_Type_Recursion
    Bacon_Source_ZF_R_Arrow_Coherence
    Bacon_Source_ZF_R_Arrow_Bound
    Bacon_Source_ZF_R_Arrow_Injectivity
    Bacon_Source_ZF_R_Arrow_Naturality
    Bacon_Source_ZF_R_Arrow_Action
    Bacon_Source_ZF_R_Type_Invariant
    Bacon_Source_ZF_R_Individual_Base
    Bacon_Source_ZF_R_Proposition_Base
    Bacon_Source_ZF_R_Base_Invariants
    Bacon_Source_ZF_R_Arrow_Invariant
    Bacon_Source_ZF_R_All_Type_Representation
    Bacon_Source_ZF_Action_Premodel
    Bacon_Source_ZF_R_Premodel_Domains
    Bacon_Source_ZF_Rooted_Category_Encoding
    Bacon_Source_ZF_R_Family_Actions
    Bacon_Source_ZF_R_Root_Constants
    Bacon_Source_ZF_R_Constructed_Premodel
    Bacon_Source_ZF_R_Canonical_Application
    Bacon_Source_ZF_R_Representation_Assignment_Syntax
    Bacon_Source_ZF_R_Representation_Assignments
    Bacon_Source_ZF_Graph_Application
    Bacon_Source_ZF_Premodel_Application
    Bacon_Source_ZF_Action_Assignments
    Bacon_Source_ZF_R_Action_Assignments
    Bacon_Source_ZF_Partial_Abstraction
    Bacon_Source_ZF_Logical_Values
    Bacon_Source_ZF_Logical_Value_Evaluation
    Bacon_Source_ZF_Partial_Interpretation
    Bacon_Source_ZF_Action_Model
    Bacon_Source_ZF_Premodel_Evaluation
    Bacon_Source_ZF_R_Eval_Basic_Correspondence
    Bacon_Source_ZF_R_Assignment_Naturality
    Bacon_Source_ZF_R_Lambda_Input
    Bacon_Source_ZF_R_Lambda_Graph
    Bacon_Source_ZF_R_Eval_Lambda_Correspondence
    Bacon_Source_ZF_R_Negation_Profile_Code
    Bacon_Source_ZF_R_Negation_Correspondence
    Bacon_Source_ZF_R_Proposition_Identity_Truth
    Bacon_Source_ZF_R_Quantifier_Tests
    Bacon_Source_ZF_R_Quantifier_Profile_Code
    Bacon_Source_ZF_R_Quantifier_Correspondence
    Bacon_Source_ZF_R_Coded_Application
    Bacon_Source_ZF_R_Boolean_Profile_Code
    Bacon_Source_ZF_R_Binary_Logical_Graphs
    Bacon_Source_ZF_R_Boolean_Correspondence
    Bacon_Source_ZF_R_Identity_Profile_Code
    Bacon_Source_ZF_R_Identity_Correspondence
    Bacon_Source_ZF_R_Eval_Logical_Correspondence
    Bacon_Source_ZF_R_Eval_Correspondence
    Bacon_Source_ZF_R_Constructed_Model
    Bacon_Source_ZF_R_Root_Truth_Correspondence
    Bacon_Source_ZF_R_Represented_Category_Action_Model
    Bacon_Source_ZF_Hull_Representation
    Bacon_Source_ZF_Action_Countermodel
    Bacon_Source_ZF_Action_Constant_Pullback
    Bacon_Source_ZF_Action_Completeness
    Bacon_Source_ZF_Action_Validity_On
    Bacon_Source_ZF_Pure_Action_Completeness
    Bacon_Source_ZF_Arbitrary_Signature_Action_Countermodel
    Bacon_Source_ZF_Arbitrary_Signature_Action_Completeness
    Bacon_Source_ZF_Evaluation_Locality
    Bacon_Source_ZF_Action_Model_Nonempty
    Bacon_Source_ZF_Action_BBK_Domains
    Bacon_Source_ZF_Degenerate_Premodel
    Bacon_Source_ZF_Premodel_Naturality_Regression
    Bacon_Source_ZF_Logical_Naturality
    Bacon_Source_ZF_Model_Logical_Naturality
    Bacon_Source_ZF_Assignment_Transport_Laws
    Bacon_Source_ZF_Premodel_Application_Naturality
    Bacon_Source_ZF_Abstraction_Naturality
    Bacon_Source_ZF_Model_Evaluation_Naturality
    Bacon_Source_ZF_Evaluation_Contexts
    Bacon_Source_ZF_Model_Evaluation_Contexts
    Bacon_Source_ZF_Exponential_Identity_Application
    Bacon_Source_ZF_Model_Eta_Conversion
    Bacon_Source_ZF_Substitution_Support
    Bacon_Source_ZF_Substitution_Abstraction
    Bacon_Source_ZF_Model_Substitution
    Bacon_Source_ZF_Model_Beta_Conversion
    Bacon_Source_ZF_Model_Conversion_Steps
    Bacon_Source_ZF_Model_Signature_Conversion
    Bacon_Source_ZF_Model_Conversion
    Bacon_Source_ZF_Action_BBK_Interpretation
    Bacon_Source_ZF_Proposition_Transport
    Bacon_Source_ZF_Model_Truth_Separation
    Bacon_Source_ZF_Action_BBK_Logical_Application
    Bacon_Source_ZF_Action_BBK_Propositional_Truth
    Bacon_Source_ZF_Action_BBK_Identity_Truth
    Bacon_Source_ZF_Action_BBK_Quantifier_Truth
    Bacon_Source_ZF_Action_BBK_Model
    Bacon_Source_ZF_Model_Vector_Equality
    Bacon_Source_ZF_Model_Vector_Identity
    Bacon_Source_ZF_Action_H_Soundness
    Bacon_Source_ZF_Action_Logical_Equivalence
    Bacon_Source_ZF_Action_BBK_Representation
    Bacon_Source_ZF_Action_Classicism_Soundness
    Bacon_Classicism_ZF_Audit

session Bacon_Core_Audit_Catalog in "theories/core_audit/catalog" = Bacon_Book_Environment_Development +
  description "
    Completed import heap and one ordered string catalog for the principal
    theorem audit. No selected theorem is resolved or audited in this stage.
  "
  options [timeout = 60, export_theory = true]
  sessions
    Bacon_Parametric_Countable_Development
    Bacon_Source_Vocabulary_Development
    Bacon_Source_Model_Development
    Bacon_C_Equivalence_Development
    Bacon_Classicism_Action_Development
    Bacon_Auxiliary_Bridge_Development
    Bacon_C_Presentation_Development
  theories
    Bacon_Core_Audit_Catalog

session Bacon_Core_Audit_First in "theories/core_audit/first" = Bacon_Core_Audit_Catalog +
  description "
    First disjoint slice of the principal theorem-object audit, inherited
    by the final audit session together with its verified report records.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_Core_Audit_First

session Bacon_Core_Theorem_Audit in "theories/core_audit" = Bacon_Core_Audit_First +
  description "
    Final principal theorem-object audit: check the second slice, verify
    exact complete catalog coverage, and export the combined report.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_Core_Theorem_Audit

session Bacon_Classicism in "theories/classicism" = Bacon_Base +
  description "
    Classicism, including CE, CEV, modal derivations, semantics, and
    canonical-model infrastructure.
  "
  theories
    Bacon_Finite_CEV_Model

session Bacon_C_Equivalence_Development in "theories/classicism/equivalence_development" = Bacon_Classicism +
  description "
    Granular reconstruction of Bacon's Theorem 6.1 and Bacon--Dorr Appendix A.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_Equivalence_Closure
    Bacon_C_PC_Atomic_Evaluation
    Bacon_C_PC_Zeroary
    Bacon_C_PC_Atom_Map
    Bacon_C_Appendix_A2_EG
    Bacon_C_Appendix_A2_LL
    Bacon_C_Appendix_A2_H
    Bacon_C_Equivalence_From_Vector_Truth
    Bacon_C_Appendix_A2_Closed_Axioms
    Bacon_C_Vector_Eta_Contraction

session Bacon_C_Presentation_Development in "theories/classicism/presentation_reconciliation" = Bacon_Classicism +
  description "
    Reconciliation of existing Equivalence presentations with the C-only
    Appendix A proof, kept outside that proof's dependency chain.
  "
  options [timeout = 60, export_theory = true]
  sessions
    Bacon_C_Equivalence_Development
    Bacon_H_Only_Classicism_Development
  theories
    Bacon_C_Modal_Reconciliation
    Bacon_H_Only_Classicism_Equivalence

session Bacon_H_Only_Classicism_Development in "theories/classicism/h_only_presentations" = Bacon_Classicism +
  description "
    Independent H-only Equivalence and Logical Equivalence formulations,
    with explicit proof bridges to the represented Classical Identities.
  "
  options [timeout = 60, export_theory = true]
  sessions
    Bacon_C_Equivalence_Development
  theories
    Bacon_HLE_Boolean_Identities
    Bacon_H_Forall_Distribution
    Bacon_H_Exists_Distribution
    Bacon_HLE_Identity_Identity
    Bacon_HLE_Quantifier_Identities

session Bacon_H_Henkin_Equality_Development in "theories/classicism/h_henkin_equality" = Bacon_Classicism +
  description "
    Granular closed-term identity classes for exact H completeness.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_H_Henkin_Equality

session Bacon_H_Henkin_Substitution_Development in "theories/classicism/h_henkin_substitution" = Bacon_H_Henkin_Equality_Development +
  description "
    Simultaneous-substitution congruence for the H identity quotient.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_H_Henkin_Substitution

session Bacon_BBK_Semantics_Development in "theories/classicism/bbk_semantics_development" = Bacon_H_Henkin_Substitution_Development +
  description "
    Source-faithful BBK semantic interface and exact H soundness development.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_H_Signature_Proof

session Bacon_Auxiliary_Bridge_Development in "theories/classicism/auxiliary_bridges" = Bacon_BBK_Semantics_Development +
  description "
    Checked bridges from useful earlier semantic infrastructure to the exact
    Bacon--Dorr BBK interface, including the audited signature
    reconciliation equivalence H_signature_parametric_iff; no source-fidelity
    claim is implied.
  "
  options [timeout = 60, export_theory = true]
  sessions
    Bacon_Parametric_Signature_Development
    Bacon_Source_Model_Development
    Bacon_Book_Environment_Development
  theories
    Bacon_Applicative_BBK_Bridge
    Bacon_H_Signature_Reconciliation
    Bacon_Finite_Calibration_BBK_Inhabitation
    Bacon_Book_Model_Inhabitation

session Bacon_Book_Lambda_I_Regressions in "theories/base/book_lambda_I_regressions" = Bacon_Auxiliary_Bridge_Development +
  description "
    Regression outside the core λI session: an actual λI model with a typed
    assignment satisfying ⊥ → ⊥, obtained from the auxiliary-bridge full
    minimal model existence theorem and the restriction of full minimal
    models to λI models; {⊥ → ⊥} is λI-consistent.
  "
  options [timeout = 60, export_theory = true]
  sessions Bacon_Book_Lambda_I_Development
  theories
    Bacon_Book_Lambda_I_Model_Regression

session Bacon_General_Model_Development in "theories/classicism/general_model_development" = Bacon_BBK_Semantics_Development +
  description "
    Bacon's general models, Leibniz equivalence, and Leibnizian specialization.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_General_Model_Semantics

session Bacon_H_BBK_Canonical_Development in "theories/classicism/h_bbk_canonical" = Bacon_BBK_Semantics_Development +
  description "
    Canonical closed-term domains and denotation for exact H BBK completeness.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_H_BBK_Completeness

session Bacon_H_BBK_Countable_Development in "theories/classicism/h_bbk_countable" = Bacon_H_BBK_Strong_Completeness_Development +
  description "
    Transport of the canonical BBK model to subsets of the natural numbers,
    and the theorem-object audit of the older represented H--BBK
    development (exact H soundness, canonical closed-term completeness,
    arbitrary-theory model existence, natural-number transport, Henkin
    substitution congruences).
  "
  options [timeout = 60, export_theory = true]
  sessions Bacon_H_Henkin_Substitution_Development
  theories
    Bacon_H_BBK_Countable_Arbitrary_Model
    Bacon_H_BBK_Audit

session Bacon_H_BBK_Strong_Completeness_Development in "theories/classicism/h_bbk_strong_completeness" = Bacon_H_BBK_Canonical_Development +
  description "
    Arbitrary-theory Henkinization and exact BBK model existence for H.
  "
  options [timeout = 60, export_theory = true]
  theories
    Bacon_H_Arbitrary_Model
