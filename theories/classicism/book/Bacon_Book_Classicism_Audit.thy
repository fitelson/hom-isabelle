theory Bacon_Book_Classicism_Audit
  imports Bacon_Book_Modal_Term_Inhabitation
begin

section \<open>Separate kernel audit of the native book-C interface\<close>

ML_file "../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("native full-F book C proofs have book-language conclusions", "book_C_proves_language"),
    ("book Definition 6.1 equals the independent finite C calculus", "book_C_iff_proves"),
    ("C-theory consequence with no additional assumptions is exactly C", "book_C_theory_empty_iff"),
    ("C-theory consequence uses finitely many additional assumptions", "book_C_theory_finite_support"),
    ("C-theory consistency has finite character", "book_C_theory_consistent_finite_character"),
    ("closed underivability permits a consistent negative extension over C", "book_C_theory_consistent_negative_extension"),
    ("the book Equivalence rule gives propositional Leibniz identity", "book_C_propositional_equivalence"),
    ("H proves the literal biconditional-with-truth implication without C completeness", "book_H_imp_iff_top"),
    ("book C admits Necessitation on original theorems only", "book_C_necessitation"),
    ("book C proves normal modal K from its own Propositional Equivalence", "book_C_normal_K"),
    ("the book literal Box satisfies T already in H", "book_H_modal_T"),
    ("closed additional premises admit finite boxed consequence over fixed C", "book_C_theory_box_lift"),
    ("closed C theorems recover the entire open C background", "book_C_consequence_closed_fragment_iff"),
    ("consistent closed C premise sets have actual fixed-signature maximal extensions", "book_C_closed_maximal_extension_exists"),
    ("an absent Box has an actual closed negation-complete fixed-signature successor", "book_C_closed_successor_exists"),
    ("book C proves modal 4 by necessitating only the original theorem Box top", "book_C_modal_4"),
    ("canonical accessibility of closed maximal C sets is transitive", "book_C_accessible_transitive"),
    ("Box membership is exactly truth in all accessible fixed-signature closed maximal sets", "book_C_closed_world_box_iff"),
    ("the entire native book C proof has finite fresh-variable retraction support", "book_C_retraction_support_exists"),
    ("native book C theoremhood is conservative under declared-signature extension", "book_C_signature_conservativity"),
    ("one fresh retraction transports a C-plus-assumptions proof including its finitely used C background", "book_C_theory_retraction_fresh"),
    ("one fresh conditional witness preserves consistency with the full enlarged-language C background", "book_C_consistent_conditional_witness"),
    ("finite witness families preserve C consistency at each partial signature", "book_C_consistent_finite_witness_family"),
    ("arbitrary witness families preserve consistency over the full enlarged C background", "book_C_consistent_witness_family"),
    ("uniform constant-name maps preserve all four book C proof constructors", "book_C_constant_rename"),
    ("injective name-carrier transport preserves and reflects C-theory consistency", "book_C_consistent_constant_rename_iff"),
    ("all constructed Henkin premise stages retain their own C consistency", "book_C_henkin_premises_consistent"),
    ("the actual full Henkin premise union is consistent over final-signature C", "book_C_henkin_full_premises_consistent"),
    ("a consistent C premise set has an actual closed maximal constant-witness-complete extension", "book_C_closed_henkin_extension_exists"),
    ("the constructed full Henkin signature leaves an explicit infinite name reserve at every type", "book_henkin_unused_names_infinite"),
    ("type-indexed constant-name maps preserve the exact declared language", "book_typed_name_map_language"),
    ("type-indexed name maps preserve all native H theory rules", "book_theory_typed_name_map"),
    ("type-indexed name maps preserve all native book C proof constructors", "book_C_typed_name_map"),
    ("declared-component injectivity preserves and reflects C consequence in the exact image", "book_C_theory_typed_image_iff"),
    ("declared-component injectivity preserves and reflects C consistency in the exact image", "book_C_consistent_typed_image_iff"),
    ("the nested Henkin-name carrier is countable for a countable original carrier", "book_henkin_name_carrier_countable"),
    ("the explicit reserve embedding is injective and fixes old declared names", "book_countable_name_reserve.book_reserve_embedding_injective"),
    ("the explicit reserve embedding leaves infinitely many ambient names unused", "book_countable_name_reserve.book_reserve_embedding_leaves_infinite"),
    ("every target closed predicate has a literal conditional witness in the image premises", "book_henkin_image_conditional_witness"),
    ("injective old-name-fixing image transport yields an actual maximal witness-complete C extension", "book_C_henkin_image_extension_exists"),
    ("the transported Henkin signature stays inside the fixed countable ambient language", "book_countable_ambient_signature.book_ambient_henkin_signature_inside"),
    ("the transported Henkin signature retains infinitely many ambient names at each type", "book_countable_ambient_signature.book_ambient_henkin_signature_reserve"),
    ("actual C Henkin completion fixes old formulas inside a countable ambient language", "book_countable_ambient_signature.book_C_ambient_henkin_extension_exists"),
    ("an absent Box has an actual witness-complete enlarged-language successor inside the countable ambient language", "book_countable_ambient_signature.book_C_ambient_henkin_successor_exists"),
    ("countably declared signatures on arbitrary carriers have consistency-equivalent natural-name recodings", "book_C_countable_signature_consistency_iff"),
    ("the natural-name image signature has an infinite reserve at every type", "book_countable_signature_has_ambient"),
    ("H proves typed Leibniz reflexivity without C completeness", "book_H_leibniz_reflexive"),
    ("literal boxed-sentence accessibility forces declared-language inclusion", "book_C_successor_language_inclusion"),
    ("a canonical world's sentence set uniquely determines its signature", "book_C_canonical_world_sentence_injective"),
    ("canonical varying-language accessibility preserves declared signatures", "book_C_canonical_le_language"),
    ("canonical varying-language accessibility is reflexive", "book_C_canonical_le_refl"),
    ("canonical varying-language accessibility is transitive", "book_C_canonical_le_trans"),
    ("countably declared C-consistent premises have an actual canonical world after initial recoding", "book_C_countable_canonical_world_exists"),
    ("the actual canonical world set supplies a witness-complete successor for every absent Box", "book_C_canonical_successor_exists"),
    ("a consistent C premise set has an actual rooted canonical frame inside its countable ambient language", "book_countable_ambient_signature.book_C_canonical_frame_exists"),
    ("Bacon Proposition 18.3 holds on the rooted witness-complete canonical frame", "book_C_canonical_frame.book_proposition_18_3"),
    ("H proves identity stability conditional only on necessary reflexive identity", "book_H_identity_stability_conditional"),
    ("C proves identity stability at every type without local Necessitation", "book_C_identity_stability"),
    ("closed identity membership persists along canonical accessibility", "book_C_canonical_identity_persistence"),
    ("H supplies the literal identity-symmetry implication", "book_H_identity_symmetry"),
    ("H supplies the literal identity-transitivity implication", "book_H_identity_transitivity"),
    ("H supplies typed application congruence for literal identity", "book_H_identity_application"),
    ("identity in a closed C world respects both application arguments", "book_C_identity_world.identity_application"),
    ("equality of typed closed term classes is equivalent to identity in the world", "book_C_identity_world.identity_class_eq_iff"),
    ("term-class application is independent of both representatives", "book_C_identity_world.identity_class_application"),
    ("the actual identity-class application has a typed result", "book_C_identity_world.term_app_typed"),
    ("the actual term application sends F and A classes to the FA class", "book_C_identity_world.term_app_classes"),
    ("canonical identity classes grow along accessibility", "book_C_identity_class_future_inclusion"),
    ("the actual counterpart sends the A class at w to the A class at v", "book_C_term_counterpart_class"),
    ("the actual term counterpart has a typed target value", "book_C_term_counterpart_typed"),
    ("term counterparts satisfy the identity law on their typed domains", "book_C_term_counterpart_identity"),
    ("term counterparts satisfy composition on their typed domains", "book_C_term_counterpart_composition"),
    ("term application commutes with the actual counterpart maps", "book_C_term_application_naturality"),
    ("the three Boolean identities used for boxed PE are original C theorems", "book_C_boxed_PE_premises"),
    ("H derives boxed PE from those three explicitly displayed identities", "book_H_boxed_PE_from_identities"),
    ("C proves boxed propositional equivalence without a separation premise", "book_C_boxed_propositional_equivalence"),
    ("boxed propositional equivalence yields identity membership in a canonical world", "book_C_world_boxed_propositional_equivalence"),
    ("the literal biconditional has the Boolean membership clause in closed C worlds", "book_C_identity_world.member_biconditional_iff"),
    ("H proves that proposition identity implies the literal biconditional", "book_H_proposition_identity_implies_iff"),
    ("equal future truth sets are equivalent to proposition identity at the source world", "book_C_canonical_frame.proposition_profiles_eq_iff_identity"),
    ("future truth sets separate the closed proposition identity classes", "book_C_canonical_frame.proposition_profiles_eq_iff_classes"),
    ("the actual proposition map is a bijection from term classes onto future truth sets", "book_C_canonical_frame.proposition_h_bijection"),
    ("the proposition inverse after the forward map is identity on term-class values", "book_C_canonical_frame.proposition_jh"),
    ("the proposition forward map after its inverse is identity on represented propositions", "book_C_canonical_frame.proposition_hj"),
    ("proposition profiles truncate by intersection with the later future", "book_C_canonical_frame.proposition_profile_truncation"),
    ("the proposition representation commutes with term counterparts and future restriction", "book_C_canonical_frame.proposition_h_naturality"),
    ("every represented proposition is a subset of its world's future", "book_C_canonical_frame.proposition_domain_future"),
    ("current-world membership of a proposition profile is sentence membership", "book_C_canonical_frame.proposition_profile_at_world"),
    ("the represented proposition domains are closed under future restriction", "book_C_canonical_frame.proposition_domain_truncation"),
    ("H proves the existential of the closed constant-truth predicate at each type", "book_H_exists_inhabitation_predicate"),
    ("every canonical world's signature has a declared constant at each type", "book_C_canonical_signature_inhabited"),
    ("every canonical identity-class domain is nonempty", "book_C_canonical_identity_domain_nonempty")]
  val checked = Bacon_Core_Audit_Check.run @{context} "native-book-C"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "SCOPE: full-F/minimal Equivalence-rule base; Chapter 8 full C also requires all-type Modalized Functionality; no modal completeness claim\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-classicism-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

text \<open>
  This audit uses the same kernel checks as the maintained principal
  audit, but records the new book-language endpoints separately.
  Source/model correspondence, modal soundness and completeness are
  separate obligations; clean kernel fields do not discharge them.
\<close>

end
