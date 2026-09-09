theory Bacon_Book_Full_Classicism_Audit
  imports Bacon_Book_Full_Classicism_Name_Inverse Bacon_Book_Full_Classicism_Base_Bridge
    Bacon_Book_Full_MF_Fresh_Instances Bacon_Book_Full_Ambient_Henkin_Extension
    Bacon_Book_Full_Proposition_Representation Bacon_Book_Full_Term_Quasi_Functionality
begin

section \<open>Separate kernel audit of the Chapter 8 full-type presentation\<close>

ML_file "../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("the three MF binders are distinct in a rich typed stock", "book_MF_names_distinct"),
    ("the literal all-type MF axiom is a formula", "book_MF_axiom_language"),
    ("the literal all-type MF axiom is closed", "book_MF_axiom_closed"),
    ("every full-C proof has a well-typed book-language conclusion", "book_full_C_proves_language"),
    ("full-C theorems are closed under the native H theory calculus", "book_full_C_contains_theory_derivation"),
    ("the finite H/MF/MP/Gen/PE calculus equals the independently defined least full theory", "book_full_C_iff_proves"),
    ("Necessitation is derived for original full-C theorems", "book_full_C_necessitation"),
    ("generalization is derived for original full-C theorems", "book_full_C_generalize"),
    ("capture-guarded variable substitution is derived for full-C theorems", "book_full_C_variable_substitution"),
    ("the open MF body follows by eliminating the two outer binders", "book_full_C_MF_body"),
    ("type-indexed constant maps preserve all five full-C proof constructors", "book_full_C_typed_name_map"),
    ("empty additional-premise consequence is exactly full-C theoremhood", "book_full_C_theory_empty_iff"),
    ("full-C consequence uses only finitely many additional assumptions", "book_full_C_theory_finite_support"),
    ("full-C consistency has finite character", "book_full_C_theory_consistent_finite_character"),
    ("type-indexed maps preserve full-C consequence including its background", "book_full_C_theory_typed_name_map"),
    ("declared-component injections preserve and reflect full-C consequence in the exact image", "book_full_C_theory_typed_image_iff"),
    ("declared-component injections preserve and reflect full-C consistency in the exact image", "book_full_C_consistent_typed_image_iff"),
    ("the open MF condition has the stated function and argument types", "book_MF_condition_language"),
    ("MF can be instantiated with arbitrary closed function terms", "book_full_C_MF_closed_instance"),
    ("open-head MF instances retain explicit sequential-substitution freshness", "book_full_C_MF_fresh_instance"),
    ("binder renaming follows from precisely the eta freshness and beta free-for provisos", "book_binder_rename_with_free_for"),
    ("the argument binder of an MF condition changes by typed declared-language conversion", "book_MF_condition_binder_conversion"),
    ("the MF body is available at every correctly typed argument variable", "book_full_C_MF_argument_variant"),
    ("arbitrary open typed MF heads require only the intended argument freshness", "book_full_C_MF_instance"),
    ("original pointwise identity yields function identity by generalization Necessitation and MF", "book_full_C_function_identity_rule"),
    ("all finite vector Equivalence rules are derived in the MF plus PE calculus", "book_full_C_vector_equivalence"),
    ("every proof in the retained Equivalence base embeds in full C", "book_C_base_embeds_full"),
    ("MF plus vector Equivalence and MF plus PE prove exactly the same formulas", "book_full_C_presentations_iff"),
    ("base theory consequence embeds in full-C consequence with the same added premises", "book_C_base_theory_embeds_full"),
    ("full-C consistency implies base consistency but no converse is assumed", "book_full_C_consistency_implies_base"),
    ("every full-C proof has finite fresh-variable retraction support including the MF case", "book_full_C_retraction_support_exists"),
    ("full-C theoremhood is conservative under declared-signature extension", "book_full_C_signature_conservativity"),
    ("one fresh retraction transports a full-C consequence and its finitely used background", "book_full_C_theory_retraction_fresh"),
    ("full-C consistency of old-language premises survives signature change", "book_full_C_theory_consistency_signature_preservation"),
    ("new-constant full-C theorems are recovered from the old full-C background", "book_full_C_new_constant_theorem_from_old_background"),
    ("one fresh conditional witness preserves full-C consistency in the enlarged language", "book_full_C_consistent_conditional_witness"),
    ("finite witness families retain the full-C background at each partial signature", "book_full_C_consistent_finite_witness_family"),
    ("arbitrary witness families preserve full-C consistency", "book_full_C_consistent_witness_family"),
    ("uniform injective name recoding preserves and reflects full-C consistency", "book_full_C_consistent_constant_rename_iff"),
    ("each actual Henkin premise stage is consistent over its full-C theorem set", "book_full_C_henkin_premises_consistent"),
    ("the actual Henkin union is consistent over full C of the final signature", "book_full_C_henkin_full_premises_consistent"),
    ("closed full-C theorems recover the entire full-C consequence background", "book_full_C_consequence_closed_fragment_iff"),
    ("universal closure of the additional premises preserves full-C consistency", "book_full_C_consistent_universal_closures"),
    ("consistent closed full-C premises have actual maximal extensions", "book_full_C_closed_maximal_extension_exists"),
    ("a full-C closed maximal extension retains full-C consistency", "book_full_C_closed_maximal_consistent"),
    ("full-C consistency yields an actual closed maximal constant-witness-complete Henkin extension", "book_full_C_closed_henkin_extension_exists"),
    ("old-name-fixing image transport yields an actual full-C Henkin extension", "book_full_C_henkin_image_extension_exists"),
    ("full-C Henkin completion is realized inside the fixed countable ambient language", "book_countable_ambient_signature.book_full_C_ambient_henkin_extension_exists"),
    ("full-C closed maximal sets satisfy the base maximal condition in the same language", "book_full_C_closed_maximal_is_base"),
    ("finite boxed consequence is derived over the full-C background", "book_full_C_theory_box_lift"),
    ("an absent boxed consequence has a full-C-consistent negative successor seed", "book_full_C_successor_seed_consistent"),
    ("full-C closed maximal sets have actual negative successors", "book_full_C_closed_successor_exists"),
    ("full-C successors gain all closed-predicate witnesses inside the fixed ambient language", "book_countable_ambient_signature.book_full_C_ambient_henkin_successor_exists"),
    ("the full-C canonical world set is proved included in the base world set", "book_full_C_canonical_world_is_base"),
    ("full-C accessibility implies language inclusion", "book_full_C_canonical_le_language"),
    ("full-C canonical accessibility is reflexive", "book_full_C_canonical_le_refl"),
    ("full-C canonical accessibility is transitive", "book_full_C_canonical_le_trans"),
    ("countably declared signatures have consistency-equivalent full-C natural-name recodings", "book_full_C_countable_signature_consistency_iff"),
    ("countably declared full-C-consistent premises have an actual canonical world", "book_full_C_countable_canonical_world_exists"),
    ("the actual full-C world set has a witness-complete successor for an absent Box", "book_full_C_canonical_successor_exists"),
    ("full-C-consistent premises yield an actual rooted canonical frame", "book_countable_ambient_signature.book_full_C_canonical_frame_exists"),
    ("Bacon Proposition 18.3 holds over the actual full-C rooted frame", "book_full_C_canonical_frame.book_proposition_18_3"),
    ("the per-world identity-class algebra is interpreted at every full-C canonical world", "book_full_C_world_identity_algebra"),
    ("all identity-class domains are nonempty at every full-C canonical world", "book_full_C_canonical_identity_domain_nonempty"),
    ("truth sets over full-C futures separate proposition classes", "book_full_C_canonical_frame.proposition_profiles_eq_iff_classes"),
    ("the full-C proposition representation is an actual bijection", "book_full_C_canonical_frame.proposition_h_bijection"),
    ("the full-C proposition inverse recovers every source class", "book_full_C_canonical_frame.proposition_jh"),
    ("the full-C proposition forward map recovers every represented truth set", "book_full_C_canonical_frame.proposition_hj"),
    ("the full-C proposition map commutes with counterparts and future restriction", "book_full_C_canonical_frame.proposition_h_naturality"),
    ("full-C proposition domains are closed under future restriction", "book_full_C_canonical_frame.proposition_domain_truncation"),
    ("future applications separate closed function terms in the full-C frame at all F types", "book_full_C_canonical_frame.full_term_future_application_separates"),
    ("the actual full-C term domains and operations are quasi-functional", "book_full_C_canonical_frame.full_term_quasi_functional")]
  val checked = Bacon_Core_Audit_Check.run @{context} "full-type-book-C"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "SCOPE: book full-F/minimal MF plus PE and MF plus vector Equivalence; base proof embedding; no modal completeness claim\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "full-book-classicism-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

text \<open>
  These endpoints belong to the explicit full-type presentation and
  are kept separate from the 92-endpoint Equivalence-base audit.
  Base proof embedding and full-background signature/witness/Henkin
  construction are now checked. Kernel cleanliness does not supply
  consistency preservation when MF is added to a base-consistent theory,
  the functional-type h/j representation, full λ interpretation, or a
  modal-model theorem. The full-C frame, proposition representation and
  term quasi-functionality are now included in this audit.
\<close>

end
