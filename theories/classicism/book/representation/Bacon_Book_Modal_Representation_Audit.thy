theory Bacon_Book_Modal_Representation_Audit
  imports Bacon_Book_Full_Function_Step Bacon_Book_Full_Individual_Functions Bacon_Book_Full_Proposition_Modalized
    Bacon_Book_Function_Representation_Characterization
begin

ML_file "../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("the actual full-C frame satisfies the pointed-preorder interface", "book_full_C_canonical_frame.full_frame_pointed_preorder"),
    ("every actual full-C term domain satisfies the modalized-set interface", "book_full_C_canonical_frame.full_term_modalized_set"),
    ("the source of term application is an actual modalized product", "book_full_C_canonical_frame.full_term_application_product"),
    ("actual term application is a modalized map", "book_full_C_canonical_frame.full_term_application_map"),
    ("the inverse of a modalized bijection is a proved modalized map", "book_modalized_bijection.inverse_modalized_map"),
    ("the constructed function is an actual future homomorphism under the lower-type hypotheses", "book_function_representation.function_h_homomorphism"),
    ("source quasi-functionality makes the constructed function map injective", "book_function_representation.function_h_injective"),
    ("the constructed function map is bijective onto its image domain", "book_function_representation.function_h_bijection"),
    ("the function inverse recovers each source value under separation", "book_function_representation.function_jh"),
    ("the function forward map recovers each image-domain value", "book_function_representation.function_hj"),
    ("function representation commutes with literal future restriction", "book_function_representation.function_h_counterpart"),
    ("the constructed function image domains form a modalized set", "book_function_representation.function_domain_modalized"),
    ("the whole function-type step is a modalized bijection under source separation", "book_function_representation.function_representation_bijection"),
    ("the canonical individual representation is the identity bijection", "book_full_C_canonical_frame.full_individual_bijection"),
    ("the actual canonical e-to-e function representation is a modalized bijection", "book_full_C_canonical_frame.full_individual_function_bijection"),
    ("the actual e-to-e inverse recovers each source class", "book_full_C_canonical_frame.full_individual_function_jh"),
    ("the actual e-to-e forward map recovers each represented function", "book_full_C_canonical_frame.full_individual_function_hj"),
    ("represented e-to-e values are actual future homomorphisms", "book_full_C_canonical_frame.full_individual_function_homomorphism"),
    ("actual full-C proposition domains satisfy the modalized-set interface", "book_full_C_canonical_frame.full_proposition_modalized_set"),
    ("the actual full-C proposition map satisfies the modalized-bijection interface", "book_full_C_canonical_frame.full_proposition_modalized_bijection"),
    ("the canonical function step constructs a modalized bijection at arbitrary full types from lower representations", "book_full_function_step.canonical_function_bijection"),
    ("the canonical function step produces actual future homomorphisms", "book_full_function_step.canonical_function_homomorphism"),
    ("the constructed function satisfies exactly the source defining-behavior equation", "book_function_representation.function_represents_iff"),
    ("the constructed image domain equals the future homomorphisms represented by source values", "book_function_representation.function_domain_characterization")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-modal-representation"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "SCOPE: actual canonical base interfaces and e-to-e representation; conditional arbitrary function-type step; no all-type recursion or modal completeness claim\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "modal-representation-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

text \<open>
  These representation endpoints are separate from the base and full-C
  proof/frame audits. The generic function step retains its lower-type
  representation hypotheses; the canonical step discharges source
  application and quasi-functionality, and e→e is fully instantiated.
  The uniform set-universe realization, λ interpretation and the complete
  modal-model/truth theorems are established in the hol_zf child sessions
  (Bacon_Book_ZF_Modal_Representation, Bacon_Book_ZF_Modal_Interpretation,
  Bacon_Book_ZF_Modal_Soundness); this audit covers the pure-HOL layer.
\<close>

end
