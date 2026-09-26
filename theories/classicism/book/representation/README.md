# Canonical modal representation

The pure-HOL layer supplies the term-model and representation ingredients.
The `hol_zf` child constructs all-type internal carriers and the actual
canonical modal model on a coded frame (arbitrary name carrier, bounded
term code injective on admitted terms). The source-directed
original-signature theorem is
[`book_full_C_small_declared_nontrivial_modal_model_exists`](hol_zf/Bacon_Book_ZF_Declared_Names_Existence.thy):
a rich stock, an injection of the declared-name union into the elements of
some ZF set, well-formed premises and full-C consistency give a nontrivial
model and admissible interpretation satisfying the theory. The countably
declared theorem
[`book_full_C_countable_nontrivial_modal_model_exists`](hol_zf/Bacon_Book_ZF_Countable_Nontrivial_Existence.thy)
and the ZF-small-carrier theorem are retained as special cases, with their
independent proofs. Ingredients include `full_ZF_canonical_nontrivial_modal_model` in
[Bacon_Book_ZF_Canonical_Nontrivial_Model.thy](hol_zf/Bacon_Book_ZF_Canonical_Nontrivial_Model.thy)
and `book_full_C_ambient_nontrivial_modal_model_exists` in
[Bacon_Book_ZF_Ambient_Nontrivial_Existence.thy](hol_zf/Bacon_Book_ZF_Ambient_Nontrivial_Existence.thy).
The earlier selected `book_full_C_countable_modal_model_exists` and its
audit remain available for the weaker structural predicate; the nontrivial
predicate is an explicit refinement, not a change to that definition.
Generic full-C soundness and modal completeness are proved in
`../modal_semantics/soundness/`; consult the current scope and source
qualifications below.

Use the repository's [status](../../../../STATUS.md),
[source correspondence](../../../../docs/SOURCE_CORRESPONDENCE.md), and
[reading guide](../../../../docs/READING_GUIDE.md).
The theorem statements and the selected ROOT closure determine verified scope.
