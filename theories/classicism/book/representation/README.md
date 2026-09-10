# Canonical modal representation

The pure-HOL layer supplies the term-model and representation ingredients.
The `hol_zf` child constructs all-type internal carriers and the actual
canonical modal model. The source-directed original-signature theorem is
[`book_full_C_countable_nontrivial_modal_model_exists`](hol_zf/Bacon_Book_ZF_Countable_Nontrivial_Existence.thy).
It constructs a model and interpretation satisfying the consistent theory,
with inhabited domains at every type and world and a proposition false at
each world. Countability is required only of the declared constants at
each type, not of the ambient constant-name carrier, and the original
signature needs no spare-name reserve.

Its ingredients include `full_ZF_canonical_nontrivial_modal_model` in
[Bacon_Book_ZF_Canonical_Nontrivial_Model.thy](hol_zf/Bacon_Book_ZF_Canonical_Nontrivial_Model.thy)
and `book_full_C_ambient_nontrivial_modal_model_exists` in
[Bacon_Book_ZF_Ambient_Nontrivial_Existence.thy](hol_zf/Bacon_Book_ZF_Ambient_Nontrivial_Existence.thy).
The earlier selected `book_full_C_countable_modal_model_exists` and its
audit remain available for the weaker structural predicate. The stronger
predicate is an explicit refinement, not a change to that definition.
Generic full-C soundness, rerooting and unrestricted modal completeness
are separate obligations; consult the current scope and source
qualifications below.

Use the repository's [status](../../../../STATUS.md),
[source correspondence](../../../../docs/SOURCE_CORRESPONDENCE.md), and
[reading guide](../../../../docs/READING_GUIDE.md).
The theorem statements and the selected ROOT closure determine verified scope.
