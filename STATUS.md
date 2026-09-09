# Verification status

Workshop extraction checkpoint: 9 September 2026.

This document states the intended checked scope of the selected ROOT sessions.
The terminal build result is recorded separately in
[verification](docs/VERIFICATION.md). A theorem's actual hypotheses and
conclusion, not its name or this overview, determine its scope.

| Part | Established endpoint | Boundary |
|---|---|---|
| H, Bacon–Dorr named full-F language | Native soundness, sentence-set model existence, closed strong completeness, and countable-domain refinements | Rich variable stock; completeness uses explicit carriers and closed premises/conclusion |
| H, Bacon's full-F minimal language | General-model soundness, original-signature model existence, and global strong completeness, including open formulas and arbitrary premise sets | Full grammar and minimal logical basis; witnessed closed values; arbitrary general sublanguages are not covered |
| Classicism proof theory | Independent presentations and their proved correspondences, including the book's MF+PE and MF+vector-Equivalence presentations | The older Equivalence-rule base is not identical by definition to full-type C |
| Bacon–Dorr relational-type C | BBK-category representation/completeness and action-model single-formula soundness/completeness at arbitrary signatures | R types; explicit carrier/world-label scope; the action-model result is not an infinite-theory compression theorem |
| Bacon's full-type C | All-type canonical modal model, its independent interpretation, and original-signature model existence for full-C-consistent theories with countably many declared constants per type | Arbitrary constant-name carrier; no original spare-name requirement; full-F minimal language and rich variable stock |
| Generic book modal interpretations | Uniqueness, typed-assignment transport, and model/interpretation pullback along constant maps | Generic interpretation existence and full generic soundness remain open |
| Book full-C unrestricted modal completeness | **Not completed** | See the contributor plan |

## Completed: original-signature model existence

On 9 September 2026, `book_full_C_countable_modal_model_exists` passed
Isabelle, together with its 14-endpoint audit. It combines syntactic
consistency recoding, fixed-ambient existence, and semantic signature
pullback to eliminate the original signature's spare-name condition.
The constant-name carrier is arbitrary; only the declared constants at each
type must be countable. Open formulas and infinite premise sets are allowed.

`Bacon_Book_ZF_Countable_Model_Existence.thy` and
`Bacon_Book_ZF_Model_Existence_Audit.thy` are now selected in ROOT.
The earlier fixed-ambient theorem and its audit remain selected too.
This completes only the immediate model-existence assembly: generic
interpretation existence, generic full-C soundness, uncountably declared
signatures, and unrestricted modal completeness remain open.

Other preserved theories not reached by ROOT are not covered by a successful
default build. Run `python3 tools/check_release.py --inventory` to see the
actual source-closure inventory rather than treating every .thy file as checked.

## Source qualifications that must remain visible

- Full F and the paper's default relational R type language are distinct.
- Pure HOL results and the stronger HOL–ZF representation layer are distinct.
- A conditional representation theorem is not model existence until all its
  stock, carrier, and semantic premises are discharged.
- Definition 18.1's printed implication clause uses a W-complement. The
  formalized modal construction explicitly uses the future-restricted clause,
  (W↑v ∖ p) ∪ q. This qualification is not a claim that the printed expressions
  are literally identical.
- Whole-world function graphs use the actual typed future domains; no PER
  carrier replacement or full-exponential substitution is being made.
- Kernel verification establishes the encoded theorem. Source correspondence
  still requires mathematical review of definitions and hypotheses.

See [the source table](docs/SOURCE_CORRESPONDENCE.md) for exact entry points.
