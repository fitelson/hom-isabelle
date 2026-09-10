# Modal models: an explicit nontriviality requirement

## The source issue

Bacon's Definition 15.1 (p.314) requires a false proposition for the minimal
logical signature. Page 315 explicitly warns that without this condition,
∀p.p can be true. Definition 18.1 (p.391) does not repeat the condition,
although p.392 calls its modal models instances of the Chapter 15 models.

The September 10 audit verified a counterexample to the broad displayed
conditions: one world, one element at every type, and only a true proposition.
All domains are inhabited and an explicit typed assignment exists. Every
well-typed formula is true, including bottom. Thus an inconsistent theory
is satisfiable in this broad class.

This affects the satisfiable ⇒ consistent direction of Theorem 18.4 (p.398).
It does not refute the completed H or relational-C results, forward model
existence, or every possible formulation of validity completeness. On the
one-world counterexample, the printed versus future-restricted implication
distinction disappears, so that separate qualification is not its cause.

## Two model predicates, not a silent change of definition

The existing `book_ZF_modal_model` predicate is unchanged. It supplies the
structural, logical-operation and constant conditions used by the generic
interpretation construction.

The new [nontrivial model class](../theories/classicism/book/modal_semantics/hol_zf/Bacon_Book_ZF_Nontrivial_Model.thy),
`book_ZF_nontrivial_modal_model`, extends it with:

1. Dσ(w) is nonempty for every type σ and world w.
2. At every world w, some p∈Dₜ(w) is false there: w∉p.

The second condition excludes the all-true example. The first prevents
truth under every typed assignment from being vacuous because there are no
assignments. Nonemptiness alone would not exclude the singleton example.

These are explicit **source-motivated strengthening conditions**, not a
claim that both appear verbatim in Definition 18.1. In particular the
book's raw applicative structures allow arbitrary sets as domains
(Definition 14.1, p.290). For the full-minimal general-model interface,
witnessed closed denotations supply typed-assignment existence.

The worldwise formulation is deliberate: the same conditions remain
available at each future world when considering it as a new root.
The actual rerooted model and its interpretation still need their own
construction and preservation proofs. We do not claim that merely
adding these fields finishes generic soundness.

## What is now checked

| Result | Endpoint |
|---|---|
| Actual assignments at every world, for every variable stock | `book_ZF_nontrivial_modal_model.typed_assignment_exists` |
| Signature pullback preserves nontriviality | `nontrivial_signature_pullback` |
| The existing canonical model satisfies both additional conditions | `full_ZF_canonical_nontrivial_modal_model` |
| Fixed-ambient consistent theories have nontrivial models | `book_full_C_ambient_nontrivial_modal_model_exists` |
| Countably declared consistent theories have nontrivial original-signature models | `book_full_C_countable_nontrivial_modal_model_exists` |
| An actual inconsistent theory has a structural modal model | `probe_inconsistent_theory_has_model` |
| That model fails the nontrivial refinement | `probe_not_nontrivial` |

The stronger existence theorem retains the same four input premises:
rich variable stock, countably many declared constants per type,
well-formed premises, and full-C consistency. It does not assume the
extra semantic conditions of the input; it proves them of the constructed
model. Open formulas and infinite premise sets remain allowed.

The earlier forward existence theorems and the more general interpretation
existence theorem remain available with their original statements.
There is no PER substitution or alternative canonical carrier.

## Maintained regression and remaining work

The [singleton regression](../theories/classicism/book/modal_semantics/regressions/Bacon_Book_ZF_Singleton_Regression.thy)
is selected by the default check in `Bacon_Book_ZF_Model_Regressions`.
Its proof constructs the actual all-type function graphs, an inhabited
assignment, an admissible interpretation, and the inconsistency witness.
The regression and the new nontrivial-model results have separate
theorem-object audits.

Still open: generic full-C soundness, the exact final completeness/
consistency characterization for the refined class, and the uncountably
declared-signature existence extension. The [contributor guide](../CONTRIBUTING.md)
breaks the semantic work into smaller tasks.
