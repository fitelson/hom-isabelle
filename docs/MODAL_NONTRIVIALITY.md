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
available at each future world. Generic soundness turned out not to need
a rerooting construction: the invariant "valid at every world under every
typed assignment" is proved directly for every full-C theorem, and the
identity, box and H clauses hold even in the broad structural class. The
false proposition is used exactly where it must be: to turn a derivable
bottom into a falsehood at the root (satisfiable ⇒ consistent).

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
| Every full-C theorem is valid at every world of every nontrivial model | `book_ZF_nontrivial_modal_interpretation.full_C_valid_everywhere` |
| Satisfiable theories are full-C consistent | `book_ZF_nontrivial_modal_interpretation.satisfiable_theory_consistent` |
| Consistency iff satisfiability, countably declared signatures | `book_full_C_theory_consistent_iff_satisfiable` |
| Consistency iff satisfiability, ZF-small name carriers | `book_full_C_theory_consistent_iff_satisfiable_small_carrier` |
| Consistent theories on ZF-small whole name carriers have nontrivial original-signature models | `book_full_C_small_carrier_nontrivial_modal_model_exists` |
| The same existence result on the uncountable carrier `nat set` | `book_full_C_nat_set_carrier_nontrivial_modal_model_exists` |
| Derivability iff root consequence for ZF-small whole name carriers | `book_full_C_theory_derivable_iff_consequence_small_carrier` |
| Consistent theories with a ZF-bounded declared-name union have nontrivial original-signature models, on any carrier | `book_full_C_small_declared_nontrivial_modal_model_exists` |
| The same on the carrier ZF with a set-bounded declared union | `book_full_C_ZF_carrier_nontrivial_modal_model_exists` |
| Consistency iff satisfiability for ZF-bounded declared names | `book_full_C_theory_consistent_iff_satisfiable_small_declared` |
| Derivability iff root consequence for ZF-bounded declared names | `book_full_C_theory_derivable_iff_consequence_small_declared` |

The countably declared nontrivial existence theorem retains its four
original input premises: rich stock, countably many declared constants
per type, well-formed premises and full-C consistency. Its original
carrier remains arbitrary. The additional small-carrier theorem replaces
the declaration-countability hypothesis with a total injection of the
whole name carrier into the elements of an actual ZF set. It permits
all names of that carrier to be declared, including on the uncountable
carrier `nat set`. The declared-names theorem replaces both by a single
hypothesis: an injective code of the declared-name union into the elements
of an actual ZF set, on an arbitrary carrier; the earlier two follow from
it. All prove the extra semantic conditions of their constructed models;
they do not assume them of the input theory. Open formulas and arbitrary
premise sets remain allowed.

The old external existence statements and generic interpretation-existence
result remain available. Internal canonical worlds now carry a cardinal
reserve condition, and the HOL–ZF representation is parameterized by a
bounded total term code. These are construction/interface changes, not
changes to the independent structural or nontrivial model definitions.
There is no PER substitution or replacement by full function spaces.

## Maintained regression and remaining work

The [singleton regression](../theories/classicism/book/modal_semantics/regressions/Bacon_Book_ZF_Singleton_Regression.thy)
is selected by the default check in `Bacon_Book_ZF_Model_Regressions`.
Its proof constructs the actual all-type function graphs, an inhabited
assignment, an admissible interpretation, and the inconsistency witness.
The regression and the new nontrivial-model results have separate
theorem-object audits.

Generic full-C soundness for the refined class is proved without a
cardinality restriction (26 September 2026). The root-consequence and
consistency characterizations are proved both for countably declared
signatures on arbitrary carriers and for ZF-small whole name carriers.
They are subsumed by the declared-names versions, which cover the type
`ZF` itself whenever the declared union is contained in a ZF set. Declared
unions with no ZF-bounded injection are outside this construction (a
limitation of the injective syntax coding, not a proof that such theories
lack models); the broader λ-sublanguage and primitive-profile variants
remain open. All these
statements retain the full minimal language, rich stock where stated, the
explicit nontrivial class, root consequence, future-restricted implication
and literal box conventions. See [STATUS.md](../STATUS.md) and the
[contributor guide](../CONTRIBUTING.md).
