# Verification status

## Repository organization, 20 September 2026

The [Applications folder](Applications/README.md) now contains
[Goodman's Purity of Pure project](Applications/goodman-isabelle/README.md)
as ordinary files. Its [status](Applications/goodman-isabelle/STATUS.md),
[report](Applications/goodman-isabelle/reports/GOODMAN_VERIFICATION_REPORT_2026-09-20.pdf)
and checker are separate from the core's. The migration does not alter any
core theorem or ROOT selection. The core theorem/audit status below remains
unchanged; application claims must not be counted as core completions.

## Core verification status

Latest checkpoint: 26 September 2026 (comprehensive repository audit and
its fixes, after the relevant λI language: model existence and
completeness); audit-response checkpoint: 10 September 2026.

The subsequent [source-fidelity consensus audit](docs/PARTIAL_SOURCE_AUDIT_2026-09-10.md)
completed 120 of 1,380 theory files and stopped at the requested cap.
Its confirmed comment/citation corrections do not change theorem statements
or proofs. The other 1,260 files, cross-batch reconciliation, and explicit
conversion/consequence correspondence obligations remain open. The checked
endpoints below must not be read as an exhaustive source-fidelity certificate.

A separate [formal-correctness review](docs/FORMAL_CORRECTNESS_AUDIT_2026-09-10.md)
has now covered the same 120 files with both participants. It found no
demonstrated formal defect, recording 18 qualified file assessments and
the remaining dependency/source-bridge limitations. This is additional
review evidence, not a new soundness or completeness theorem.

This document states the intended checked scope of the selected ROOT sessions.
The terminal build result is recorded separately in
[verification](docs/VERIFICATION.md). A theorem's actual hypotheses and
conclusion, not its name or this overview, determine its scope.

| Part | Established endpoint | Boundary |
|---|---|---|
| H, Bacon–Dorr named full-F language | Native soundness, sentence-set model existence, closed strong completeness, and countable-domain refinements | Rich variable stock; completeness uses explicit carriers and closed premises/conclusion |
| H, Bacon's full-F minimal language | General-model soundness, original-signature model existence, and global strong completeness, including open formulas and arbitrary premise sets | Full grammar and minimal logical basis; rich variable stock; witnessed closed values; the completeness direction ranges over models on the explicit canonical carrier; premise truth is global (under every typed assignment); arbitrary general sublanguages are not covered |
| H over Bacon's relevant (λI) language | An independently defined λI theory calculus (Definition 9.8 restricted, with the binder-occurrence guard on Gen) with soundness for λI models under the internal conversion clause, original-signature model existence, and global strong completeness for arbitrary well-formed λI premise sets | Minimal logical basis, rich stock and an actual typed assignment; the model class uses the internal (λI-node) βη/α conversion clause; open and distinct: identification with HJ (Definitions 9.9–9.10), conservativity of full H over the λI calculus, the λI printed/exact β correspondence, and completeness for the raw-invariant subclass (internalization of raw conversion); other general sublanguages are not covered |
| Classicism proof theory | Independent presentations and their proved correspondences, including the book's MF+PE and MF+vector-Equivalence presentations | The older Equivalence-rule base is not identical by definition to full-type C; the MF+PE / MF+vector-Equivalence correspondence `book_full_C_presentations_iff` assumes a rich variable stock (`sg_rich G`) |
| Bacon–Dorr relational-type C | BBK-category representation/completeness and action-model single-formula soundness/completeness at arbitrary signatures | R types; explicit carrier/world-label scope; the action-model result is not an infinite-theory compression theorem |
| Bacon's full-type C model existence | Original-signature nontrivial modal models with admissible interpretations satisfying the entire consistent theory | One signature-size hypothesis: the union of the declared names has an injective code into the elements of some ZF set, on an arbitrary name carrier (including the type ZF with set-bounded declared names); the countably declared and ZF-small-carrier scopes are special cases and are retained. Rich stock and full minimal language; open formulas and arbitrary premise sets allowed |
| Generic book modal interpretations | Constructed interpretation for every independent full-minimal modal model; exact future abstraction, naturality, typed-input uniqueness, and signature pullback | No countability, richness, supplied interpreter or extra nonemptiness premise |
| Book full-C generic modal soundness | Every full-C theorem is valid at every world of every nontrivial book modal model under every admissible interpretation; theory derivations are valid at the root when the premises are satisfied there | Rich variable stock; nontrivial class (inhabited domains and a false proposition at every world); the identity/box/H clauses themselves hold in the broader structural class |
| Book full-C modal completeness | Derivability from a theory iff root consequence over the nontrivial class; consistency iff satisfiability | The same declared-name smallness hypothesis; rich stock; premises and conclusion in the full minimal language; local root consequence under every typed assignment |
| Remaining full-C signature size | Signatures whose declared-name union admits no injection bounded by a ZF set are outside the construction | A limitation of the injective syntax-coding method, not a claim that every theory in such a signature lacks a set-valued model; no broader existence theorem or sharp impossibility result is established |

## Completed: original-signature model existence

The audit response strengthens `book_full_C_countable_modal_model_exists`
(described below) to `book_full_C_countable_nontrivial_modal_model_exists`,
with the SAME four premises on Σ, G and S. The stronger conclusion has actual typed assignments
and false propositions at every world, established for the existing
canonical construction rather than assumed of the input theory.
See [the model-class distinction](docs/MODAL_NONTRIVIALITY.md).

On 9 September 2026, `book_full_C_countable_modal_model_exists` passed
Isabelle, together with its 14-endpoint audit. It combines syntactic
consistency recoding, fixed-ambient existence, and semantic signature
pullback to eliminate the original signature's spare-name condition.
The constant-name carrier is arbitrary; only the declared constants at each
type must be countable. Open formulas and infinite premise sets are allowed.

`Bacon_Book_ZF_Countable_Model_Existence.thy` and
`Bacon_Book_ZF_Model_Existence_Audit.thy` are selected in ROOT, and the
earlier fixed-ambient theorem and its audit remain selected too.

The countably declared-signature endpoints remain available with their
original statements, including on non-small name carriers. The
small-carrier theorem `book_full_C_small_carrier_nontrivial_modal_model_exists`
proves existence when the whole name carrier admits an injection into the
elements of an actual ZF set, permitting all names of that carrier to be
declared (countable carriers, powersets of small carriers, `nat set`). The
general endpoint `book_full_C_small_declared_nontrivial_modal_model_exists`
(further below) needs only that the declared-name union admits such an
injection, on an arbitrary carrier, and subsumes both. All routes construct
a model and interpretation in the original signature, with inhabited
domains and a false proposition at every world, and allow open formulas
and arbitrary premise sets.

## Completed: generic full-C soundness and modal completeness (26 September 2026)

The new session `Bacon_Book_ZF_Modal_Soundness`
(`theories/classicism/book/modal_semantics/soundness/`) proves, for every
admissible interpretation of an independent book modal model
(`book_ZF_modal_interpretation`): naturality of denotation under
counterparts, coincidence on free variables, the truth clauses for
implication, quantification, bottom, the defined Boolean connectives,
predicate quantification and top, the Leibniz identity clause
(`truth_leibniz`: identity is value identity, using the model's own
equality operation as separating predicate) and the literal box clause
(`truth_box`), semantic substitution and βη-step invariance in every
context, and worldwise validity of every H axiom and rule. In the
nontrivial refinement (`book_ZF_nontrivial_modal_interpretation`) it
proves worldwise validity of every all-type Modalized Functionality
instance, that Propositional Equivalence preserves validity at every
world, hence `full_C_valid_everywhere`: every `book_full_C_proves`
theorem is valid at every world under every typed assignment. Theory
derivations `book_full_C_theory_derivable Σ G S A` are valid at the root
when S is satisfied at the root (`full_C_theory_valid_at_root`); the
all-worlds invariant is used only for C theorems, never for premises.

`Bacon_Book_ZF_Full_C_Completeness.thy` defines root consequence over
the nontrivial class (`book_ZF_full_C_consequence`). It retains
`book_full_C_theory_derivable_iff_consequence` under four premises:
rich stock, countably many declared constants per type, well-formed
premises S, and a well-formed conclusion A in the full minimal language.
It retains `book_full_C_theory_consistent_iff_satisfiable` under the
first three premises; that equivalence has no conclusion A. Neither
equivalence assumes consistency of S. Its
`book_full_C_theory_complete_from_existence` isolates the common
completeness argument: add the negation of the universal closure of an
underivable conclusion, construct a model, and use the semantic closure
bridge (`truth_universal_closure`) to obtain a counterexample at the root.
`Bacon_Book_ZF_Full_C_Small_Carrier_Completeness.thy` discharges the same
existence premise for ZF-small name carriers, proving
`book_full_C_theory_derivable_iff_consequence_small_carrier` and
`book_full_C_theory_consistent_iff_satisfiable_small_carrier`, together
with `nat set` corollaries. Soundness and satisfiable-implies-consistent
require no countability or carrier-smallness hypothesis. The
soundness/completeness theories were independently reviewed in three
stages before this checkpoint; no correctness repair was required.

At that checkpoint the selected small-carrier and modal-soundness audit
catalogs contained 25 and 37 targets respectively (the soundness catalog
now has 42, and a 31-target declared-names catalog was added later the
same day; see the declared-names section below), and the saved reports
record zero oracles, residual hypotheses and flex-flex pairs for every
target. The four affected sessions built serially with timeout 60; the
complete core-check outcome is recorded in [verification](docs/VERIFICATION.md).
An independent implementation review of the 62 new named mathematical
results identified compatibility and documentation follow-ups; those are
folded in, and a final pass accepted the compatibility proofs and banners
and required one premise correction in this paragraph, which has been
applied.
Neither that review nor these catalogs are an exhaustive source-fidelity
certificate.

The extension to ZF-small declared unions on arbitrary carriers was
completed later the same day by the declared-names endpoints (below). Remaining scope includes the book's
general λ-sublanguages and richer primitive profiles, and the outstanding
source-correspondence obligations. The results retain the explicit
nontrivial class, root consequence, the future-restricted implication
convention, and the literal box `λp.(p =ₜ ⊤)`.

## Completed: ZF-small name carriers of arbitrary cardinality (26 September 2026)

The countable construction displayed on pp.398–400 was generalised. The
enumeration-based Henkin-name embedding is replaced by the locale
`book_ambient_signature` (`Bacon_Book_Ambient_Signature.thy`): each reserve
Bτ − Στ must be infinite and at least as large as the whole declared
signature; half of it (a chosen two-sided injection of ⋃Σ + ℕ) receives the
used Henkin names, the other half stays unused, and both conditions hold
again for the enlarged signature (`book_ambient_henkin_signature_ambient`).
The syntax cardinal bounds behind this are in
`Bacon_Book_Named_Syntax_Cardinal.thy`. `book_full_C_canonical_worlds`
carries the extra cardinal clause; the countable ambient locale is a
sublocale, so the earlier external countable existence statements are
retained. The internal interface changed: `book_ambient_name_map` now
takes the context and is injective only on the Henkin names actually
used, and a countable interpretation does not identify it with the
earlier independently chosen map. On a countable carrier the cardinal
clause is redundant: `book_full_C_countable_canonical_world_iff`
(`Bacon_Book_Full_Canonical_World_Existence.thy`) proves membership in the
full world set equivalent to the earlier displayed conjunction. The HOL-ZF
representation is parameterised by a bounded injective term code
(`book_full_C_coded_frame`, `Bacon_Book_ZF_Coded_Frame.thy`); the
natural-number code is the countable instance, and in any countable
canonical frame `book_countable_class_code` and `book_countable_world_code`
identify its class and world codes with the earlier countable set codes.
The earlier global names `book_ZF_world_code`, `book_ZF_term_class_domain`
and `book_ZF_powerset_image` now live in the coded-frame context; the old
polymorphic powerset-image utility is not recovered.

`book_full_C_small_carrier_nontrivial_modal_model_exists`
(`Bacon_Book_ZF_Small_Carrier_Existence.thy`) then gives original-signature
nontrivial model existence for every full-C-consistent theory over a
ZF-small name carrier (`book_ZF_small_carrier f U`: an injection of the
carrier type into `explode U`), with all constants declared; countable
types, powersets of ZF-small types and in particular the uncountable
carrier `nat set` are proved ZF-small. The completeness and consistency
equivalences follow (`book_full_C_theory_derivable_iff_consequence_small_carrier`,
`..._consistent_iff_satisfiable_small_carrier`, and `..._nat_set` corollaries
in `Bacon_Book_ZF_Full_C_Small_Carrier_Completeness.thy`); the countable
proof was factored through `book_full_C_theory_complete_from_existence`.
Neither theorem subsumes the other: the countable one allows any carrier
type (including ZF) with countably many declared constants per type. Two
new audits (`Bacon_Book_ZF_Small_Carrier_Audit`, 25 endpoints; the extended
`Bacon_Book_ZF_Modal_Soundness_Audit`, 37 endpoints at that checkpoint, 42
after the declared-names extension below) pass with no oracles.

The declared-names generalization below removes the whole-carrier
hypothesis. Remaining: the book's general λ-sublanguages and richer
primitive profiles.

## Completed: ZF-small declared names on an arbitrary carrier (26 September 2026)

`Bacon_Book_ZF_Declared_Names_Existence.thy` proves
`book_full_C_small_declared_nontrivial_modal_model_exists`: rich stock,
`book_ZF_small_declared Σ f U` (an injection `f` of the declared union
⋃τ Σ τ into `explode U`), well-formed premises and full-C consistency give
an original-signature nontrivial model and admissible interpretation
satisfying the premises, on an arbitrary HOL name carrier. Its corollary
`book_full_C_ZF_carrier_nontrivial_modal_model_exists` covers the type ZF
with declared union contained in some ZF set (identity code), extending
the already covered countably declared case on ZF; the small-carrier and
countably declared theorems are re-derived as
`…_from_small_declared` corollaries (subsumption lemmas
`book_ZF_small_carrier_declared`, `book_ZF_countable_declared`), while
their independent proofs are retained. Completeness follows in
`Bacon_Book_ZF_Full_C_Declared_Names_Completeness.thy`
(`book_full_C_theory_derivable_iff_consequence_small_declared`,
`book_full_C_theory_consistent_iff_satisfiable_small_declared`, and
`…_ZF_carrier` corollaries) through `book_full_C_theory_complete_from_existence`.

Construction: the declared names are recoded into `('c + nat) × bool` as
before, but the ambient signature is only the declared-or-reserve name set
K = (Inl ` ⋃Σ ∪ range Inr) × UNIV; the tagged carrier code is injective on
K and bounded, so terms admitted by K are cardinally bounded and receive a
total code injective on those terms. To make this possible the coded-frame
locales (`book_full_C_coded_frame`, `book_coded_ambient_signature`) now
assume a term code that is total, bounded, and injective on terms admitted
by the ambient signature B, rather than globally injective; the class
decoder is `inv_into` on admitted term sets, and the Replacement-image,
range, inverse, assignment-decoding, closed-value and reindexed-structure
lemmas carry an explicit admitted-pair or world guard (all rooted worlds
qualify). External endpoint statements and the countable coding equations
are unchanged; the independent model and interpretation predicates are
untouched. New audit `Bacon_Book_ZF_Declared_Names_Audit` (31 endpoints);
the modal soundness audit now has 42 endpoints; every affected report was
re-exported and checked (zero oracles, residual hypotheses, flex-flex).
The design was independently reviewed before implementation and the
result audited afterwards; the requested documentation-level changes are
applied.

Remaining signature size: declared unions with no injection bounded by a
ZF set are outside this construction. That is a limitation of the
injective syntax-coding method, not a proof that every theory in such a
signature lacks a set-valued model (the model's constant interpretation
need not be injective). Theorem 18.4 is printed without a cardinality
qualification; its displayed proof is countable; declared-name smallness,
the cardinal reserve and the bounded code are formalization additions.
The cardinal invariant and the carrier hypothesis are this repository's,
not Bacon's, whose statement of Theorem 18.4 is unqualified but whose
displayed proof is countable.

## Completed: Bacon's relevant (λI) language (26 September 2026, latest)

Session `Bacon_Book_Lambda_I_Development` (`theories/base/book_lambda_I/`,
72 theories) treats the relevant language of Definition 9.2 as an instance
of the general λ-sublanguage clauses of Definition 9.1
(`book_lambda_I_general_lambda_language`): every abstraction binds a
variable that occurs free in its body. The λI theory calculus
`book_lambda_I_derivable` is an independently defined inductive relation:
the rules of Definition 9.8 restricted to λI formulas, with exact-capture
β and η, and binder Gen carrying the occurrence guard `n ∈ FV(B)`
(otherwise ∀n.B is not a λI formula). The constant-form Gen of the source
is derived and the two presentations are proved equivalent
(`book_lambda_I_presentations_iff`). Internal conversion
`book_lambda_I_conv` is the finite chain of β/η steps whose nodes are λI
terms of the signature; α-conversion between λI terms is internal
(`book_lambda_I_alpha_conv`) and internal conversion transports
derivability. λI models (`book_lambda_I_model`) are Definition 14.13 read
through Proposition 9.1: an applicative structure with a denotation that
is invariant under internal conversion, the minimal-basis truth clauses
and a false proposition; every full minimal model restricts to one, and
the calculus is sound for all of them.

Completeness replays the H pipeline inside the fragment: generalization and
variable substitution split on the occurrence of the substituted variable,
retraction and signature conservativity preserve the Gen guard, the Henkin
stages declare witness names only for closed λI predicates, the
inhabitation constant is the witness of λx.∀X.(X x → X x), and the term
model is built on internal conversion classes of closed λI terms
(`book_lambda_I_henkin_conversion_model`). The endpoints are
`book_lambda_I_canonical_model_existence` (Theorem 15.3, λI instance,
original signature, open formulas and arbitrary premise sets),
`book_lambda_I_canonical_countermodel_with_assignment`, and
`book_lambda_I_canonical_strong_completeness` (Corollary 15.2, λI
instance: derivability from S iff consequence over every λI model on the
canonical carrier). Audit `Bacon_Book_Lambda_I_Audit` (73 endpoints,
`book-lambda-I-audit.txt`).

Scope: minimal logical basis, rich variable stock for the main endpoints,
and the model class requires an actual typed assignment. Boundaries, each
open and distinct: identification of the independently defined λI calculus
with HJ, the least relevant-language logic of Definitions 9.9–9.10 (its
substitution closure is not proved); conservativity of full H over the λI
calculus, that is identification with the restriction of H to λI formulas
(only the one-way embedding `book_lambda_I_derivable_embeds` is proved);
the λI printed/exact β correspondence (the calculus uses exact-capture β
only); and internalization of raw βη-conversion between λI endpoints (a
typed Church–Rosser argument the repository does not have), so completeness
is stated for the internal-clause model class and completeness for the
raw-invariant subclass is open. A separate regression session
`Bacon_Book_Lambda_I_Regressions` exhibits an actual λI model with a typed
assignment satisfying ⊥ → ⊥ and proves {⊥ → ⊥} λI-consistent, using the
auxiliary-bridge full minimal model existence theorem. The native
proof-dependency policy checks that the λI consistency, witness, valuation
and completeness roots use no full-H proof judgment or full-model class.
See the [source guide](docs/SOURCE_CORRESPONDENCE.md) and the audit theory
`Bacon_Book_Lambda_I_Audit`.

## Completed: generic interpretation existence

`book_ZF_modal_model.generic_interpretation_exists` constructs an admissible
interpretation for every model satisfying the independent modal-model
predicate, in the full minimal language. Typed K/S abstraction elimination
produces a value in the chosen function domain, and that value is proved
identical to Definition 17.13's entire future Lambda graph. Evaluation
commutes with counterparts; the earlier uniqueness theorem applies on typed
terms and assignments.

No canonical construction, countability, rich variable stock, supplied
interpreter, full function space, or additional nonemptiness assumption is
needed. The model and interpretation definitions are unchanged. A separate
15-endpoint audit checks the construction and its ingredients. This is the
interpretation-existence component of Theorem 17.1 for the independent
full-minimal modal-model class, not generic soundness or completeness.

Other preserved theories not reached by ROOT are not covered by a successful
default build. Run `python3 tools/check_release.py --inventory` to see the
actual source-closure inventory rather than treating every .thy file as checked.

## Source qualifications that must remain visible

- `book_ZF_modal_model` retains the broad structural conditions. It admits
  an inhabited all-true model, as the maintained singleton regression proves.
  It cannot characterize consistency merely by existence of a model.
- `book_ZF_nontrivial_modal_model` adds inhabited domains and a false
  proposition at EVERY world. This is an explicit source-motivated
  strengthened subclass, not a literal transcription of additional
  printed clauses of Definition 18.1. The canonical construction establishes both extra conditions. Generic
  soundness for this class is proved without a cardinality restriction;
  model existence and the consequence/consistency equivalences are proved
  for every signature whose declared-name union is bounded by a ZF set,
  on arbitrary carriers (subsuming the countably declared and ZF-small
  whole-carrier scopes). The reverse consistency implication remains
  false for the unchanged broad structural class.

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
