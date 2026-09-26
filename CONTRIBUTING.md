# An invitation to finish the formalization

This repository is offered to scholars who would like to work on the formal
foundations of higher-order metaphysics. Contributions may be mathematical,
formal, or expository. Small, well-verified changes are welcome.

This guide concerns the core. Application-specific work has its own guide:
see [Applications](Applications/README.md) and
[Goodman's contributor projects](Applications/goodman-isabelle/CONTRIBUTING.md).
Keep application sessions out of the core ROOT and verify each project
with its own checker, serially.

The standalone repository is
[fitelson/hom-isabelle](https://github.com/fitelson/hom-isabelle).
Use its issues and pull requests to propose and review contributions.

Please start by [opening an issue](https://github.com/fitelson/hom-isabelle/issues) describing the source statement, its exact
scope, and the proposed change. Existing theorem names are useful anchors,
not evidence that a broader source result has already been formalized.
Submit the agreed contribution as a pull request, including its source
locator, exact scope and relevant verification results.

## Choose a bounded first contribution

Start with the [worked existing proof](docs/READING_GUIDE.md#one-small-checked-proof).
Then choose one item below and agree its statement in an issue. The formal
items are research tasks, not promises that a particular proof method works.
Each has a smaller deliverable than a completeness theorem.

### 1. Explain one quantifier rule and its consequence boundary

Start with `paper_named_H.Gen` and `paper_named_derivable` in
[Bacon_Source_Named_H.thy](theories/base/source_vocabulary/Bacon_Source_Named_H.thy),
and Figure 2 and the H-theory discussion, pp.7–8 of the 1 July 2022 paper
draft. The source supplies the H rules; `paper_named_derivable` is the
project's separately defined local consequence relation, not a transcription
of a displayed source definition. The rules already exist; the open
contribution is an annotated worked inference for the reading guide.

Translate the encoded rule from P → Q to P → ∀x.Q, displaying the type
condition and the restriction that x is not free in P. Explain why
`paper_named_derivable`, whose constructors are Assumption, Theorem and MP,
does not thereby acquire an unrestricted rule from an assumed Q to ∀x.Q.
Finish with a source locator, the exact constructor names, and a
line-by-line account of the guards. Do not advertise the existing rule as
a missing lemma or silently assert an underivable instance has a proof.

This is suitable for a contributor new to Isabelle. Its focused check is:

```sh
isabelle build -j 1 -d . -o timeout=60 -o export_theory=true Bacon_Source_Vocabulary_Development
```

### 2. Explain a proved generic connective truth clause

The implication and universal-quantifier clauses are already proved as
`book_ZF_modal_interpretation.truth_imp` and `truth_all` in
[Bacon_Book_ZF_Modal_Truth_Clauses.thy](theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Modal_Truth_Clauses.thy).
Choose one and contribute a worked explanation connecting the operation
clause to interpreted-formula truth. Display every world, language and
assignment guard; for quantification, explain the typed assignment update.
For implication, retain the future-restricted complement convention.
Completion means a source-located explanation whose stated hypotheses
match the existing theorem. This is an exposition task, not a missing
truth lemma or a new soundness claim.

### 3. Reroot one modal model at a future world

Start with `book_ZF_nontrivial_modal_model` in
[Bacon_Book_ZF_Nontrivial_Model.thy](theories/classicism/book/modal_semantics/hol_zf/Bacon_Book_ZF_Nontrivial_Model.thy)
and its base `book_ZF_modal_model` in
[Bacon_Book_ZF_Modal_Model.thy](theories/classicism/book/modal_semantics/hol_zf/Bacon_Book_ZF_Modal_Model.thy),
the all-world operation-membership theorems in
[Bacon_Book_ZF_Model_Operator_Restriction.thy](theories/classicism/book/modal_semantics/hol_zf/Bacon_Book_ZF_Model_Operator_Restriction.thy),
and `generic_interpretation_natural` in
[Bacon_Book_ZF_Generic_Interpretation_Existence.thy](theories/classicism/book/modal_semantics/interpretation/Bacon_Book_ZF_Generic_Interpretation_Existence.thy).

The proposed deliverable is a future-cone restriction with a chosen
accessible world as its new root. Specify the restricted frame, domains,
counterparts and new root denotations of constants; prove that the result
satisfies the intended model predicate and that interpretation of typed
terms is preserved. Target the stronger class and preserve its worldwise
inhabited-domain and false-proposition requirements. Those requirements
are now explicit, but the construction of a rerooted model is still open;
neither generic interpretation existence nor nontrivial model existence
already supplies this transport theorem.

This is a bounded structural prerequisite, not a proof of Equivalence
soundness. In particular, global validity under Equivalence is not closure
of the true sentences of one pointed model under that rule. Completion
requires explicit modelhood and truth-transport statements, all root and
future-cone guards, a source explanation, and audited proofs. Focused check:

```sh
isabelle build -j 1 -d . -o timeout=60 -o export_theory=true Bacon_Book_ZF_Modal_Interpretation
```

### 4. Explain the universal-instantiation case of modal H soundness

`UI_valid` and the full H induction are already proved in
[Bacon_Book_ZF_Modal_H_Soundness.thy](theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Modal_H_Soundness.thy).
Write a worked derivation from the arbitrary-predicate quantifier clause,
showing that the argument denotes an element of the current typed domain
and that application evaluates at the appropriate pair. Explain why the
displayed structural interpretation guards suffice. Completion means an
accurate annotated proof and a Chapter 5/Chapter 18 source locator; do not
present this existing result as an open formalization problem.

## Completed work and larger open problems

### Complete the source-fidelity audit

The [10 September partial audit](docs/PARTIAL_SOURCE_AUDIT_2026-09-10.md)
reviewed 120 of 1,380 theory files with Fable 5.1 and Astra, then stopped at
the requested cap. **The remaining 1,260 files and cross-batch dependency
reconciliation are open contributor work.** The linked manifest records
the exact reviewed and deferred paths. This is distinct from the selected
Isabelle build, and a reviewed qualification is not necessarily a defect.

The same 120 files also received a separate
[formal-correctness review](docs/FORMAL_CORRECTNESS_AUDIT_2026-09-10.md).
It records no demonstrated formal defect, but retains scope/dependency
qualifications; the comment that understated a substitution premise has
since been corrected to match the all-index hypothesis.
Continuation should track fidelity and correctness coverage separately
for the remaining files rather than treat either review as a substitute
for the other or for kernel checking.

Choose one deferred file or a small connected group. Compare every
substantive definition and result with the cited publication, checking
logical primitives, F/R types, binding, signature and carrier hypotheses,
and local versus theory consequence. Record the source page/result or the
explicit auxiliary role of each result. Follow crucial imports without
silently counting their entire files as reviewed. Completion requires an
evidence-backed assessment, explicit remaining dependencies, and checked
repairs where necessary, not merely a passing build or another model's assent.

Two bounded mathematical follow-ups from the reviewed material are:

- In `Bacon_Parametric_BBK_Semantics`, prove raw βη equivalence implies
  language-restricted equivalence when both endpoints are well-typed
  Σ-terms, or establish the exact alternative source bridge. The checked
  direction is currently language-restricted to raw. A suitable
  Church–Rosser argument must retain typing and signature preservation.
- For `paper_global_derivable`, prove Gen/Inst admissibility with sentence
  premises and the correct freshness conditions, or complete the checked
  correspondence with H-theory closure. Start from `paper_global_derivable`
  and `paper_global_derivable_finite_support` in
  [Bacon_Source_Local_Deduction.thy](theories/base/source_vocabulary/Bacon_Source_Local_Deduction.thy).
  The **existing constructor-side comparison lemmas** `pH_set_Gen` and
  `pH_set_Inst` are in
  [Bacon_Parametric_Local_Quantifiers.thy](theories/base/parametric_signature/Bacon_Parametric_Local_Quantifiers.thy).
  The contribution is the source-side admissibility result or the checked
  correspondence needed for open intermediate formulas, not reproving those
  existing lemmas. If the chosen route needs a source-side local deduction
  lemma, proving it is part of this task; no such starting theorem is supplied
  here. Do not generalize arbitrary open assumptions unrestrictedly or omit
  the rich-stock and freshness guards.

Both tasks need a precise statement, source explanation, maintained audit
coverage and serial verification. The partial audit's mathematical sketches
are not additional Isabelle theorems.

Original-signature nontrivial model existence, generic full-C soundness,
and the root-consequence and consistency equivalences are established
for countably declared signatures on arbitrary name carriers. A second
route now covers ZF-small whole name carriers with no restriction on the
number of declared constants, including `nat set`. Both routes retain
rich stock, the full minimal language and the explicit nontrivial model
class, and allow open formulas and arbitrary premise sets. Soundness
itself has no carrier-cardinality restriction. Items 2 and 4 above are
therefore exposition tasks, and item 3's rerooting construction was not
needed for soundness, though it remains an open structural exercise.
These completed endpoints are not first-contribution TODOs; see
[STATUS.md](STATUS.md) for their verification evidence and remaining
compatibility work.

The extension to ZF-small declared unions on arbitrary carriers is now
completed by the declared-names endpoints
(`Bacon_Book_ZF_Declared_Names_Existence.thy`,
`Bacon_Book_ZF_Full_C_Declared_Names_Completeness.thy`): only an injective
code of the declared-name union into the elements of a ZF set is assumed,
on an arbitrary carrier, and the earlier countable and whole-carrier
results follow. Declared unions with no ZF-bounded injection are outside
the injective syntax-coding construction; whether every theory in such a
signature has a set-valued model is not settled either way.

### Three larger open projects

With the extension to ZF-small declared unions completed (larger signatures remain open, as stated above), three substantive projects remain.
Each is research, not a filled-in template; agree a precise theorem
statement in an issue before starting, and preserve the distinctions
between the book's full-type C and the paper's relational R, HOL and
HOL–ZF, root and all-world consequence, and the structural and nontrivial
model classes. The future-restricted implication and literal box
`λp.(p =ₜ ⊤)` remain explicit conventions.

**1. General λ-sublanguages (Bacon, Chapter 9).** The general H results
are proved for the full minimal language; the relevant (λI) language has
its own internal-class treatment (below); the general-sublanguage problem
remains. Definition 9.1 is already
transcribed (`book_general_lambda_language`, with the full language as an
instance) and Definition 14.13's interpretation interface exists
(`book_general_interpretation`). Missing are the general higher-order
theory and logic of Definitions 9.8–9.10 restricted to a sublanguage,
general models of the sublanguage (Definition 15.1 over such an
interpretation), soundness, and model existence/completeness for closed
premises. A design for this was drafted and independently reviewed
(the records are kept by the maintainer); the decisive obstacle is that
α-conversion inside a proper sublanguage can fail to be derivable from
literal β/η steps (the applicative-plus-identity language gives a concrete
counterexample, while the λI development proves exactly such derivability
in another proper sublanguage), so the calculus's treatment of α-variants and of the
negation encoding must be settled before any Henkin argument. The
relevant (λI) language of Definition 9.2 is treated separately
(`theories/base/book_lambda_I/`, session `Bacon_Book_Lambda_I_Development`):
its calculus, internal-conversion models, soundness, and original-signature
model existence and completeness are checked, under the minimal logical
basis, a rich variable stock for the main endpoints, and an actual typed
assignment required of every model. What that treatment leaves
open, and what a general-sublanguage project would have to settle, are
four distinct questions: identification of the independently defined λI
calculus with HJ (the least relevant-language logic of Definitions
9.9–9.10); conservativity of full H over the λI calculus (identification
with the restriction of H to λI formulas); the λI printed/exact β
correspondence; and completeness for the raw-invariant model subclass (the
internalization of raw βη-conversion between λI endpoints).

**2. Richer primitive profiles.** All modal results use the minimal
primitive basis (implication and typed universal quantification).
Definition 15.1 lists the book's full logical signature, and §9.4 adds
hatted quantifiers for general languages. The preserved conjunction and
disjunction developments under `theories/base/book_models/`
(`Bacon_Book_Primitive_Conjunction_*`, `…_Disjunction_*`) show the
encoding/decoding pattern for one extra primitive at the H level (note that
four disjunction theories, `Bacon_Book_Disjunction_{Decoded_Model,
Decoding_Environment, Encoding_Environment, Model_From_Background}.thy`, are
preserved but outside the checked ROOT closure); the
project is to state and prove soundness and completeness for a richer
profile, first for H and then for the modal C endpoints, without changing
the independent model predicates.

**3. A Kirchner-style shallow embedding.** This repository is a deep
embedding: syntax, calculi and models are inductive objects, and
metatheorems are proved about them. The complementary approach of
Benzmüller and Kirchner embeds higher-order modal logic shallowly in HOL,
so that object-level reasoning runs on Isabelle's own automation. The
project is to build a shallow embedding of the book's full-type Classicism
(worlds, the modalized domains and the literal box), reprove a selection of
the object-level theorems checked here (for example the modal K, T and 4
facts and the SL_t → □Actuality argument, which the core's relational
C calculus can express), and state precisely how the shallow validity notion relates
to this repository's root consequence over the nontrivial class. The
value is a second, independently checkable route to the same object-level
results and much faster experimentation; it is not a replacement for the
metatheory proved here, and the two must not be silently identified.

For a new theory file, ensure ROOT or a selected theory imports it before
treating a focused build as verification. Add the relevant theorem to the
appropriate audit catalog. The [verification guide](docs/VERIFICATION.md)
explains selected-source coverage. Run the complete check before submitting
a formal change; the focused commands above are development checks, not
release certificates.

## Working rules

1. Use Isabelle2025-2. Run `./check_isabelle.sh` before and after a change.
2. Keep Isabelle builds, exports, and graph extraction serial. Split a slow
   argument into smaller named lemmas; do not raise the 60-second session
   limit to hide proof growth.
3. No `sorry`, admitted facts, new oracles, or unchecked axioms.
4. Use Bacon's and Bacon–Dorr's notation and terminology in explanatory text.
   State types, freshness, signature, and model assumptions explicitly.
5. Preserve the distinction between a conditional lemma and a constructed
   instance. Do not import a stronger calculus to prove a weaker claim
   without an established reduction.
6. Include source correspondence, tests, and audit coverage in a pull request.
   Explain separately what Isabelle checked and what required human judgment.
7. Credit collaborators and disclose substantial AI assistance. AI suggestions
   are not proof certificates or substitutes for source comparison.

The BSD-2-Clause license permits reuse, modification, and redistribution.
Please retain the required notices.
