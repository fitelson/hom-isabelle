# An invitation to finish the formalization

This repository is offered to scholars who would like to work on the formal
foundations of higher-order metaphysics. Contributions may be mathematical,
formal, or expository. Small, well-verified changes are welcome.

This guide concerns the core. Application-specific work has its own guide:
see [Applications](Applications/README.md) and
[Goodman's contributor projects](Applications/goodman-isabelle/CONTRIBUTING.md).
Keep application sessions out of the core ROOT and verify each project
with its own checker, serially.

The [standalone repository](https://github.com/fitelson/bacon-dorr-isabelle)
is private as of 10 September 2026. Ask Branden for collaborator access
with your GitHub username if you do not already have it.

Please start by [opening an issue](https://github.com/fitelson/bacon-dorr-isabelle/issues) describing the source statement, its exact
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

### 2. Prove one generic connective truth clause

Start with `book_ZF_if_future_value` or `book_ZF_all_value` in
[Bacon_Book_ZF_Model_Operations.thy](theories/classicism/book/modal_semantics/hol_zf/Bacon_Book_ZF_Model_Operations.thy),
`implication_member_at` or `universal_member_at` in
[Bacon_Book_ZF_Model_Operator_Restriction.thy](theories/classicism/book/modal_semantics/hol_zf/Bacon_Book_ZF_Model_Operator_Restriction.thy),
and `denote_logical`, `denote_application`, `denote_abstraction` in
[Bacon_Book_ZF_Interpretation_Clauses.thy](theories/classicism/book/modal_semantics/interpretation/Bacon_Book_ZF_Interpretation_Clauses.thy).

Choose just implication or universal quantification. Derive its truth-at-w
iff statement for an admissible generic interpretation using
`book_ZF_truth_at` from
[Bacon_Book_ZF_Model_Truth.thy](theories/classicism/book/modal_semantics/interpretation/Bacon_Book_ZF_Model_Truth.thy).
For implication, the target relates truth of `book_imp A B` at w to truth
of A and B at w. For `book_all G n A`, the target quantifies the values of
the variable n in the domain at w. Retain world, language and assignment
guards, and justify assignment updates. The existing operation-value
lemmas alone are not yet these interpreted-formula truth clauses.

Completion means a named theorem, its exact hypotheses, a source comment
for Definitions 17.13 and 18.1, and audit coverage. Use the model-class
qualifications in [STATUS.md](STATUS.md): the source-directed class is
`book_ZF_nontrivial_modal_model`, which extends the unchanged
`book_ZF_modal_model` with inhabited domains and a false proposition at
every world. Record if a particular truth clause needs only the weaker
predicate; do not silently add or remove these conditions. Focused check:

```sh
isabelle build -j 1 -d . -o timeout=60 -o export_theory=true Bacon_Book_ZF_Modal_Interpretation
```

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

### 4. Supply the modal soundness lemma for one H rule

After the needed truth clause in item 2, choose the UI case of the book's
Chapter 5 calculus. Start with `book_theory_derivable.UI` in
[Bacon_Book_Theory_Derivation.thy](theories/base/book_models/Bacon_Book_Theory_Derivation.thy)
and the UI case of `book_theory_soundness` in
[Bacon_Book_Theory_Soundness.thy](theories/base/book_models/Bacon_Book_Theory_Soundness.thy).
The latter is already proved for general models; it is not a theorem
about the modal-model interface merely because both developments use H.

Prove that the UI instance is true in the intended generic modal model,
with an admissible interpretation and typed assignment. Record whether
the weaker modal predicate suffices or the stronger source-directed
assumptions are used. Finish with one named modal validity lemma, a
Chapter 5 source locator, all typing guards, and an audit entry. Do not
claim the entire H induction, full-C soundness, or completeness from
this single case. Focused check:

```sh
isabelle build -j 1 -d . -o timeout=60 -o export_theory=true Bacon_Book_ZF_Modal_Interpretation
```

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

Original-signature model existence for countably declared signatures now
also has the stronger endpoint `book_full_C_countable_nontrivial_modal_model_exists`
in [Bacon_Book_ZF_Countable_Nontrivial_Existence.thy](theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Countable_Nontrivial_Existence.thy).
It constructs inhabited domains at every type and world and a proposition
false at each world, as well as an admissible interpretation satisfying
the original consistent theory. The canonical and fixed-ambient stronger
endpoints are ingredients of this result. Generic interpretation existence
already holds for the weaker structural class and hence applies to this
subclass. See [STATUS.md](STATUS.md) for exact hypotheses and source
qualifications; none of these constructions is a first-contribution TODO.

The larger program still includes generic full-C soundness and the final
modal consequence theorem. Uncountably declared signatures require a
separate argument: finite compression of one formula is not compression
of an arbitrary theory. Other substantive source-scope questions include
the book's general λ-sublanguages and richer primitive profiles, and the
paper's finite presentations. Propose a precise statement before beginning
one of these larger projects.

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
