# An invitation to finish the formalization

This repository is offered to scholars who would like to work on the formal
foundations of higher-order metaphysics. Contributions may be mathematical,
formal, or expository. Small, well-verified changes are welcome.

Please start by opening an issue describing the source statement, its exact
scope, and the proposed change. Existing theorem names are useful anchors,
not evidence that a broader source result has already been formalized.

## Suggested projects

### 1. Completed: original-signature modal model existence

The previously open proof in
`theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Countable_Model_Existence.thy`
is now checked (9 September 2026). Its ingredients are syntactic consistency
recoding, the fixed-ambient existence theorem, and generic semantic signature
pullback.

The theorem supplies a model and an admissible interpretation for arbitrary constant-name
carriers with countably many declared constants per type, with no supplied
model or original spare-name premise. It and its audit are selected in ROOT.
Open formulas and infinite premise sets are allowed. This is still not
unrestricted full C completeness. The next item is also completed; project 3
and the later source-review projects remain open.

### 2. Completed: generic interpretation existence

`Bacon_Book_ZF_Generic_Interpretation_Existence.thy` now constructs an
interpretation for every `book_ZF_modal_model` and proves all the independent
`book_ZF_modal_interpretation` clauses. It uses typed K/S abstraction
elimination and proves equality with the required whole future Lambda graph.

No supplied interpreter, full function space, countability, richness or
additional nonemptiness axiom is assumed. Assignment guards are preserved,
including in degenerate cases. Naturality and the existing typed-input
uniqueness are covered by the 15-endpoint existence audit. This does not
prove generic soundness.

### 3. Full-type C: soundness and final modal completeness

Build on the two completed existence constructions. Derive generic soundness,
then formulate and prove
the exact countermodel/completeness statements at their source scope.
Treat arbitrary uncountably declared signatures as a separate substantive
obligation: finite compression of one formula is not compression of an
arbitrary theory.

Global validity under Equivalence is not the closure of the true sentences
of a single pointed model under that rule. Any rerooting or model-class
argument must be supplied explicitly.

### 4. Source correspondence and readable exposition

Choose one theorem or definition, compare it with the identified source
edition, and explain the match in a short Unicode theory comment. Record
every extra hypothesis or correction. Particularly useful projects include
the full-F/R boundary, partial assignments, and the documented implication
clause qualification.

Completion means a source locator, an exact theorem link, an explanation
that can be followed without internal project jargon, and a passing build
if code was changed.

### 5. Broader source scope and presentation audit

The book's arbitrary general λ-languages and richer primitive profiles are
not all covered by the minimal-language completeness theorem. The paper's
finite presentation claims also require their own precise correspondence
review. Identify the exact missing statement before generalizing a theorem.

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
