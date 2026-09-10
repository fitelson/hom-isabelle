# Partial source-fidelity audit: 10 September 2026

## Coverage and limits

The subsequent [formal-correctness consensus audit](FORMAL_CORRECTNESS_AUDIT_2026-09-10.md)
completed a separate two-sided review of these same 120 files. Its paired
revision/coverage record and qualifications are reported separately; the
source-fidelity findings and remaining obligations below remain in force.

Fable 5.1 and Astra completed an adversarial review of **120 of the 1,380
theory files**, in four batches of 30, 36, 44 and 10 files. The run stopped
at the requested cap. These are the first files in the prepared review
order, not the first 120 alphabetically and not a random sample. All 120
belong to the selected build. They contain 18,768 physical source lines in
the reviewed snapshot, before the comment corrections below.

The review compared syntax, proof rules, semantic interfaces and supporting
proofs with Bacon's book and the 1 July 2022 Bacon–Dorr paper. The file
[manifest](../verification/source_fidelity/2026-09-10-first120.json) records
every reviewed path, its frozen-source hash, and each participant's final
assessment. It also identifies all 1,260 deferred files. The snapshot
included the earlier audit repairs on top of commit `d8cee60`; it was not
just that commit. Raw model journals and local source PDFs are not included.

The final classifications were 10 source matches, 32 qualified source
correspondences, 77 reviewed auxiliary files and one source-problem file.
These are file classifications, not counts of correct or incorrect
theorems. An auxiliary file can have a false explanatory comment, as one
did here. Both participants reviewed every listed file, but did not
independently re-derive every imported dependency outside their batches.

**The other 1,260 files and whole-development dependency reconciliation
remain unaudited by this run.** The review did not discover a failed
derivation in its inspected proof chains. It did discover documentation
errors and substantive correspondence obligations. Agreement on this
assessment is not a certificate that the entire repository exactly
formalizes its sources. Isabelle kernel checking and source fidelity
are distinct forms of evidence.

## Corrections made after the review

No definitions, theorem statements, proof steps, assumptions or session
selection were changed in response to this capped review.

| Location | Finding and correction |
|---|---|
| `Bacon_Parametric_Fresh_Witness_Elimination` | The comment wrongly excluded every undeclared-witness axiom from guarded assumptions. A vacuous binder can leave a constant-free formula. The corrected comment distinguishes actual syntactic occurrence from the chosen witness name; the elimination theorem is unchanged. |
| `Bacon_Source_Local_Cut` | The replacement premise requires every member of T to be derivable from S, hence well-formed. The comment now allows unused ill-formed members only in S, while allowing both sets to be infinite. |
| `Bacon_Parametric_Set_Soundness` | The finite-proof discussion precedes Theorem 15.2 on book p.318; Theorem 15.2 itself is the deduction theorem. The comments also distinguish at-an-assignment local soundness from Theorem 15.1's model-validity statement. |
| `Bacon_Parametric_Local_Quantifiers` | Replaced an accidental internal identifier in the subsection heading with readable prose. |
| `Bacon_Parametric_Local_Derivability` | Made explicit that footnote 64 discusses formula sets, and that local assumption/theorem/MP consequence is not unrestricted H-theory closure on open premises. |
| `Bacon_Parametric_BBK_Semantics` | Removed the unsupported implication that foreign-constant conversion paths demonstrate different endpoint equivalences. Recorded the precise unproved converse instead. |
| `Bacon_Deduction` | Made the primitive-basis qualification explicit at the foundational calculus, directing source claims to the separate source-language translations. |

The manifest retains the original findings and hashes rather than silently
relabelling the repaired files as independently re-reviewed. Subsequent
build results check the edited Isabelle text, not a second source audit.

## Reconciled qualifications

**Logical primitives.** The constructor calculus treats implication as
primitive. The paper defines it by λpq.¬p ∨ q. Their direct identification
is not harmless in H, where truth equivalence does not imply identity of
propositions or higher-order objects. The reviewers gave a mathematical
separating interpretation; they did not construct an Isabelle instance of
that countermodel. Their argument establishes failure of a naive direct
vocabulary correspondence, not by itself a general proper-sublogic theorem.

The later reviewed files contain the actual first-class source language,
source-defined implication, and explicit translations. In particular,
`paper_closed_set_derivable_iff` compares source sentence-set consequence
with the translated target consequence under a rich variable stock. This
is not a claim that arbitrary constructor terms are definitionally the
printed terms, nor a two-sided model isomorphism. We therefore preserve
the constructor development rather than replace it or add an identity axiom.

**Renaming and Existence.** The initially questioned source-model renaming
field is derived from the weaker structure by
`paper_db_structure_is_model` in `Bacon_Source_BBK_Renaming_Derived`.
It is not an outstanding missing assumption proof for that interface.
The target's `IndividualExistence` constructor is handled by a derived
source theorem in the reverse correspondence. The native named H calculus
has the ten Figure 2 constructors. We do not identify the finite-context
presentation literally with H⁻.

**Types and local consequence.** These reviewed H files use full F types.
The paper defaults to R and also discusses F. R recursively restricts
arrow codomains, excluding e as an arrow codomain. An F result is not
automatically an R result; this review proves no F-over-R conservativity.
The project's local consequence uses assumptions, H theorems and MP.
For unrestricted open premises this differs from closure under all
H-theory rules. Theorem 3.2's sentence-set model-existence statement and
footnote 64's formula-set discussion must remain distinct.

**Abbreviations and binding.** The named calculus reads PC with the paper's
declared connective abbreviations, consistent with its own Existence
derivation. The audit did not establish equivalence to every stricter
primitive-only reading of PC. The β insertion condition is internal to the
redex; the surrounding formula context may bind free variables as the
paper expressly allows. α-invariance is derived through the representation
and conversion results, not added as a semantic identity assumption.

## Remaining work

1. Finish the other 1,260 theory-file reviews, including the model-existence,
   completeness, category and action-model developments not covered by
   these four batches. Retain exact file coverage and publication locators.
2. Reconcile imports across batches and check the hypotheses of every
   advertised endpoint. Selected build membership alone does not discharge
   a source-correspondence obligation.
3. Prove the raw-to-language-restricted βη bridge on typed Σ-endpoints,
   or isolate the exact source condition another way. Only the
   language-restricted-to-raw direction is supplied in the inspected interface.
   A foreign-constant expansion alone is not a counterexample. A typed
   Church–Rosser argument with signature preservation is a proposed route.
4. Formalize source-side Gen/Inst admissibility for sentence premises, or
   give a complete checked bridge to the appropriate H-theory closure.
   Target guarded admissibility and closed-set correspondence are useful
   ingredients, but closed conclusions alone do not handle every open
   intermediate formula. The reviewers supplied a mathematical deduction
   argument, not an additional kernel-checked theorem.

If a conversion condition were weaker than the source condition, the
encoded model class could be broader. Soundness already proved over the
broader class would still hold on the source subclass, subject to the
assignment correspondence. Existence in the broader class alone would
not establish source-model existence. The audit does not establish that
the classes differ; this is why the bridge remains an explicit obligation.

The [contributor guide](../CONTRIBUTING.md) turns these into bounded tasks.
No new modal-model result follows from this review. The earlier
[nontriviality clarification](MODAL_NONTRIVIALITY.md) remains separate.

## Post-correction verification

The maintained serial check passed with Isabelle2025-2 in 4 minutes
33 seconds, selecting 30 sessions and 1,371 theory files. This was an
incremental rebuild of affected dependencies, not a fresh-cache benchmark.
All 29 lexical-policy tests and source-boundary/packaging checks passed.
Comparing the seven edited theories with the frozen snapshot after removing
their document text/headings found no formal-content change.

The native graph refresh and dependency-policy checks passed, retaining
31,855 nodes and 2,323,506 edges. All 23 freshly exported theorem-audit
reports matched the repository's stored checksums. The documentation links and 1,380-path
review/deferred partition were checked. The presentation and three-page,
four-up handout were recompiled and visually inspected, with all 16 URI
links preserved. Their statistics now include the 23 added comment lines.
No upload, commit or push was performed during this response.
