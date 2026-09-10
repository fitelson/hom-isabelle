# Formal-correctness audit of the 120 source-reviewed theories

## Result and exact scope

Fable 5.1 and Astra 6 completed a separate adversarial correctness review
of the same 120 theory files covered by the
[source-fidelity audit](PARTIAL_SOURCE_AUDIT_2026-09-10.md). All four batches
(30, 36, 44 and 10 files) reached agreement on their assessments. Both final
participants supplied complete per-file coverage. The final batch finished
on 10 September 2026 at 15:04:35 local time, and the queue stopped.

The agreed result is **no demonstrated formal defect in the reviewed
definitions, statements and proof chains**, with explicit qualifications.
The file classifications are 102 REVIEWED and 18 QUALIFIED, with no PROBLEM,
UNREVIEWED or BLOCKED entries. These labels record review, not new Isabelle
theorems or a guarantee of universal correctness.

The [paired coverage record](../verification/formal_correctness/2026-09-10-first120.json)
identifies every path, each run's frozen hash, and both participants'
assessments for both fidelity and correctness. The sets of 120 paths agree
exactly. Seven files received documentation-only corrections between the
runs. The coordinator compared their formal text after removing document
commands; the other 113 files were byte-identical. All 120 live theory hashes
matched the correctness snapshot at completion. The reviewers separately
checked their batch hashes, but did not both repeat the historical
cross-snapshot comparison.

The review covers 18,791 physical lines in its frozen theory files. The
other **1,260 theory files remain deferred**, and complete dependency
reconciliation remains open. The selected import ancestry was inspected
for relevant contracts and trust boundaries, not exhaustively audited as
additional files. No application, general modal-completeness program or
Isabelle foundation was added to the review scope.

## What was challenged

| Proof family | Decisive scrutiny and retained boundary |
|---|---|
| Fresh-witness elimination | Substitution replaces the typed constant by an admissible eigenvariable even without its declaration. A surviving undeclared occurrence fails the guard; vacuous substitution can leave a constant-free axiom. Name-wide freshness is sufficient but stronger than typed-pair freshness. |
| Witness ranks and Henkin completion | Equal maximal ranks do not invalidate freshness: occurrence in another witness body would force a strict rank inequality, while name injectivity excludes the other distinguished label. Finite support and signature conservativity precede Zorn completion. The resulting extension concerns closed sentences in the expanded signature. |
| Signature conservativity | Auxiliary declarations are removed before projection back to old names. Type Existence discharges an unused context slot; no closed old-language inhabitant or arbitrary default name is silently assumed. |
| Quantifier and substitution transport | Binder shifts, restored indices and the order of premises were checked. Independence for local Gen/Inst comes from shifted premises together with old-context typing, not typing alone. |
| Renaming coherence and model translations | Closing the finite frame, application congruence and guarded β equations establish coherence without assuming Functionality. The translations use supplied model contracts and do not claim a two-sided isomorphism or unconditional model existence. |
| Native named syntax and theoremhood | α-to-βη arguments use strict-subterm induction without circularity. Decoder arguments use chart-supported inverses, not globally invertible renamings or out-of-range list values. Root β determinism is not confused with contextual determinism. Native/source-global theoremhood correspondence retains richness. |
| HOL choice | Fresh names, reverse-PC representatives and the inverse type-code construction are used only where their existential or injectivity specifications apply. These are ordinary HOL choice constructions, not user axioms or oracles. |

The source calculus has ten theoremhood constructors; the constructor
target includes `IndividualExistence` as an eleventh. Its reverse transfer
uses a derived source Existence theorem under richness. In the unrestricted
constant language individual terms already exist, so the extra rule is
redundant there. The audit corrected reviewers' initial descriptions rather
than mistaking those descriptions for code defects.

## Qualifications and the corrected prose

The checked results retain their actual signatures, type contexts,
freshness conditions, local-consequence definitions, closedness/richness
premises, supplied-model assumptions and off-domain limitations. Full F
results are not automatically R results. The raw-versus-language-restricted
βη obligation and the source-side sentence-premise closure task from the
earlier audit remain open; this review does not silently discharge them.

One introductory comment in
[Bacon_Source_Global_Substitution.thy](../theories/base/source_vocabulary/Bacon_Source_Global_Substitution.thy)
described correctly typed replacements for free variables, while
`ssubst_preserves_global_typing` actually assumes correctly typed replacements
at **every stock index**. The proof establishes that stronger-premise
theorem, and its uses retain the premise. This is a prose/contract
qualification, not a demonstrated failure of the theorem. After the audit,
Branden requested the correction: the comment now explicitly says
“for every variable index v” and identifies this as a sufficient total-stock
condition. No definition, theorem statement or proof changed. A support-local
theorem would be a separate strengthening. The paired record retains the
reviewed hash and separately records this documentation-only correction.
The affected `Bacon_Source_Vocabulary_Development` session rebuilt
successfully (16 seconds overall, 12 seconds for the session); the lexical
trust check and Git whitespace check also passed. Source line counts are
unchanged. This focused recheck is not a new full-repository build.

The native implication operator uses a canonical choice of bound names
relative to a rich variable stock. Results concern that defined operator.
The audit does not claim a separately proved comparison for every possible
alternative connective implementation.

## Verification evidence and limits

The maintained serial build preceding this audit passed in 4 minutes
33 seconds, with all 30 selected sessions and 1,371 selected theories.
All 23 freshly exported theorem-audit reports matched the stored checksums,
and the native graph/dependency checks passed. There were no subsequent
formal-theory changes. The reviewers inspected this existing evidence;
they did not run new builds or independently verify Isabelle's kernel.

The mathematical review inspected the formal source, import/session
configuration, relevant graph statements, explicit audit catalogs and
stored theorem-object records. Zero oracle dependencies, residual kernel
hypotheses and flex-flex constraints in a catalogued endpoint are useful
checks, but not an exhaustive axiom inventory, proof of statement adequacy,
or review of all imported library proofs. Ordinary proof holes fail a
standard batch build independently of lexical detection.

Batch 3 encountered an Astra service-capacity error. The interrupted session
was resumed after user authorization, retaining Fable's completed report
and the first 66 completed file reviews. Only the completed resumed
assessment contributes to the final coverage; the aborted attempt is not
counted as a second independent review.

An accurate presentation description is: **Fable 5.1 and Astra 6
adversarially reviewed the same 120 theory files for source fidelity and
formal correctness, with recorded qualifications.** It must not imply that
all 1,380 files, their complete dependency closures, the mathematical
foundations, or every published theorem have been certified.
