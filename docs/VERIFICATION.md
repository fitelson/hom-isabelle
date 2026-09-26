# Verification and trust boundaries

## Default check

This section concerns the core ROOT/import closure under `theories/`.
Applications are not part of that closure. Check Goodman separately with
`./Applications/goodman-isabelle/check_isabelle.sh --export` from the
repository root, and never run the two checks concurrently. See
[Applications](../Applications/README.md).

`./check_isabelle.sh` runs the lexical trust-guard tests, the trust guard,
the source-boundary guard, the core-only packaging check, and a serialized
Isabelle build of the 33 ROOT sessions. It includes
the principal theorem-object audit, the separate HOL–ZF action audit, and
the selected book audit stages.

The trust guard covers all preserved theory files, including core audits,
ROOT, embedded ML and repository-local ML files. It recognizes nested
comments, quoted strings and prose cartouches, and rejects ordinary inline
as well as multiline proof holes, including the `\<proof>` symbol (an
alias of `sorry`); the build also pins `skip_proofs=false`. Its unit tests
(29 when first recorded, 32 in the current check) run in the default
check, using in-memory examples rather than admitted theory files.

This is an explicitly limited lexical policy, NOT a sandbox for arbitrary
ML, aliases, generated code, custom antiquotations or external session heaps.
It supplements rather than replaces theorem-object audits and manual
review. See `tools/check_isabelle_trust.py` for the exact policy.

The audit examines Isabelle theorem objects for oracle dependencies,
residual kernel hypotheses and flex-flex constraints, and checks exact
catalog coverage. Mathematical statement premises and type-class assumptions
are reported, not erased. Passing it does not prove the historical accuracy
of the encoded definitions.

All default build jobs have timeout=60 and export_theory=true.
For a focused development check, use:

```sh
isabelle build -j 1 -d . -o timeout=60 -o export_theory=true SESSION
```

The explicit options also cover sessions that do not declare them in ROOT.
Do not run concurrent builds, exports, or graph extraction.

## Repository audit checkpoint (26 September 2026, latest)

A comprehensive audit of the whole repository (sixteen read-only module
reviews by two independent reviewers, verdict SOUND WITH CHANGES, no
blocker: no checked theorem disagrees with its documentation, no hidden
premise, no vacuity, no dependency violation) was followed by its fixes:
new audit coverage for documented endpoints that had no explicit catalog
target (the generic action-validity endpoint `paper_ZF_classicism_valid_on`
in the HOL–ZF action audit, now 259 endpoints; the older H–BBK completeness
development in the new 15-endpoint `h-bbk-audit.txt`; the three
countable-compatibility lemmas in the full-Classicism and small-carrier
audits, now 73 and 27 endpoints); the generic-validity endpoint added to
the native proof-dependency policy; stale scope banners, catalog labels,
theory comments and documentation corrected; the trust guard extended to
the `\<proof>` symbol and the build pinned to `skip_proofs=false` (32 guard
tests); the manifest procedure documented; dead artefacts removed. All 29
reports were re-exported and the manifest regenerated (29 reports,
verified). The complete serial check passed (`./check_isabelle.sh`: 32
lexical tests, 1,473 trust-scanned files, 33 sessions, 1,462 selected
theories, exit 0) and the native graph was rebuilt in the same run (87
seconds in total): 1,462 project theories, 33,123 nodes and 2,377,425
edges, all maintained dependency-policy checks clean. Goodman's dependency
pin was then refreshed and its full serial check and export passed.
Nothing is committed.

## Relevant (λI) language checkpoint (26 September 2026)

A new session `Bacon_Book_Lambda_I_Development` (`theories/base/book_lambda_I/`,
72 theories) checks Bacon's relevant language of Definition 9.2: an
independently defined λI theory calculus with the occurrence-guarded binder
Gen and its constant-form presentation, internal βη/α conversion with
derivability transport, λI models under the internal conversion clause with
soundness, λI retraction and signature conservativity, Henkin witness stages
restricted to closed λI predicates, a term model on internal conversion
classes of closed λI terms, original-signature model existence
(`book_lambda_I_canonical_model_existence`) and global strong completeness
(`book_lambda_I_canonical_strong_completeness`) for arbitrary well-formed λI
premise sets, under the minimal logical basis, a rich variable stock for
the main endpoints, and an actual typed assignment required of every model
in the class. Open and stated as four distinct questions: identification
with HJ (Definitions 9.9–9.10), conservativity of full H over the λI
calculus, the λI printed/exact β correspondence, and internalization of raw
βη-conversion (completeness for the raw-invariant subclass). A separate
regression session `Bacon_Book_Lambda_I_Regressions`
(`theories/base/book_lambda_I_regressions/`) exhibits an actual λI model and
typed assignment satisfying ⊥ → ⊥ and proves {⊥ → ⊥} λI-consistent; the
native proof-dependency policy gained λI roots checking that the
consistency, witness, valuation and completeness proofs use no full-H proof
judgment or full-model class. The design was reviewed and its amendments
applied before implementation; the final review asked for the regression
session, the dependency policy, scope wording and comment corrections,
which were applied, and its same-day follow-up confirmed them and asked
for two further documentary corrections (scope qualifications in the
abbreviated summaries and the design record's amendment status), which are
applied in this snapshot. Audits `book-lambda-I-audit.txt` (73 endpoints) and
`book-lambda-I-regression-audit.txt` (2 endpoints), all with zero oracles,
residual hypotheses and flex-flex pairs, are stored in `verification/audits/`
with the regenerated `verification/SHA256SUMS` (28 reports, verified). The
complete serial check passed (`./check_isabelle.sh`: 31 lexical tests,
1,472 trust-scanned files, 33 sessions, 1,461 selected theories, exit 0)
and the native graph was rebuilt in the same run (85 seconds in
total): 1,461 project theories, 33,122 nodes and 2,377,423 edges, all
maintained dependency-policy checks clean. Nothing is committed.

## Declared-names smallness checkpoint (26 September 2026)

Full-C model existence and completeness were extended to ZF-small declared
unions on arbitrary carriers: the only signature hypothesis is now an injective code of the
declared-name union into the elements of a ZF set, on an arbitrary name
carrier (`Bacon_Book_ZF_Declared_Names_Existence.thy`, session
`Bacon_Book_ZF_Modal_Representation`;
`Bacon_Book_ZF_Full_C_Declared_Names_Completeness.thy`, session
`Bacon_Book_ZF_Modal_Soundness`), covering the type ZF with a set-bounded
declared union and subsuming the countably declared and ZF-small-carrier
theorems, which are retained. To allow a code that is only injective on
admitted terms, the coded-frame locales were relativized and about thirty
representation lemmas gained an admitted-pair or world guard; external
endpoint statements, the independent model/interpretation predicates and
the countable coding equations are unchanged. The design was independently
reviewed before implementation (seven amendments applied) and the result
audited afterwards. New audit
`book-zf-declared-names-audit.txt` (31 endpoints) and the extended
`book-zf-modal-soundness-audit.txt` (42 endpoints) are stored in
`verification/audits/` with the regenerated `verification/SHA256SUMS`
(26 reports, verified); the other affected catalogs changed only in the
stated-premise counts of the guarded lemmas, all with zero oracles,
residual hypotheses and flex-flex pairs. The complete serial check passed
(`./check_isabelle.sh`: 31 lexical tests, 1,399 trust-scanned files,
31 sessions, 1,388 selected theories, exit 0) and the native graph was
rebuilt in the same run (109 seconds in total): 1,388 project theories,
32,317 nodes and 2,340,795 edges, all maintained dependency-policy checks
clean. Codex's final audit (27 AGREE, 0 DISAGREE, 0 UNSURE; SOUND WITH
CHANGES) required one extra audit target (the guarded class-decoder type
law, taking the declared-names catalog to 31), scope wording, present-tense
report counts and two theory comments; after those changes the complete
serial check and graph rebuild were rerun with the same outcome (110
seconds), the report was re-exported and the manifest regenerated and
verified. Nothing is committed.

## Stage-4 review follow-ups checkpoint (26 September 2026)

The six follow-ups of the independent stage-4 implementation review
were folded in; no proof of the cardinal construction changed.
Added: `book_full_C_countable_canonical_world_iff`
(`Bacon_Book_Full_Canonical_World_Existence.thy`; on a countable carrier
the full world set equals the earlier displayed conjunction without the
cardinal clause), and the countable coding equations
`book_countable_class_code` (`Bacon_Book_ZF_Coded_Frame.thy`) and
`book_countable_world_code` (`Bacon_Book_ZF_World_Codes.thy`). The latter
two assume a canonical frame on a countable carrier, because Isabelle
exposes a locale definition outside its locale only under the locale
predicate; the equations are otherwise literal unfoldings. The stale
compatibility comment in `Bacon_Book_Ambient_Henkin_Extension.thy` was
corrected (the name map now takes G and is injective only on used Henkin
names; external existence results, not every statement, are preserved).
The SCOPE banners of `Bacon_Book_ZF_Small_Carrier_Audit` and
`Bacon_Book_ZF_Modal_Soundness_Audit` now say that the type ZF is excluded
only from the whole-carrier-smallness case; both reports were re-exported
(only the banner line changed; the 25 and 37 endpoint entries are
unchanged, all with zero oracles, residual hypotheses and flex-flex pairs)
and `verification/SHA256SUMS` regenerated and verified (25 reports).
README, STATUS, the source guide, the nontriviality note and the
contributor guide were reconciled with the review's §7 drafts. The four
affected sessions rebuilt serially (exit 0), then the complete serial
check passed (`./check_isabelle.sh`: 31 lexical tests, 1,396 trust-scanned
files, 31 sessions, 1,385 selected theories, exit 0) and the native graph
was rebuilt in the same run (85 seconds incremental in total): 1,385
project theories, 32,244 nodes and 2,338,621 edges, all maintained
dependency-policy checks clean. The final review pass accepted
follow-ups 1–4 and 6 and required the correction of one STATUS.md
sentence that conflated the premises of the existence theorem with those
of the two equivalences; that sentence has been corrected, after which no
further change was required. Its low-priority residuals (forecasting
comments in the old countable existence theories and "countable ambient"
audit labels for facts now in the general locales) were cleaned up in the
26 September repository audit. Nothing is committed.

## ZF-small name carriers checkpoint (26 September 2026, later)

The countability restriction of the full-C completeness theorems was
removed for ZF-small name carriers. New theories:
`Bacon_Book_Named_Syntax_Cardinal`, `Bacon_Book_Ambient_Signature`
(session `Bacon_Book_Classicism_Development`, which now declares
`sessions "HOL-Cardinals"`), `Bacon_Book_ZF_Coded_Frame`,
`Bacon_Book_ZF_Small_Carrier_Existence`, `Bacon_Book_ZF_Small_Carrier_Audit`
(`Bacon_Book_ZF_Modal_Representation`) and
`Bacon_Book_ZF_Full_C_Small_Carrier_Completeness`
(`Bacon_Book_ZF_Modal_Soundness`). The canonical-frame, successor and
function-step locales lost their `countable` sort; `book_full_C_canonical_worlds`
gained the cardinal reserve clause; the 43 HOL-ZF representation contexts
now use `book_full_C_coded_frame` with an explicit bounded term code, the
natural-number code being the countable instance; the countable ambient
locale is a sublocale of the general one, so the earlier external
countable existence statements are retained (the internal name-map
interface changed; see the follow-up checkpoint above). Audit fact names that named the countable locale
now name the general locales. The complete serial check passed (31
sessions, 1,385 selected theories, 31 lexical tests, exit 0). The new
25-endpoint audit `book-zf-small-carrier-audit.txt` and the extended
37-endpoint `book-zf-modal-soundness-audit.txt` are stored in
`verification/audits/` with the regenerated `verification/SHA256SUMS`
(25 reports). An independent design review (all four amendments adopted)
preceded the implementation, and an implementation review followed it.
The native graph was rebuilt after
the check: 1,385 project theories, 32,241 nodes and 2,338,456 edges, all
maintained dependency-policy checks clean.

## Full-C soundness and completeness checkpoint (26 September 2026)

The session `Bacon_Book_ZF_Modal_Soundness` (originally eight theories, now ten, under
`theories/classicism/book/modal_semantics/soundness/`) is selected in ROOT
and in `check_isabelle.sh`. It builds serially with timeout 60 and
export_theory in about 15 seconds and contains no sorry, oops, oracle or
axiomatization. Its 31-endpoint audit report
`book-zf-modal-soundness-audit.txt` is stored in `verification/audits/`
and listed in `verification/SHA256SUMS`; every endpoint has zero oracles,
residual hypotheses and flex-flex pairs. The endpoints are the truth
clauses, naturality, identity/box clauses, βη invariance, H worldwise
soundness, MF/PE validity, `full_C_valid_everywhere`,
`full_C_theory_valid_at_root`, `satisfiable_theory_consistent`,
`book_full_C_theory_sound`, `book_full_C_theory_complete`,
`book_full_C_theory_derivable_iff_consequence` and
`book_full_C_theory_consistent_iff_satisfiable`. Three staged independent
reviews accompanied the development; the second stage's recommendation to
drop the bottom-falsity premise from the identity and box clauses was
adopted, and the third stage's three suggested extra audit labels were
added. The complete serial check
(`./check_isabelle.sh`, 31 sessions, 1,379 selected theories, 31 lexical
tests) passed in 2 minutes 35 seconds incremental, and the native graph
was rebuilt: 31,967 nodes and 2,327,986 edges, all maintained
dependency-policy checks clean, `verification/SHA256SUMS` verified.

## Workshop checkpoint check (10 September 2026)

The final pre-push serial check passed with all 30 selected sessions and
1,371 selected theory files. The incremental build took 2 minutes 28 seconds;
all 29 lexical-policy tests and the source-boundary/packaging guards passed.
All 23 fresh theorem-audit exports matched the stored checksum manifest.
The native graph refresh and dependency-policy checks passed with
31,855 nodes and 2,323,506 edges. All 130 local Markdown link targets
resolved, and Git's whitespace check passed.

The separate fidelity and correctness reviews still cover 120 theory
files, with the qualifications and remaining 1,260-file scope recorded in
their reports. This release check does not expand that independent review
coverage or turn the unfinished full-type C completeness work into a theorem.

## Foundations

The main H and proof-theoretic developments use Isabelle/HOL. Explicit
set-valued action/modal representations use the separate standard HOL–ZF
foundation. No arbitrary HOL carrier is silently treated as an internal ZF set.

## What the check covers

ROOT selects session entry theories; Isabelle also checks their imported
theories. A file merely present on disk is not necessarily in that closure.
Run:

```sh
python3 tools/check_release.py --inventory
```

The countable-signature full-C model-existence theorem and its dependent
audit are now selected. The nine remaining preserved unselected theory
files are listed by the same command. They are not release certificates.

### Check the evidence for one result

1. **Build coverage:** first confirm a successful build of the relevant
   session, then use the inventory above to check that its theory is in the
   selected import closure. Presence on disk alone does not establish checking.
2. **Source-review coverage:** find the theory's path in the
   [partial-audit manifest](../verification/source_fidelity/2026-09-10-first120.json).
   Its `reviewed` and `deferred_files` lists distinguish this audit's coverage.
   Compare the frozen hash with the current file, and consult the
   [correction report](PARTIAL_SOURCE_AUDIT_2026-09-10.md) for subsequent edits.
   File review does not certify every imported dependency.
   The separate [paired correctness record](../verification/formal_correctness/2026-09-10-first120.json)
   gives both participants' correctness and fidelity assessments for these
   same 120 paths. Read its revision note before equating the two snapshots.
3. **Additional theorem-object audit:** look for the exact theorem in the
   [audit reports](../verification/audits/) and its catalog. These add explicit
   oracle/hypothesis/constraint checks for named endpoints. Absence from a
   catalog does not mean an otherwise successfully built proof escaped
   Isabelle's kernel.

Thus a theorem can be kernel-checked while its file remains deferred for
source review. Neither a graph edge nor a filename match collapses these
distinct checks into a complete source-fidelity certificate.

## Nontrivial-model audit response (10 September 2026)

The structural `book_ZF_modal_model` definition is unchanged. The new
nontrivial refinement adds inhabited domains and a false proposition at
every world. The same canonical construction and original-signature
countable existence now satisfy this stronger conclusion. A separate
nine-endpoint audit covers the new proofs.

The maintained singleton regression has a seven-endpoint audit: it proves
actual structural modelhood, a typed assignment, all-formula truth,
bottom truth/inconsistency, a concrete inconsistent satisfiable premise set,
and exclusion by the nontrivial refinement. It runs in the separate
`Bacon_Book_ZF_Model_Regressions` session. The selected closure contains
1,371 theory files; nine additional files remain unselected.

The complete post-repair check passed in 2 minutes 7 seconds, with
30 sessions selected and every changed session below its 60-second limit.
This was incremental, not a fresh-cache timing. The graph rebuild and
maintained dependency policies also passed: 31,855 nodes and 2,323,506
edges over the 1,371 selected theories. All 23 exported audit reports
match the refreshed manifest. The lexical policy's 29 tests pass.

The earlier comprehensive audit distinguished a 34-second incremental
check from a fresh project build in an empty user-session-cache directory,
which passed in 5 minutes 23 seconds. A default incremental run is not a
fresh-build benchmark. Both selected the same then-current 29 sessions.
The fresh audit's 21 exported reports matched the repository copies exactly.

See [the source clarification](MODAL_NONTRIVIALITY.md). Neither the
refinement nor exclusion of the singleton is a completed generic soundness
or final completeness theorem.

## Partial source audit and comment corrections (10 September 2026)

The [capped source audit](PARTIAL_SOURCE_AUDIT_2026-09-10.md) completed
two-participant reviews of 120 theory files, leaving 1,260 deferred. Seven
theories received document-text/heading corrections only; their formal
content was unchanged against the reviewed snapshot. The subsequent full
serial check passed in 4 minutes 33 seconds, with all 30 selected sessions,
1,371 selected theories and 29 policy tests. The graph and dependency-policy
checks passed with 31,855 nodes and 2,323,506 edges. This is an incremental
rebuild, not a fresh-cache benchmark or complete source-fidelity certificate.
All 23 fresh theorem-audit exports matched the stored checksum manifest.

## Generic interpretation existence (9 September 2026)

`book_ZF_modal_model.generic_interpretation_exists` is now checked for
every independent full-minimal modal model. The explicit construction uses
typed K/S abstraction elimination and derives type closure, exact future
Lambda graphs, and naturality. The existing uniqueness result identifies
all admissible interpretations on typed inputs. No model or interpretation
definition was changed; no supplied interpreter, countability, rich variable
stock, full function space or additional nonemptiness premise was added.

The complete serial `./check_isabelle.sh` passed in 0:00:24; the changed
interpretation session took 0:00:14. Its separate 15-endpoint audit reports
zero oracle dependencies, residual kernel hypotheses and flex-flex
constraints. The existence endpoint has only the independent model premise
and the ordinary HOL type requirement on constant names.

At that checkpoint, the selected closure contained 1,364 theories in 29 sessions; nine
additional theories remain unselected. The source-boundary and packaging
guards pass. This completes generic interpretation existence for this
model/language class, not generic full-C soundness or completeness. Goodman
and the original research checkout were not modified.

That checkpoint's rebuilt native graph contained 31,592 nodes and 2,314,872 edges over the
1,364 selected project theories. The maintained dependency policies pass.
A focused traversal of proof dependencies and used definitions from the
existence endpoint reached 1,644 entities and found no occurrence of the
listed C/CEV derivability judgments or full-C canonical-model predicates.
This is an additional dependency check, not an independent source-fidelity
proof. All 21 exported audit-report checksums match their manifest.

## Countable-signature proof completion (9 September 2026)

The previously unfinished `book_full_C_countable_modal_model_exists` now
passes in the selected `Bacon_Book_ZF_Modal_Representation` session, together
with its 14-endpoint kernel audit (0:00:10 elapsed, exit status 0).
The theorem statement and model definitions were unchanged: repairs named
the outer image-membership assumption explicitly and corrected quoting of
the final existential witnesses. It constructs an original-signature model
and admissible interpretation for a full-C-consistent theory with countably
many declared constants at each type. The original name carrier is arbitrary,
and no original spare-name condition remains.

The complete standalone check passed before the extension (0:05:03) and
after selecting the completed theorem and updating the packaging guard
(0:00:09). At that checkpoint the selected closure contained 1,358 theory
files in the same 29 sessions, with nine preserved unselected theories.
Generic interpretation existence was then open; it is completed above.
Generic soundness and unrestricted modal completeness remain open.
No theorem here asserts that the constructed model's domains are countable.
The graph was rebuilt after this completion: 1,358 project theories,
30,625 nodes and 2,166,484 edges. Its maintained dependency-policy checks
passed, and the new theorem's exported statement retains only the four
stated mathematical premises and the ordinary HOL type requirement on
the constant-name carrier.

## Extraction validation

The standalone build passed on 9 September 2026 with Isabelle2025-2:
29 selected sessions, 0:05:31 elapsed time, exit status 0. The complete core
source-boundary and packaging checks also passed. No default session exceeded
the 60-second build-job limit; the HOL–ZF action stage took 49 seconds.

The final packaging gate also passed after adding the 13-endpoint audit of
the already checked fixed-ambient existence construction (0:00:17 elapsed).
At that extraction checkpoint, the then-unproved countable-signature
extension and its dependent audit remained unselected: 1,356 theory files
were selected and eleven were preserved but unselected. The completion
record above supersedes that boundary.

At the extraction checkpoint, the bundled graph workflow completed successfully: 30,622 nodes and
2,166,412 edges over the selected core. Its maintained proof-dependency
policies passed, including the HOL/HOL–ZF separation checks. These policies
cover their explicitly listed theorem roots, not an exhaustive independent
source audit of every declaration.

Twenty-nine generated theorem-audit reports are included in
[`verification/audits/`](../verification/audits/). They record the principal
1,143-endpoint HOL audit, the separate 259-endpoint HOL–ZF action audit, and
the smaller book audits, including the 11-endpoint generic-interpretation
and 13-endpoint ambient existence audits. The 14-endpoint
countable-signature existence report preserves and extends the latter
coverage without removing the earlier report. The separate 15-endpoint
generic interpretation-existence audit covers that construction. The
September 10 additions are the nine-endpoint nontrivial-model audit and
seven-endpoint singleton-regression audit. The September 26 additions are
the modal soundness/completeness audit (42 endpoints), the 27-endpoint
ZF-small-carrier audit, the 31-endpoint declared-names audit, the
73-endpoint relevant-language (λI) audit with its 2-endpoint regression
audit, and the 15-endpoint audit of the older H–BBK development.
Catalogs overlap; do not
add their counts to claim a count of distinct mathematical results.

## Reproducing audit reports and the manifest

After a successful default build, extract a report without triggering a build:

```sh
isabelle export -n -d . -O build/audits -x '*:*audit.txt' Bacon_Core_Theorem_Audit
isabelle export -n -d . -O build/audits -x '*:*audit.txt' Bacon_Classicism_ZF_Representation
```

Book, λI and H–BBK sessions export their separate audit reports using the
same pattern. The stored copies under `verification/audits/` are produced
by the same command with `-O verification/audits`. The manifest
`verification/SHA256SUMS` lists every stored report with a root-relative
path; it is regenerated and verified from the repository root with

```sh
find verification/audits -name '*.txt' | sort | xargs shasum -a 256 > verification/SHA256SUMS
shasum -a 256 -c verification/SHA256SUMS
```

Generated heaps, databases, logs, and graph data are local artifacts, not
required downloads.
