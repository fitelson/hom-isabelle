# Verification and trust boundaries

## Default check

`./check_isabelle.sh` runs the lexical trust-guard tests, the trust guard,
the source-boundary guard, the core-only packaging check, and a serialized
Isabelle build of the 30 ROOT sessions. It includes
the principal theorem-object audit, the separate HOL–ZF action audit, and
the selected book audit stages.

The trust guard covers all preserved theory files, including core audits,
ROOT, embedded ML and repository-local ML files. It recognizes nested
comments, quoted strings and prose cartouches, and rejects ordinary inline
as well as multiline proof holes. Its 29 unit tests run in the default
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

Twenty-three generated theorem-audit reports are included in
[`verification/audits/`](../verification/audits/). They record the principal
1,143-endpoint HOL audit, the separate 257-endpoint HOL–ZF action audit, and
the smaller book audits, including the 11-endpoint generic-interpretation
and 13-endpoint fixed-ambient existence audits. The new 14-endpoint
countable-signature existence report preserves and extends the latter
coverage without removing the earlier report. The separate 15-endpoint
generic interpretation-existence audit covers that construction. The
September 10 additions are the nine-endpoint nontrivial-model audit and
seven-endpoint singleton-regression audit.
Catalogs overlap; do not
add their counts to claim a count of distinct mathematical results.

## Reproducing audit reports

After a successful default build, extract a report without triggering a build:

```sh
isabelle export -n -d . -O build/audits -x '*:*audit.txt' Bacon_Core_Theorem_Audit
isabelle export -n -d . -O build/audits -x '*:*audit.txt' Bacon_Classicism_ZF_Representation
```

Book sessions export their separate audit reports using the same pattern.
Generated heaps, databases, logs, and graph data are local artifacts, not
required downloads.
