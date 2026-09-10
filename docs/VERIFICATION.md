# Verification and trust boundaries

## Default check

`./check_isabelle.sh` runs the source-boundary guard, the core-only packaging
check, and a serialized Isabelle build of the 29 ROOT sessions. It includes
the principal theorem-object audit, the separate HOL–ZF action audit, and
the selected book audit stages.

The audit examines Isabelle theorem objects for oracle dependencies,
residual kernel hypotheses and flex-flex constraints, and checks exact
catalog coverage. Mathematical statement premises and type-class assumptions
are reported, not erased. Passing it does not prove the historical accuracy
of the encoded definitions.

All default build jobs have timeout=60 and export_theory=true.
Use `isabelle build -j 1 -d . SESSION` for a focused development check.
Do not run concurrent builds, exports, or graph extraction.

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

The selected closure now contains 1,364 theories in 29 sessions; nine
additional theories remain unselected. The source-boundary and packaging
guards pass. This completes generic interpretation existence for this
model/language class, not generic full-C soundness or completeness. Goodman
and the original research checkout were not modified.

The rebuilt native graph contains 31,592 nodes and 2,314,872 edges over the
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

Twenty-one generated theorem-audit reports are included in
[`verification/audits/`](../verification/audits/). They record the principal
1,143-endpoint HOL audit, the separate 257-endpoint HOL–ZF action audit, and
the smaller book audits, including the 11-endpoint generic-interpretation
and 13-endpoint fixed-ambient existence audits. The new 14-endpoint
countable-signature existence report preserves and extends the latter
coverage without removing the earlier report. The separate 15-endpoint
generic interpretation-existence audit covers the new construction.
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
