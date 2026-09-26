# Applications

Applications use the Bacon–Dorr core while retaining their own mathematical
scope, documentation, Isabelle sessions and verification commands. Goodman is
the only application distributed with this repository; it is an ordinary
tracked subfolder, not a submodule, and shares the repository's access
permissions and visibility.

## Goodman: Purity of Pure

[goodman-isabelle](goodman-isabelle/README.md) formalizes results and model
constructions relevant to Jeremy Goodman's Purity of Pure question. It has
a [report](goodman-isabelle/reports/GOODMAN_VERIFICATION_REPORT_2026-09-20.pdf),
[source ledger](goodman-isabelle/docs/RECONCILIATION_2026-09-20.md), and
[contributor projects](goodman-isabelle/CONTRIBUTING.md). Tasks 1–5 are
accepted; tasks 6–9 remain open for contributors. The consistency question
itself is open.

From the repository root, run checks **serially**:

```sh
./check_isabelle.sh
./Applications/goodman-isabelle/check_isabelle.sh --export
```

The first checks the selected core sessions. The second checks Goodman
and its required core dependencies. Adding this folder did not add Goodman
imports to any core theory or alter the core ROOT. Goodman checks the
enclosing core's source hashes against its recorded baseline; ordinary
application/documentation commits need not change that baseline.

## Adding an application

Give each application a self-contained README, an explicit status/source
map, a contributor guide and an independently invocable checker. Keep its
ROOT and audit catalogs separate from the core's. Cite the core results
and exact assumptions used; do not count application results as completing
an open core theorem. Do not introduce a dependency from the core back to
an application. Source publications and private research records are not
automatically authorized for redistribution with software.
