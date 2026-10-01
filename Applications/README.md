# Applications

Applications use the Bacon–Dorr core while retaining their own mathematical
scope, documentation, Isabelle sessions and verification commands. Goodman
and the Proposition 2.11 investigation are the applications distributed
with this repository; both are ordinary tracked subfolders, not submodules.
Other local applications are not authorized for redistribution.

## Classicism Proposition 2.11

[2.11](2.11/README.md) contains an all-type model construction, exact
source-model bridges, and calculations concerning the normalization in
footnote 42 of the 1 July 2022 *Classicism* draft. Its
[technical note](2.11/reports/NOTE_ON_PROPOSITION_2_11.pdf) presents a
counterexample. Isabelle certifies the refutation end to end for Boolean
Completeness with its intended lower-bound clause: every hypothesis
instance is valid in the model, the Rigid Comprehension instance at type
t→t is not, so it is not derivable (`proposition_2_11_refuted`). See its
[status](2.11/STATUS.md) and [contributor projects](2.11/CONTRIBUTING.md).

```sh
./Applications/2.11/check_isabelle.sh
```

Run this separately from every other Isabelle check or export.

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
