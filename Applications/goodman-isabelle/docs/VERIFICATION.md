# Checking the development

## Requirements and dependency

Use Isabelle2025-2, Python 3.9+, Git, and a Unix environment. The checker
uses `fcntl` locking and `pgrep` (provided on macOS; normally by procps on
Linux). The core sources must match the baseline in
[bacon-dorr.json](../dependencies/bacon-dorr.json), including ROOT, any ROOTS,
and theory/ML source files. Goodman is an ordinary folder in the main
repository and has the same access permissions.

In the Applications layout the default core path is the enclosing repository
(`../..`). The core commit ID is provenance; exact source hashes are the
authority, since application/docs commits also change the parent's HEAD.
If copied out as a standalone project, the default is the sibling
`../bacon-dorr-isabelle` and the separate checkout must also match the pinned
Git revision. Use `--core` or `BACON_DORR_ROOT` for another checkout. No
command automatically fetches, resets, or changes a dependency checkout.

## Commands

From this repository root:

```sh
# Dependency/preserved-source hashes, trust scan and packaging tests only:
./check_isabelle.sh --inputs-only

# Full selected-session build:
./check_isabelle.sh

# Full build, then serial export of all integration audits/statements:
./check_isabelle.sh --export

# Additionally compare every theory byte with the initial extraction:
./check_isabelle.sh --inputs-only --snapshot
```

The optional `--snapshot` check is expected to fail after reviewed changes
to live theory files; it records extraction fidelity, not a ban on future
development. The 82 preserved historical files have a separate immutable
manifest checked on every run. Build new adapters instead of silently
altering those inputs. Updating a dependency pin requires an explicit
source review and renewed verification.

Builds run with `-j 1` and `timeout=60` for each session. The lock serializes
cooperating invocations in this checkout; a process check also refuses to
start when another possible Isabelle build/export is already running.
Coordinate across projects: no local lock can prevent a separately launched
process from starting later. Do not run builds/exports concurrently.

Logs, including failed runs, remain in `verification/runs/`; new exports
go into a fresh timestamped directory under `verification/exports/`.
Both are Git-ignored. No cleanup command deletes older logs. The committed
release certificates are in `verification/audits/`. Refresh those only as
part of a reviewed checkpoint, not automatically on every development run.

## What the checks mean

1. **Dependency hashes:** all recorded ROOT/ROOTS and theory/ML bytes match
   the pinned core input. In standalone mode its Git revision is also checked.
   The old research repository is not needed.
2. **Preservation checks:** the historical files match the frozen bytes
   whose proof bodies were compared against their original source before
   extraction. The provenance manifest records both hashes. A fresh
   contributor need not possess that historical checkout.
3. **Static trust scan:** catches common admission/oracle escape commands.
   It is a guard, not a complete parser or a replacement for kernel checks.
4. **Isabelle build:** checks the selected sessions and their dependencies.
   Merely including a file in Git does not select it.
5. **Theorem-object audits:** named catalog entries have no oracle
   dependencies, residual kernel hypotheses or unresolved unification
   pairs. Explicit premises in the theorem statement remain assumptions.
6. **Source review:** mathematical fidelity needs comparison of definitions,
   quantifiers, stocks, type domains and consequence relations with the
   cited sources. Neither a clean build nor an AI review establishes that
   every source claim is represented or that its hypotheses were intended.

The theory uses Isabelle/HOL and, for the exact set-theoretic carriers,
HOL–ZF. These library foundations are retained; “no new axioms” does not
mean that the logic and its libraries have no axiomatic foundations.

## Selected and unselected source

ROOT and the three paths in ROOTS select the current session graph. All
293 supplied theory files now belong to the checked graph: the two
enumeration/completeness snapshots listed in
[STATUS.md](../STATUS.md#formerly-included-but-not-selected) were selected by
contributor task 4 (submitted for review) under sessions
`Goodman_Exact_Enumeration` and `Goodman_Exact_Frame_Completeness`. So do
the ten live theories added on 20 September 2026 for contributor tasks 1–5
(`Goodman_Native_TU_RS_Witness`, `Goodman_Native_Finite_PC` and their audits in
session `Goodman_Integration_Native_Extras`; `Goodman_Native_Biconditional_Algebra`
and its audit in session `Goodman_Integration_WI_Master`;
`Goodman_Exact_Frame_Representation` and its audit in session
`Goodman_Integration_Exact_Frame`; `Goodman_Exact_10_1_Parametric` and its
audit in session `Goodman_Integration_Exact_QLN`). The `unselected_theories` list in
`verification/provenance/extraction.json` is now empty, with a
`selected_later` record.
The main core's own selected dependency sessions are built as needed; this
does not run every unrelated session in the core repository.

The current catalog count excludes nine historical central-stock replay
entries from the integration total. `audit_summary` in `tools/check.py`
reports both counts rather than silently folding them together. Exports
must match the catalog paths and clean theorem-entry names in
`verification/catalogs.json`; an empty or partial export fails. When adding
or changing audited endpoints, review and update that manifest explicitly
along with the source catalog and status, rather than disabling validation.

## Dependency inspection

The core supplies an Isabelle-native graph tool, but its existing graph
covers the core, not the Goodman theories automatically. Here the explicit
ROOT/import graph, exported statements, and M5/WI proof-node provenance
checks provide the maintained evidence. A complete Goodman entity graph
can be added as a separate contributor task; no graph is represented as
a source-fidelity certificate.
