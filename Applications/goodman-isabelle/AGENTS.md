# Working in this repository

Read README.md, STATUS.md, CONTRIBUTING.md, docs/SOURCE_CORRESPONDENCE.md
and docs/VERIFICATION.md. This is the Goodman application, an ordinary folder
under Applications/ in the main repository. Its build graph remains separate.
Do not
edit the Bacon–Dorr core or historical research checkout as part of a task
here. Source publications control notation and scope; use readable Unicode.

The repository was packaged while the wider research program was paused.
Packaging is not authority to resume proof research or call another model.
Follow the user's current scoped task. The M5 nested collision is complete;
do not revive historical TODOs saying otherwise.

Current handoff: tasks 1–5 are accepted, and the agreed task-10 report/ledger
checkpoint is complete. Branden explicitly left tasks 6–9 open for
contributors. Do not resume them automatically. Read the current ledger
at docs/RECONCILIATION_2026-09-20.md before reusing an older audit's frontier.
Completing a reporting checkpoint is not completing every mathematical claim.

Use ./check_isabelle.sh. All Isabelle builds, exports and graph extraction
are serial, with timeout=60 per session. Split slow lemmas. Keep all logs,
including failures. No admissions, new oracles, unexplained axioms or
quick_and_dirty. Preserve the dependency pin and immutable historical proof
files; add a new adapter instead of silently modifying preserved bodies.

Keep distinct: H versus CEV+; F versus R types; local assumption versus
global added axiom; proposition identity versus material equivalence;
root truth versus global validity; closed-logical stock versus an enlarged
Pure interpretation; exact carriers versus general Henkin models; full
external PC versus internally expressible comprehension; HOL versus HOL–ZF.

Before claiming a result, inspect its exported statement and hypotheses.
Passing the build is not a source-fidelity audit. Never describe the no-PP
model as a solution of Goodman's question. Read the M5 repair to understand
why globalizing a fixed fun′ assumption invalidates the intended argument.

Use Isabelle-native dependencies, not Graphify. The core graph covers the
core, not automatically these Goodman theories. The M5 proof-node audit is
a scoped dependency certificate, not a complete graph of this repository.

Keep human-facing README/status separate from these instructions. Update
the source map, contributor TODOs and verification coverage when claims
change. Never delete or move existing user files without explicit approval;
do not publish private source PDFs or raw model journals. New copies may be
created for requested extraction. No recursive debates or model calls are
implied by a request to check or build the code.
