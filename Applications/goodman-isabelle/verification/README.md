# Standalone release verification

## Recombination without Exhaustion — 11 November 2026 (full build passed under Isabelle2026)

A new session `Goodman_Integration_Recombination_Only`
(`theories/recombination_only/`, parent `PoP_Main`) formalizes the
strengthening of Lettie's result that drops Exhaustion:
`Goodman_RecOnly_Closure`, `Goodman_RecOnly_Relative` and
`Goodman_RecOnly_Final` contain the proof, and `Goodman_RecOnly_Audit` adds
no proof. The audit exports `recombination-only-audit.txt` and
`recombination-only-statements.txt` for 31 endpoints (the steps of the hand
proof, then `ro_thm1_U`, `ro_cor_EF_U`, `ro_cor_U`, `ro_thm1_CEVs`,
`ro_recombination_refutes_PP` and `ro_recombination_PP_inconsistent`). It
fails the build on any oracle, residual hypothesis or flex-flex pair. The
tree now has 315 theory files and 68 application sessions. No existing
theory, preserved file, external input or proof changed; Lettie's 11 files
still match their recorded hashes.

A targeted serial build of the new session with the checker's options
(`runs/build-2026-11-11T18-35-16-recombination-only-session.log`) passed,
and its audit files were retained under `audits/` so that the packaging
tests could compare them with the manifest. Input checks then passed (core
hashes equal to the pin, 82 preserved files, 11 external input files, 12
packaging tests), and `./check_isabelle.sh --export` passed with
**Isabelle2026**: build exit **0**, log
`build-2026-11-11T18-35-41-865083.log`, every session current. Exports in
`exports/2026-11-11T18-35-41-865083/`: **89 catalogs**, **1,756
integration entries and 9 replay entries** (1,765 clean rows). All 172
exported catalog and statement files are byte-identical to the retained
copies under `audits/`, the 170 earlier ones included; `audits/summary.json`
was updated to these counts.

## Lettie formalization — 11 November 2026 (full build passed under Isabelle2026)

The Isabelle theories of Jacob Lettie (Purity of Pure team) are included
with his permission and unmodified in `theories/lettie_pp/`: his seven
sessions `PoP_Main`, `PoP_SYN`, `PoP_W`, `PoP_NUP`, `PoP_K6`, `PoP_PSI` and
`PoP_PPT`, his three ROOT files and his README, in his layout. All 11 files
are byte-identical to his release; their SHA-256 hashes equal those
published in its CHECKSUMS.md and are recorded in
`provenance/external.json`. The typeset `README.pdf` was not copied, since
the application ignores PDFs. `ROOTS` gained the three directories
`theories/lettie_pp`, `theories/lettie_pp/psi` and
`theories/lettie_pp/ppt`. The checker now treats these files as immutable
inputs: it fails on any changed, missing or additional file, and two new
packaging tests (12 in all) cover this check.

A new session `Goodman_Integration_Lettie_Audit`
(`theories/lettie_audit/Goodman_Lettie_Audit.thy`) adds no proof. It
exports `lettie-w-not-pp-audit.txt` and `lettie-w-not-pp-statements.txt`
for 17 of his principal theorems, `w_not_pp` first, and fails the build on
any oracle, residual hypothesis or flex-flex pair. The tree now has 311
theory files and 67 application sessions (59 existing, his seven, and the
audit session). No existing theory, preserved file or proof changed.

Input checks passed (core hashes equal to the pin, 82 preserved files, 11
external input files, 12 packaging tests). `./check_isabelle.sh --export`
then passed with **Isabelle2026**: build exit **0**, 29 seconds, log
`build-2026-11-11T12-10-57-419558.log`. Most sessions were current from
builds made earlier the same day with the same sources and Isabelle; this
invocation built five of his sessions, and a preceding targeted build with
the checker's options built `PoP_Main`, `PoP_W` and the audit session.
Exports in `exports/2026-11-11T12-10-57-419558/`: **88 catalogs**, **1,725
integration entries and 9 replay entries** (1,734 clean rows). The 87
earlier catalogs match their certificates entry for entry. The new catalog
`Goodman_Integration_Lettie_Audit.Goodman_Lettie_Audit/lettie-w-not-pp-audit.txt`
has 17 entries; its certificate and statement file are retained under
`audits/`.

Of the 170 exported files, 168 are byte-identical to the retained copies.
`m5-nested-collision-audit.txt` and `wi-master-transfer-audit.txt` differ
only in their DIRECT-PROVENANCE proof-node counts under Isabelle2026
(45,179→39,854 and 46,568→41,201); their endpoint lists and kernel fields are
unchanged. Those two retained files were then refreshed from this export, so
all 170 retained files match the Isabelle2026 export. The proof-node counts
change because Isabelle2026 produces different proof terms; the provenance
verdicts (no historical collision, collapse, refutation or ex-falso endpoint
used) are the same.

## Core update — 26 September 2026 (third pin refresh; full build passed)

After the core's comprehensive repository audit and its fixes (the
relevant-language (λI) development through completeness with its regression
session, new audit coverage for the older H–BBK endpoints and the generic
action-validity endpoint, comment and documentation corrections), the pin
was refreshed to that checkpoint: 1,473 entries (77 added core files, 70
changed, none removed; base revision unchanged). No Goodman theory imports
any changed or added core theory directly. Input checks passed (all
hashes, 82 preserved files, packaging tests). `./check_isabelle.sh --export`
then passed: build exit **0**, 4 minutes 9 seconds, 60 sessions; exports in
`exports/2026-09-26T16-32-53-749032/`, **87 catalogs**, **1,708 integration
entries and 9 replay entries** (1,717 clean rows), every entry identical to
the retained certificates. Of the 169 exported files, 167 are byte-identical
to the retained copies; `m5-nested-collision-audit.txt` and
`wi-master-transfer-audit.txt` differ only in their DIRECT-PROVENANCE
proof-node counts (45,189→45,179 and 46,578→46,568), because the core proof
terms they traverse changed; their endpoint lists and kernel fields are
unchanged. Those two retained files were refreshed to the new export. No
Goodman `.thy`, ROOT or catalog manifest changed.

## Core update — 26 September 2026 (second pin refresh; full build passed)

Later the same day the core's ZF-small-carrier development was
independently reviewed (an implementation review and a follow-up pass)
and its complete serial check passed. The pin was refreshed again to that
checkpoint: 1,396 entries (six added core theories, 70 changed files, none
removed; base revision unchanged). No Goodman theory imports any changed or
added core theory directly. Input checks passed (all hashes, 82 preserved
files, 10 packaging tests). `./check_isabelle.sh --export` then passed:
build exit **0**, 3 minutes 51 seconds, 60 sessions, log
`build-2026-09-26T12-34-38-334323.log`; exports in
`exports/2026-09-26T12-34-38-334323/`, **87 catalogs**, **1,708 integration
entries and 9 replay entries** (1,717 clean rows), every entry identical to
the retained certificates. Of the 168 exported files, 166 are byte-identical
to the retained copies; `m5-nested-collision-audit.txt` and
`wi-master-transfer-audit.txt` differ only in their DIRECT-PROVENANCE
proof-node counts (45,185→45,189 and 46,574→46,578), because the core
proof terms they traverse changed; their endpoint lists and kernel fields
are unchanged. Those two retained files were refreshed to the new export.
No Goodman `.thy`, ROOT or catalog manifest changed.

## Core update — 26 September 2026, earlier (first pin refresh; build then pending)

The dependency manifest was explicitly reviewed and refreshed for the
completed full-C soundness/completeness checkpoint: eight new core files,
one ROOT selection and two comment-only edits, with no prior proof-body
changes. The 1,390-entry input check passed, all 82 preserved Goodman
files matched, and all ten packaging tests passed.

The requested full check/export did **not** start an Isabelle build.
The first attempt was refused by the conservative active-process guard
while a concurrent core review command was running. A later attempt was
refused for genuine source drift: another core theory
`Bacon_Book_Named_Syntax_Cardinal.thy` and an additional ROOT edit had
appeared. No guard was disabled, no other job was interrupted, and these
unfinished changes were not automatically accepted into the pin.
The previous 87-catalog certificates remain intact; there are no fresh
Goodman audit exports for this maintenance checkpoint yet.

That resumption is recorded in the section above: the additional delta was
reviewed, the pin adjusted, and the full check/export passed.
See [the scope review](../docs/CORE_UPDATE_2026-09-26.md).

The report's background section was updated without changing its Goodman
theorem claims. Its 12-page PDF compiled with TeX Live/Lucida and was
visually inspected; references and unequal signs are clean. The previous
PDF is preserved locally in `reports/build/core-update-2026-09-26/`.
No Goodman `.thy`, ROOT, catalog or historical source file was changed.

## Applications-folder verification — 20 September 2026

Goodman is now an ordinary tracked folder in the main repository, not a
submodule. All 303 theory files were byte-identical before and after the
move. The enclosing core ROOT and theory sources remain unchanged.

The parent core checker passed first: 31 Python tests, lexical trust and
source-boundary checks, core-only session packaging, and the selected core
Isabelle build (9 seconds with cached theories). The application checker
then passed serially from its new location: 10 Python tests, source/preserved
file hashes, and full selected Goodman build/export, with timeout=60 per
session. Relocated Goodman build: **3m46s**, exit 0; log
`build-2026-09-20T11-00-06-435697.log` under the ignored `runs/` directory.
All 87 catalogs and statement files are byte-identical to the accepted
certificates: 1,708 integration entries and nine separately counted replay
entries. No mathematical result changed.

The checker finds the enclosing core automatically. Its pin now also covers
the core source ML, recovered from the recorded baseline revision. Exact
core-source hashes remain mandatory; a differing whole-repository commit
is allowed only in the embedded layout, since app/docs commits also change
the parent HEAD. Standalone mode retains the revision check.

The report's repository links were updated, recompiled with Lucida/TeX Live
and visually inspected. No source publications, raw journals, Git metadata
or ignored working logs are part of the application commit. The original
standalone Git metadata and local artifacts were preserved outside the
tracked main-repository files.

## Current reporting checkpoint — 20 September 2026

Tasks 1–5 are accepted; the agreed task-10 report/reconciliation checkpoint
is complete. Tasks 6–9 remain open for contributors, by Branden's direction.
See [the report](../reports/GOODMAN_VERIFICATION_REPORT_2026-09-20.pdf) and
[claim ledger](../docs/RECONCILIATION_2026-09-20.md). The earlier sections
below retain their dated submission/build histories.

Final serial check: `build-2026-09-20T10-30-24-457044.log`, exit 0,
16 seconds with cached theories. All eight packaging tests passed; all 87
audit catalogs exported and matched the existing certificates byte-for-byte:
1,708 integration entries plus nine historical replay entries. All 82
preserved files and pinned core ROOT/theory hashes matched.

The new report compiled with TeX Live/Lucida, with no undefined references,
missing-character warnings or overfull boxes on the final compile. All 12
rendered pages were visually inspected, including unequal signs; the source
contains no standalone short not-equal alias. Local Markdown link targets
and the ledger's explicitly named theorem identifiers were checked.
No proof was edited, no original report overwritten, and no commit, push,
website upload or model consultation was performed for this checkpoint.

## Initial extraction evidence

20 September 2026. The relocated standalone repository passed
`./check_isabelle.sh --snapshot --export` using Isabelle2025-2 and the
pinned Bacon–Dorr core revision
`8dc5940a664172459da3bddaba3d72b067b359c3`.

- Build exit status: **0**; elapsed **3 minutes 39 seconds**. This run
  rebuilt the relocated Goodman sessions, rather than just checking
  their previous directory's cached result.
- All **293 copied theory files** matched their original integration bytes.
- The build log selected **291** of those theory names. The two remaining
  names were exactly `Bacon_PP_ZF_Exact_Enumeration` and
  `Bacon_PP_ZF_Exact_Completeness`, as documented in STATUS.md.
- All **82 preserved files** and the pinned core ROOT/theory hashes matched.
- Eight read-only packaging tests passed after the process-guard and
  incomplete-export regression checks were added. Subsequent documentation checks
  also verify local Markdown links before release.
- Serial exports produced **82 audit catalogs**, containing **1,574
  integration entries and 9 historical replay entries** (1,583 clean rows).
- The M5 audit traversed **45,189 proof nodes**, excluding dependency on
  the historical collision and fixed-fun′ collapse endpoints.

The actual text certificates and full available statement exports are in
[audits/](audits/), with machine-readable counts in
[summary.json](audits/summary.json). Initial proof-bridge catalogs predate
the separate statement-file convention; consult their theory declarations
as well as their audit rows. An exported audit entry can have explicit
statement premises even though it has no residual kernel hypotheses.

Local raw build/export logs are retained, but are not distributed because
they contain machine paths. The standalone build's local basename is
`build-2026-09-20T07-51-59-479782.log` under `verification/runs/`.
No model consultations or model-search transcripts are release artifacts.

These checks certify the selected formal objects and extraction, not an
exhaustive source-fidelity review. No mathematical result was strengthened
by repository packaging. The original integration workspace and both
upstream repositories remain unchanged.

After hardening the process guard and export validation, the documented
wrapper was rerun with `--export`: build exit 0, 15 seconds with cached
theories, followed by all successful exports and an exact catalog-manifest
match. Its local log is `build-2026-09-20T08-02-04-087719.log`. The new
exports are byte-identical to the committed certificates. Inherited theory
whitespace is preserved intentionally to retain the extraction checksums;
it is not a failed proof check.

To reproduce the build and create fresh exports, run:

```sh
./check_isabelle.sh --export
```

See [the verification guide](../docs/VERIFICATION.md) for setup, limitations
and the difference between source hashes, theorem audits and source review.

## Task-1 submission run (20 September 2026, later the same day)

Contributor task 1 (native TU⇒RS transfer) added
`theories/native_extras/Goodman_Native_TU_RS_Witness.thy` and its audit
theory to session `Goodman_Integration_Native_Extras`, one new catalog
`native-tu-rs-witness-audit.txt` (17 entries) to `verification/catalogs.json`
and to [audits/](audits/), and refreshed `summary.json`. This is
the historical submission record. Codex subsequently checked the proof,
source-scope correspondence and exported statements independently and
accepted the formal task. The two requested prose corrections are recorded
in STATUS.md; they do not change the derivations or their assumptions.

Independent review run: `./check_isabelle.sh --export`, log
`build-2026-09-20T08-33-24-919622.log`, exit 0, 15 seconds with cached
theories. Eight packaging tests passed; all 83 catalogs exported, with
1,591 integration entries plus nine replay entries, byte-identical to
the submitted certificates. Core hashes and 82 preserved files matched.

After the wording corrections (including a theory comment), the full
checker/export passed again: `build-2026-09-20T08-45-10-676487.log`, exit 0,
27 seconds. All 83 exported catalogs and statement files remained
byte-identical to the submitted certificates. No proof or stock changed.

- Session-only development builds (serial, timeout=60) are retained as
  `dev-native-tu-rs-2026-09-20T08-24-04.log` (failed: two proof-script
  errors), `dev-native-tu-rs-2026-09-20T08-24-36.log` (failed: one
  proof-script error) and `dev-native-tu-rs-2026-09-20T08-25-03.log`
  (exit 0) under `verification/runs/`.
- `./check_isabelle.sh --export` then passed: build exit **0** (cached
  heaps from the 08:25 session build; log
  `build-2026-09-20T08-27-14-189009.log`), all 82 preserved files and core
  hashes matched, eight packaging tests passed, and serial exports produced
  **83 catalogs** with **1,591 integration entries and 9 historical replay
  entries** (1,600 clean rows). The new exports are byte-identical to the
  committed certificates.
- The `--snapshot` extraction check is expected to report the two new files
  as additions; it is not a proof failure.

## Task-2 submission run (20 September 2026, later the same day)

Contributor task 2 (arbitrary-finite pure comprehension at every type) added
`theories/native_extras/Goodman_Native_Finite_PC.thy` and its audit theory to
session `Goodman_Integration_Native_Extras`, one new catalog
`native-finite-pc-audit.txt` (42 entries) to `verification/catalogs.json` and
to [audits/](audits/), and refreshed `summary.json`. This section retains the
submission history; Codex subsequently accepted the formal task after
independent proof review and a full checker/export run. The two requested
prose corrections concern relative consistency and the external-PC boundary,
not the proof or its assumptions.

Independent review run: `build-2026-09-20T09-08-10-145572.log`, exit 0,
15 seconds with cached theories. Eight packaging tests passed; all 84
catalogs and exported statements matched the submission byte-for-byte,
with 1,633 integration entries plus nine historical replay entries.

After the wording corrections (including a theory comment), the checker
and all exports passed again: `build-2026-09-20T09-11-25-481355.log`, exit 0,
27 seconds. The 84 catalogs and statement files remained byte-identical
to the submission. No proof or axiom package changed.

- Session-only development builds (serial, timeout=60) are retained under
  `verification/runs/` as `dev-finite-pc-2026-09-20T08-54-37.log` (failed:
  three proof-script errors), `…T08-55-45.log` (failed: one), `…T08-56-12.log`
  (exit 0, constructor half), `…T08-58-36.log` and `…T08-59-09.log` (failed:
  audit fact-name selection only), `…T08-59-52.log` (exit 0).
- `./check_isabelle.sh --export` then passed: build exit **0** (log
  `build-2026-09-20T09-00-44-085646.log`, cached heaps from the 08:59 session
  build), all 82 preserved files and core hashes matched, eight packaging tests
  passed, and serial exports produced **84 catalogs** with **1,633 integration
  entries and 9 historical replay entries** (1,642 clean rows), byte-identical
  to the committed certificates.

## Task-3 submission run (20 September 2026, later the same day)

Contributor task 3 (one packaged native subsidiary algebra result: biconditional
operators are self-inverse, pure, and members of G) added
`theories/wi_master/Goodman_Native_Biconditional_Algebra.thy` and its audit
theory to session `Goodman_Integration_WI_Master`, one new catalog
`native-biconditional-algebra-audit.txt` (26 entries) to
`verification/catalogs.json` and to [audits/](audits/), and refreshed
`summary.json`. This section retains the submission history. Codex subsequently
accepted the chosen task after independent proof review and a full checker/export
run. Documentation now distinguishes the package used from any claim that PP
is necessary, and STATUS.md has the current counts. No proof or axiom package
was changed.

Independent review: `build-2026-09-20T09-30-17-143833.log`, exit 0,
15 seconds with cached theories. Eight packaging tests passed; all 85
catalogs and statement exports matched the submission byte-for-byte,
with 1,659 integration entries plus nine historical replay entries.

After the documentation corrections (including a theory comment), the full
checker/export passed again: `build-2026-09-20T09-32-57-858159.log`, exit 0.
All 85 catalogs and statement exports remained byte-identical to the
submission. No proof or axiom package changed.

- Session-only development builds (serial, timeout=60) are retained under
  `verification/runs/`: `dev-bic-algebra-2026-09-20T09-15-44.log` (failed: two
  script errors), `…T09-17-17.log` (failed: `blast` timed out on a two-part
  language lemma, replaced by direct rule use), `…T09-19-02.log` and
  `…T09-19-43.log` (failed: polymorphic term-type instances, fixed by
  `gb_term` annotations), `…T09-20-34.log` (exit 0).
- `./check_isabelle.sh --export` then passed: build exit **0** (log
  `build-2026-09-20T09-21-17-266699.log`, cached heaps from the 09:20 session
  build), all 82 preserved files and core hashes matched, eight packaging tests
  passed, and serial exports produced **85 catalogs** with **1,659 integration
  entries and 9 historical replay entries** (1,668 clean rows), byte-identical
  to the committed certificates.

## Task-4 submission run (20 September 2026, later the same day)

Contributor task 4 selected the two formerly unselected snapshots
`Bacon_PP_ZF_Exact_Enumeration` and `Bacon_PP_ZF_Exact_Completeness` under
their recorded replay session names (`Goodman_Exact_Enumeration`,
`Goodman_Exact_Frame_Completeness`; proof bodies unchanged, hashes as in
`provenance/frozen.json`), added `theories/exact_frame/Goodman_Exact_Frame_Representation.thy`
and its audit theory in the new session `Goodman_Integration_Exact_Frame`,
one new catalog `exact-frame-representation-audit.txt` (21 entries, after
the companion necessity theorems requested in review) to
`verification/catalogs.json` and to [audits/](audits/), refreshed
`summary.json`, and emptied `unselected_theories` in
`provenance/extraction.json` (with a `selected_later` record). The earlier
"291 selected" statements above are historical. Codex independently reviewed
both the representation and companion necessity proofs and accepted task 4.
The result is a semantic characterization, not an effective decision procedure.

Independent review run: `build-2026-09-20T09-50-54-336930.log`, exit 0,
16 seconds with cached theories. All eight packaging tests passed; all 86
catalogs and statement files matched the submission byte-for-byte, with
1,680 integration entries plus nine historical replay entries. The core
hashes and all 82 preserved files remained unchanged.

After the documentation cleanup (including a theory comment), the full
checker/export passed again: `build-2026-09-20T09-53-32-591384.log`, exit 0,
17 seconds. All 86 catalogs and statement files remained byte-identical to
the submission. No theorem, proof or assumption changed.

- Session-only development builds (serial, timeout=60) are retained under
  `verification/runs/`: `dev-frame-2026-09-20T09-35-31.log` (both snapshot
  sessions built, exit 0 for them; three script errors in the new theory),
  `…T09-36-22.log` (failed: two locale-qualified lemma names and one
  range-membership step), `…T09-37-16.log` (exit 0).
- `./check_isabelle.sh --export` first failed only in the packaging test
  `test_unselected_files_are_explicit`, because `extraction.json` still listed
  the snapshots as unselected; after the provenance update it passed: build
  exit **0** (log `build-2026-09-20T09-38-56-589675.log`, cached heaps from
  the 09:37 session build), all 82 preserved files and core hashes matched,
  eight packaging tests passed, and serial exports produced **86 catalogs**
  with **1,676 integration entries and 9 historical replay entries** (1,685
  clean rows), byte-identical to the committed certificates.
- Companion necessity theorems added at Codex's request (no defect found in
  the submission): `dev-frame-2026-09-20T09-47-55.log` exit 0;
  `./check_isabelle.sh --export` exit **0** (log
  `build-2026-09-20T09-48-32-537017.log`), **86 catalogs**, **1,680
  integration entries and 9 replay entries** (1,689 clean rows),
  byte-identical to the committed certificates.

## Task-5 submission run (20 September 2026, later the same day)

Contributor task 5 (Theorem 10.1 parametric in constant names) added
`theories/exact_qln/Goodman_Exact_10_1_Parametric.thy` and its audit theory to
session `Goodman_Integration_Exact_QLN`, one new catalog
`exact-10-1-parametric-audit.txt` (28 entries) to `verification/catalogs.json`
and to [audits/](audits/), and refreshed `summary.json`. Codex independently
reviewed and accepted the closed-term arbitrary-name result. Its review
checker/export run, `build-2026-09-20T10-12-59-741982.log`, passed (exit 0,
16 seconds with cached theories); the exported statements matched exactly.

- Session-only development builds (serial, timeout=60) are retained under
  `verification/runs/`: `dev-parametric-2026-09-20T10-04-55.log` (failed: one
  nonexistent proof-method name), `…T10-05-29.log` (failed: one unfolding
  chain), `…T10-06-03.log` (exit 0).
- `./check_isabelle.sh --export` then passed: build exit **0** (log
  `build-2026-09-20T10-07-13-891623.log`, cached heaps from the 10:06 session
  build), all 82 preserved files and core hashes matched, eight packaging tests
  passed, and serial exports produced **87 catalogs** with **1,708 integration
  entries and 9 historical replay entries** (1,717 clean rows), byte-identical
  to the committed certificates.
