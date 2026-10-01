# Verification and trust boundary

Use Isabelle2025-2 and Python 3.9 or later. Run, from the repository root:

```sh
./Applications/2.11/check_isabelle.sh
```

The checker applies the core's lexical trust guard to this application
(every `.thy` file under `theories/`, including `theories/refutation/`),
checks that every local theory is selected by exactly one session of the
application ROOT, and builds all application sessions with one build job,
timeout=60 per session, theory export enabled, and proof skipping disabled.
Never run it alongside another Isabelle build or export. A cold dependency
build takes longer than a cached application build.

## Sessions

| Session | Directory | Content |
|---|---|---|
| `Classicism_2_11` | `theories` | Concrete carriers, book and paper modelhood (35 theories) |
| `Classicism_2_11_Formulas` | `theories/refutation/formulas` | Object-language formulas, hypothesis set, `c211_proves` and its soundness, order definitions, world bookkeeping |
| `Classicism_2_11_Semantics` | `theories/refutation/semantics` | Generic truth conditions of □, ≤, Atom, Atomicity, Boolean Completeness, Rigid, Rigid Comprehension |
| `Classicism_2_11_Barcan` | `theories/refutation/bf` | Proposition 3.24(ii) and concrete BF |
| `Classicism_2_11_Lattice` | `theories/refutation/lattice` | Current relations, raw order coordinates, ultralimit of relations, realization |
| `Classicism_2_11_Raw_Lattice` | `theories/refutation/raw_lattice` | Completeness and atomicity at every world |
| `Classicism_2_11_Transfer` | `theories/refutation/transfer` | Raw order notions = paper (arrow-coded) order notions |
| `Classicism_2_11_Raw_Rigidity` | `theories/refutation/raw_rigidity` | Raw failure of Rigid Comprehension at t→t |
| `Classicism_2_11_Rigidity` | `theories/refutation/rigidity` | Paper-level failure of Rigid Comprehension |
| `Classicism_2_11_Refutation` | `theories/refutation/assembly` | Validity of all hypotheses, the main theorem, the audit |

`Classicism_2_11_Audit.thy` (34 endpoints) audits the model construction.
`Classicism_2_11_Refutation_Audit.thy` audits 35 refutation endpoints:
oracle dependencies, residual hypotheses and flex-flex pairs, with the
actual statements and explicit premise counts, and it **requires** the main
theorem `proposition_2_11_refuted` and `c211_conclusion_not_valid` to have
no premises. A theorem with explicit assumptions is not described as
assumption-free because its residual proof obligations are empty.

After a successful build, export the audits:

```sh
isabelle export -d . -d Applications/2.11 \
  -O Applications/2.11/build/exports \
  -x 'Classicism_2_11.Classicism_2_11_Audit:2-11-*' Classicism_2_11
isabelle export -d . -d Applications/2.11 \
  -O Applications/2.11/build/exports \
  -x 'Classicism_2_11_Refutation.Classicism_2_11_Refutation_Audit:2-11-*' \
  Classicism_2_11_Refutation
```

Read `build/exports/<session>.<theory>/2-11-*-audit.txt` and the
corresponding statements files. The `build_log` message filter did not show
audit text in the tested installation. Do not use force/clean rebuild flags
to obtain audit output.

## How the certificate is assembled

1. `c211_proves Σ G Ax` is the smallest set containing every theorem of the
   core's native Classicism judgment and every in-language member of Ax,
   closed under the core's MP, Gen and Inst rule shapes (source pp. 7–8,
   12). `c211_soundness`: if every member of Ax is valid in an action model
   (true at the root identity arrow under every typed adequate assignment,
   Definition 3.20), so is every derivable formula.
2. Generic semantics, for every action model: `c211_box_holds`,
   `c211_le_holds`, `c211_le_neg_holds`, `c211_atom_holds`,
   `c211_atomicity_holds`, `c211_box_atomicity_valid`, `c211_BC_valid`,
   `c211_BF_valid`, `c211_rigid_holds`, `c211_RC_holds_root`.
3. Concrete model: realization (`c211_root_realize_ex1` and its middle and
   terminal analogues), the coordinate order (`c211_rleq_root`), the
   ultralimit of relations (`c211_rcur_limit_ulim`), completeness and
   atomicity at every world (`c211_raw_complete`, `c211_raw_atomic`), and
   transfer to the encoded model (`c211_transfer_*`).
4. `c211_hypotheses_valid` and `c211_conclusion_not_valid` (through
   `c211_concrete_pRC_false`), then `proposition_2_11_refuted` by
   `c211_underivable`.

## What the checks do not establish

The lexical guard is not an ML sandbox. Kernel checking and the theorem
audit do not by themselves establish fidelity to a publication; the
source correspondence and the independent reviews address that separately.
HOL–ZF's standard axioms, HOL's metatheoretic choice (used, for example, in
SOME-selected witnesses whose specifications are proved) and the standard
library's free-ultrafilter existence theorem are foundational dependencies;
the application introduces no additional axioms.

The refutation does not certify the boxed forms □Boolean Completeness or
□BF, or the footnote's actual-LUB identification; neither is needed for
the refutation.

## Recorded checkpoint

30 September 2026, against unchanged core theory sources and ROOT at commit
`c53fa28c6655cf2190c65992a079e9bcd388f9e3`: the application checker passed
(trust guard clean on 54 files; 53 theory files in 10 sessions; with the
model session cached, the nine refutation sessions built in about 32 s in
total, each in at most 5 s). The refutation audit exported 35 clean
endpoints, the main theorem premise-free. The model audit's 34 endpoints
are unchanged. Earlier checkpoints of the model session are recorded in
the [consensus response](CONSENSUS_AUDIT_2026-09-30.md).

## Rebuilding the note

The checked PDF is included. Its editable source uses Branden Fitelson's
Lucida/Forbes setup. With those fonts installed, compile from `reports/`
using system TeX Live (`/Library/TeX/texbin/pdflatex` on the maintainer's
Mac), then visually inspect the resulting PDF. Do not substitute the app's
separate Tectonic installation or silently change the fonts. The note is
not required for the Isabelle build.
