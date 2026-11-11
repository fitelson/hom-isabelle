# Goodman's Purity of Pure Project in Isabelle

This application formalizes results and model constructions relevant to
Jeremy Goodman's question about Purity of Pure in higher-order metaphysics.
It is an ordinary subfolder of the
[Bacon–Dorr repository](../../README.md), not a
replacement for that development.

**Goodman's consistency question is answered negatively (11 November 2026).**
The background theory with the Purity schema, Application closure and Purity
of Pure at type t→t proves that no proposition r satisfies the condition that
unary Recombination imposes on a fundamental proposition: for every pure X,
□Xr → ∀p.Xp. Hence that theory has no fun′ proposition, and with unary
Recombination it has no fundamental proposition. Both the Recombination-only
package and the full-QLN package with PP are therefore inconsistent. Purity
of Fun, Exhaustion, L2 and the classification principles are not used.

The proof is given in a short note,
[Purity of Pure and Recombination](reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.pdf),
and is derived in Isabelle item by item in `theories/pp_refutation/`; the
[correspondence table](docs/PP_REFUTATION_CORRESPONDENCE.md) maps each lemma
and numbered formula of the note to its theorem. The native endpoint is
`gr_native_recombination_PP_refutation`: for a rich variable supply `G`,
`goodman_book_proves gb_signature G (gb_recombination_PP_axioms G) (book_bottom G)`.
The result depends on the added principles being axioms, so that the Rule of
Equivalence applies above them; it does not concern theories in which they
are merely true. It is checked with Isabelle2026 and has not yet been
independently refereed. See [STATUS.md](STATUS.md) for the exact scope.

Before this result we had verified substantial parts of Goodman's notes,
corrected several arguments, and connected the results to the new core.
That material is unchanged. Results stated over the refuted packages remain
theorems but are now vacuous.

The source question asks whether Purity of Pure is compatible with the
background theory and exactly one fundamental proposition, without assuming
Purity of Fun. The code distinguishes several axiom packages; a result for
one must not be silently attributed to another.

## Start here

- [The PP refutation: hand proof (PDF)](reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.pdf)
  and [its Isabelle correspondence](docs/PP_REFUTATION_CORRESPONDENCE.md)
- [26 September core compatibility updates](docs/CORE_UPDATE_2026-09-26.md)
- [What is checked and what remains](STATUS.md)
- [Goodman verification report (PDF)](reports/GOODMAN_VERIFICATION_REPORT_2026-09-20.pdf)
- [Detailed claim reconciliation](docs/RECONCILIATION_2026-09-20.md)
- [Reading the theories, with a worked M5 proof](docs/READING_GUIDE.md)
- [Goodman's numbered claims and Isabelle endpoints](docs/SOURCE_CORRESPONDENCE.md)
- [Published notation and Isabelle notation](docs/NOTATION.md)
- [Contributor projects and completion criteria](CONTRIBUTING.md)
- [Verification, audit scope and foundations](docs/VERIFICATION.md)
- [Sources, credits and extraction provenance](docs/SOURCES_AND_CREDITS.md)

The extracted development contains **293 theory files**. Two preserved
enumeration/frame-representation snapshots were initially not selected by
the build; contributor task 4 (**independently checked and accepted**) now
selects them and transfers their representation theorem to named sentences.
Ten further live theories were added on 20 September 2026: two for the
native TU⇒RS transfer (contributor task 1, **independently checked and
accepted**), two for arbitrary-finite pure comprehension (task 2,
**independently checked and accepted**), two for the packaged
biconditional-operator algebra (task 3, **independently checked and
accepted**), two for the frame-representation transfer (task 4,
**independently checked and accepted**), and two for the name-parametric
Theorem 10.1 (task 5, **independently checked and accepted**). The integration
catalogs now contain **1,708 entries in 87 catalogs**, plus nine separately
counted historical replay entries. These counts are not a count of independent mathematical
results and do not certify complete fidelity to every sentence in the notes.
The PP refutation of 11 November 2026 added fifteen theories in five sessions
and one catalog of 78 entries, giving **318 theory files** and **1,786 entries
in 88 catalogs**.

One concrete correction is M5. For F(p) = (p ↔ NC(p)), the proposed collision
at NC(r) and ⊤ fails under a local fun′(r) assumption. Replacing NC(r) by
NC(□r) gives a checked collision and conditional nonreversibility proof.
See [the corrected argument](docs/M5_NESTED_COLLISION_REPAIR.md).

## Obtain and check the application

Goodman is included at `Applications/goodman-isabelle/` in the main
repository, with the same visibility and access permissions. No submodule
or second clone is needed. If the repository is private, ask Branden
Fitelson for access, supplying your GitHub username.

```sh
git clone https://github.com/fitelson/hom-isabelle.git
cd hom-isabelle/Applications/goodman-isabelle
./check_isabelle.sh --export
```

Use **Isabelle2026**, Python **3.9 or newer**, Git, and a Unix environment
(macOS or Linux; Windows users can use a suitable Linux environment).
Put `isabelle` on PATH. The build itself needs no AI account, Vampire,
source PDFs, or access to the old research checkout. First builds take
longer than cached checks. All Isabelle builds and exports must be serial;
the limit is 60 seconds **per session**, not for the whole project.

The checker uses the enclosing core and verifies its exact recorded source
hashes (including its source ML). Application/documentation commits may
change the main repository's HEAD without changing that core baseline.
The reviewed 26 September baseline includes generic full-C modal soundness
and countably declared-signature completeness. This does not settle PP
consistency or turn root truth of the added stock into global extension
validity. See the compatibility note for the scope and the currently
uncommitted source checkpoint.
It will still refuse actual core source drift. For a separate dependency
checkout, use:

```sh
./check_isabelle.sh --core /path/to/pinned/bacon-dorr-isabelle --export
```

The checker refuses source drift. It retains local logs and can export all
integration audits. See [verification instructions](docs/VERIFICATION.md)
for the difference between a source-hash check, a build, an exported theorem
statement, and a source-fidelity review.

## Organization

| Directory | Role |
|---|---|
| `theories/axiom_extension/`, `vector/`, `replay/` | Named axiom extensions and whole-proof transfer into the core |
| `theories/central_stock/`, `individual/`, `numbered/`, `t8/`, `native_extras/` | Goodman object-language results and explicit axiom packages |
| `theories/semantics/`, `logical_stock/`, `exact_qln/`, `exact_l2/` | Exact Bacon carriers, denotation correspondence, QLN and L2 |
| `theories/m_claims/`, `m5/`, `m5_object/`, `general_m1/`, `t9/` | Model claims, corrections and counting arguments |
| `theories/control/`, `granularity/`, `wi_master/` | Further consequences and suggested-attack reductions |
| `theories/pp_refutation/` | The refutation of PP with Recombination, following the note lemma by lemma; packaging and native transfer |
| `theories/preserved/`, `preserved-additions/` | Required historical proof dependencies, with immutable provenance |
| `dependencies/` | Core revision and source hashes, not a second copy of the core |
| `verification/` | Audit certificates and extraction provenance |
| `docs/`, `tools/` | Source guides and portable verification tools |

Directory names after the first entry in each row are also under `theories/`.
Historical session and theorem names are retained so proofs remain traceable.
Private conversations, model-search experiments, source PDFs, the old report,
and chronological agent handoffs are not distributed here.

## Contributing

Contributions can be a source comparison, an explanatory comment, a small
missing theorem, or a larger model-theoretic argument. The
[contributor guide](CONTRIBUTING.md) separates bounded tasks from genuine
open mathematics and specifies what counts as completing each task.
Agree a scope in an [issue](https://github.com/fitelson/hom-isabelle/issues)
and submit a [pull request](https://github.com/fitelson/hom-isabelle/pulls)
with source references, exact hypotheses and verification evidence.

Branden Fitelson developed the implementation with AI assistance. Goodman,
Bacon and Dorr are credited for the underlying work, not represented as
authors of or endorsers of this implementation. Software is covered by the
[BSD 2-Clause license](LICENSE); source publications are not licensed by it.
