# Goodman reports

## Recombination without Exhaustion, 11 November 2026

- [Hand proof PDF](RECOMBINATION_WITHOUT_EXHAUSTION_HAND_PROOF_2026-11-11.pdf)
- [Self-contained LaTeX](RECOMBINATION_WITHOUT_EXHAUSTION_HAND_PROOF_2026-11-11.tex)
- [Item-by-item Isabelle correspondence](../docs/RECOMBINATION_ONLY_CORRESPONDENCE.md)

Shortly after Lettie found his result, a strengthening was found that drops
Exhaustion. This eleven-page note proves that Logical Purity, Application
and Purity of Pure at type t→t, as ordinary premises over H + PE, refute the
existence of a universal proposition, and hence, with unary Recombination
and a fundamental proposition, refute Purity of Pure. Every numbered step
names its theorem in the session `Goodman_Integration_Recombination_Only`,
and every use of Logical Purity or Application names its instance. The
proof is Isabelle-checked and pending independent human review. It is
compiled the same way as the verification report below.

## Lettie's refutation of Purity of Pure, 11 November 2026

- [Hand proof PDF](LETTIE_PP_REFUTATION_HAND_PROOF_2026-11-11.pdf)
- [Self-contained LaTeX](LETTIE_PP_REFUTATION_HAND_PROOF_2026-11-11.tex)
- [Item-by-item Isabelle correspondence](../docs/LETTIE_PP_CORRESPONDENCE.md)

An explanatory proof, written for this repository in Goodman's notation, of
Jacob Lettie's theorem that ten ordinary premises over H + PE refute Purity
of Pure at type t→t. The revised nine-page note starts with the connection to
Goodman's question, explains the construction before proving its properties,
and isolates the uses of the purity premises and Exhaustion. Its appendix
maps the lemmas to Lettie's unchanged Isabelle development. The result and
its proof are Lettie's; this is an expository revision, not a new theorem.

The original five-page TeX and PDF are preserved byte-for-byte in the
[pre-revision archive](archive/2026-11-11_pre_explanatory_revision/README.md).

## Verification report, 20 September 2026

- [Report PDF](GOODMAN_VERIFICATION_REPORT_2026-09-20.pdf)
- [Editable, self-contained LaTeX](GOODMAN_VERIFICATION_REPORT_2026-09-20.tex)
- [Detailed source/claim reconciliation](../docs/RECONCILIATION_2026-09-20.md)

This self-contained report describes the verified object-language results,
exact-model constructions, corrections to Goodman's notes, and remaining
contributor problems. It does not claim that every mathematical obligation
or file-level fidelity audit is complete. It predates Lettie's result and says
that Goodman's consistency question is open; for the full-QLN reading that
statement is superseded.

The report uses Branden's self-contained Lucida/Forbes LaTeX setup and has
no automatic byline. Compiling it requires TeX Live and the licensed Lucida
fonts installed on Branden's machine; neither is needed to read the PDF or
check the Isabelle development. The source-publication PDFs are not included.

On Branden's Mac, from the repository root:

```sh
mkdir -p reports/build
/Library/TeX/texbin/pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory=reports/build reports/GOODMAN_VERIFICATION_REPORT_2026-09-20.tex
/Library/TeX/texbin/pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory=reports/build reports/GOODMAN_VERIFICATION_REPORT_2026-09-20.tex
```

After checking the log and visually inspecting every rendered page, copy
the resulting PDF from `reports/build/` to the report path above. Always use
`\neq`, not its short alias. Build logs and page images are retained under
the ignored build directory; do not delete them without approval.
