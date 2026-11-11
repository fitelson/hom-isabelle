# Goodman reports

## Lettie's refutation of Purity of Pure, 11 November 2026

- [Hand proof PDF](LETTIE_PP_REFUTATION_HAND_PROOF_2026-11-11.pdf)
- [Self-contained LaTeX](LETTIE_PP_REFUTATION_HAND_PROOF_2026-11-11.tex)
- [Item-by-item Isabelle correspondence](../docs/LETTIE_PP_CORRESPONDENCE.md)

A five-page proof, written for this repository in Goodman's notation, of
Jacob Lettie's theorem that ten ordinary premises over H + PE refute Purity
of Pure at type t→t. Each lemma names the theorem of Lettie's Isabelle
development that states it. The result and its proof are Lettie's.

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
