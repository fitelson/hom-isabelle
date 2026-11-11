# Goodman reports

## Purity of Pure and Recombination, 11 November 2026

- [Note PDF](PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.pdf)
- [Self-contained LaTeX](PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex)
- [Item-by-item Isabelle correspondence](../docs/PP_REFUTATION_CORRESPONDENCE.md)

This eight-page note proves that Purity of Pure at type t→t is inconsistent
with unary Recombination and a fundamental proposition, and that the
background theory with that instance of PP has no fun′ proposition. It
answers Goodman's consistency question negatively. The note is fixed: the
Isabelle development in `theories/pp_refutation/` was aligned with exactly
this text, whose checksum is recorded in the correspondence table. Do not
edit or recompile it in place; a corrected or extended account belongs in a
new file.

## Verification report, 20 September 2026

- [Report PDF](GOODMAN_VERIFICATION_REPORT_2026-09-20.pdf)
- [Editable, self-contained LaTeX](GOODMAN_VERIFICATION_REPORT_2026-09-20.tex)
- [Detailed source/claim reconciliation](../docs/RECONCILIATION_2026-09-20.md)

This self-contained report describes the verified object-language results,
exact-model constructions, corrections to Goodman's notes, and remaining
contributor problems. It does not claim that every mathematical obligation
or file-level fidelity audit is complete. It predates the result above and
says that Goodman's consistency question is open; that statement is
superseded, and the report has not been revised.

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
