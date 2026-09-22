# Sources, credits and provenance

## Current location

Goodman is maintained as the ordinary subfolder `Applications/goodman-isabelle/`
of [bacon-dorr-isabelle](https://github.com/fitelson/hom-isabelle).
It is not a submodule and shares the main repository's visibility. The
standalone GitHub repository remains as an earlier checkpoint; its local
Git metadata and working artifacts were preserved during the move.
The core ROOT and theory sources were not changed by incorporating the
application. The extraction history below describes the earlier standalone
packaging, not a second current build dependency.

## Mathematical sources

- Jeremy Goodman, *Is Purity of Pure consistent with Bacon's Logical
  Combinatorialism?*, project notes, July 2026, seven printed pages.
  The T-, L- and M-labels in this repository refer to these notes.
  Ask Branden or the author for an authorized copy. The source used for
  comparison has SHA-256
  `4527b3fed9ea8df47ef7015132cbd2b842a29140d3b145f0c72c21fa6bf1e106`.
- Andrew Bacon, *A Philosophical Introduction to Higher-Order Logics*
  (Routledge, 2024), [DOI](https://doi.org/10.4324/9781003039181).
  This is the definitive source for the book's H/Classicism conventions.
- Andrew Bacon and Cian Dorr, *Classicism*, draft dated 1 July 2022.
  [Author-hosted source](https://andrew-bacon.github.io/papers/Classicism.pdf).
  Source numbering follows that draft; SHA-256 of the copy used:
  `49c6b04e48964360b0331e7108077798ae2807e58385240ba054c4eebdbc095f`.
- Andrew Bacon, *Logical Combinatorialism*, *The Philosophical Review*
  (2020). Its appendix supplies the exact model construction, including
  Proposition 8 and Theorem 10.1. These are **not** references to identically
  numbered results in the introductory book. Source-copy SHA-256:
  `1ecbd6e4be4639bd233532b59524a80ea573a967aac0f37f216112279f76c1ce`.

Source PDFs are not redistributed. Obtain lawful copies from the authors,
publisher or a library. The software license grants no rights in them.

## Implementation credits

Branden Fitelson developed the implementation with assistance from OpenAI's
Codex/ChatGPT and Anthropic's Claude. Goodman, Bacon and Dorr are the authors
of the underlying philosophical and mathematical work; this repository is
not presented as their implementation or endorsement. The corrected M5
input is an implementation-project repair, not silently attributed to the
original notes.

Isabelle and its standard libraries, including HOL–ZF, are external
dependencies under their own terms. The separate Bacon–Dorr repository
retains its own provenance and source qualifications. This software is
distributed under the [BSD 2-Clause license](../LICENSE).

## Extraction

The initial snapshot was copied on 20 September 2026 from the separate
`goodman-integration` workspace, not from a Git commit of that workspace.
All **293 theory files are byte-identical**; only session-directory paths
in ROOT/ROOTS were mechanically relocated. Session and theorem names are
unchanged. The initial commit of this repository records the extracted
state. Neither the integration workspace nor either upstream repository
was changed by copying it.

[extraction.json](../verification/provenance/extraction.json) maps every
new path to its old relative path and checksum.
[frozen.json](../verification/provenance/frozen.json) records the 82
preserved historical inputs, their original/frozen hashes and import
adaptations. The original research checkout included uncommitted work;
its Git HEAD alone is not its source identity. No inherited Git history,
machine-specific path, source PDF, consultation transcript, model-search
experiment or old report is needed for this repository's build.

The three retained technical/review documents identify their integration
baseline explicitly. Other chronological working notes and unfinished
research handoffs remain outside this repository. Current claims belong
in [STATUS.md](../STATUS.md), not in an old audit's historical TODO list.
