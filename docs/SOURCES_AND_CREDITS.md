# Sources, credits, and provenance

## Mathematical sources

- Andrew Bacon, *A Philosophical Introduction to Higher-order Logics*,
  Routledge. [Publisher page](https://www.routledge.com/A-Philosophical-Introduction-to-Higher-Order-Logics/Bacon/p/book/9780367483012);
  [DOI](https://doi.org/10.4324/9781003039181).
  The development uses the book's own H and full-type Classicism
  conventions, especially Chapters 5–6, 8, 14–15, and 17–18.
- Andrew Bacon and Cian Dorr, *Classicism*, draft dated **1 July 2022**.
  [Author-hosted PDF](https://andrew-bacon.github.io/papers/Classicism.pdf).
  Source numbering and page references in this implementation refer to that
  draft, not automatically to later publication pagination.
  The source copy used in the parent project has SHA-256
  `49c6b04e48964360b0331e7108077798ae2807e58385240ba054c4eebdbc095f`.

PDFs of the source publications are not redistributed here. Obtain lawful copies from the authors,
publishers, or a library. The software license does not grant rights in the
underlying publications.

## Implementation and tools

Branden Fitelson developed this implementation with assistance from OpenAI's
Codex/ChatGPT and Anthropic's Claude. Human source comparison and Isabelle
verification are distinct obligations. Neither AI assistance nor a successful
kernel check by itself establishes fidelity to the source.

Bacon and Dorr receive credit for their underlying theories and results.
No authorship of this code or endorsement of the formalization is attributed
to them. Isabelle and its standard libraries, including HOL–ZF, are external
dependencies distributed under their own terms.

## Extraction provenance

This standalone repository was extracted from the core directories of
[Higher-Order Metaphysics in Isabelle](https://github.com/fitelson/higher-order-metaphysics-in-isabelle)
on 9 September 2026. The parent checkout's HEAD was
`3bb580368083a97f1e387df6b77d8819bbb8c079`, but the extraction includes
substantial **uncommitted core work** present at that date. It is not a
snapshot of that commit alone. The new repository's initial commit is the
reproducible source checkpoint.

The parent checkout is unchanged by the extraction. No research-application
directories, consultation transcripts, credentials, source PDFs, or inherited
Git history are included. Relative theory paths and names were retained to
preserve formal dependency and source-reference stability.
