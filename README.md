# Higher-Order Metaphysics in Isabelle

This is an open formalization of the higher-order logic H and Classicism C
developed by Andrew Bacon and Cian Dorr. It is offered as a resource for
research and teaching, and as an invitation to graduate students and other
scholars to help complete the formalization.

There is a substantial checked development here, but **the project is not
finished**. In particular, the paper's relational-type Classicism results
must not be confused with the still unfinished full-type modal completeness
development for Bacon's book.

H soundness and completeness are proved in the scopes described in the
[source guide](docs/SOURCE_CORRESPONDENCE.md). For the book's full-type C,
we now have both original-signature model existence for countably declared
signatures and an admissible interpretation for every independent
full-minimal modal model. The latter includes the exact future-function
interpretation of abstraction, without adding model assumptions. The
canonical existence result now also supplies inhabited domains and a false
proposition at every world. An [audited source clarification](docs/MODAL_NONTRIVIALITY.md)
explains why those conditions are explicit in a separately named model
class. Generic full-C soundness and final modal completeness remain open.

## Start here

- [What is proved, with exact scope](STATUS.md)
- [Reading the Isabelle theories](docs/READING_GUIDE.md)
- [Source statements and theorem names](docs/SOURCE_CORRESPONDENCE.md)
- [Published notation and Isabelle notation](docs/NOTATION.md)
- [Modal-model source clarification and regression](docs/MODAL_NONTRIVIALITY.md)
- [Open problems and contributor projects](CONTRIBUTING.md)
- [Partial source-fidelity audit: 120 files reviewed, 1,260 deferred](docs/PARTIAL_SOURCE_AUDIT_2026-09-10.md)
- [Formal-correctness audit of those same 120 files](docs/FORMAL_CORRECTNESS_AUDIT_2026-09-10.md)
- [Sources, credits, and provenance](docs/SOURCES_AND_CREDITS.md)
- [Applications of the core](Applications/README.md), including [Goodman's Purity of Pure project](Applications/goodman-isabelle/README.md)

For one concrete source-to-code example, the sentence-consequence instance
of Bacon–Dorr's Theorem 3.2 is
[`paper_named_closed_strong_completeness`](theories/base/source_models/Bacon_Source_Named_Closed_Strong_Completeness.thy).
Its statement keeps the sentence, rich-variable-stock and carrier conditions
explicit. The source guide explains its full-F scope and remaining
correspondence qualifications.

## Access and contributions

The standalone repository is
[fitelson/hom-isabelle](https://github.com/fitelson/hom-isabelle).
As of 22 September 2026 it is public. To work on it locally:

```sh
git clone https://github.com/fitelson/hom-isabelle.git
cd hom-isabelle
```

Use [issues](https://github.com/fitelson/hom-isabelle/issues) to agree
the scope of a contribution and [pull requests](https://github.com/fitelson/hom-isabelle/pulls)
to submit it for review. See the contributor guide before changing a theorem.

## Check the development

Install **Isabelle2025-2**, put its `bin` directory on your PATH, and install
Python **3.9 or newer**. This is the required API floor, not a tested
compatibility matrix for every Python version and platform. Run from the
repository root:

```sh
isabelle version
python3 --version
./check_isabelle.sh
```

This checks the selected core sessions and their theorem-object audits.
Builds are serialized and use a 60-second limit **per session**, not for the
whole repository. A first build also builds dependencies and takes longer
than a cached run. No Vampire, Claude, Codex, or AI-service account/API key
is needed for local verification.

To explore a theory interactively:

```sh
isabelle jedit -d . -R Bacon_Source_Vocabulary_Development theories/base/source_vocabulary/Bacon_Source_Named_H.thy
```

[Verification details](docs/VERIFICATION.md) explain the audit, foundations,
and how to distinguish included source files from checked session contents.
[The dependency graph](docs/KNOWLEDGE_GRAPH.md) can be generated locally.

## Organization

| Directory | Role |
|---|---|
| `theories/base/` | Types, syntax, H, BBK/general models, and source-language bridges |
| `theories/classicism/action_models/` | Bacon–Dorr's relational-type C, categories, actions, and semantic results |
| `theories/classicism/book/` | Bacon's full-type C and the unfinished Chapter 18 modal development |
| Other `theories/classicism/` subdirectories | Earlier proof presentations and supporting bridges retained as dependencies |
| `theories/core_audit/` | Explicit theorem catalogs and kernel-object checks |
| `tools/` | Verification guards and Isabelle-native dependency inspection |
| `Applications/` | Separately documented applications with independent sessions and checks; currently Goodman's Purity of Pure project |

The theorem names and relative theory paths are preserved from the parent
development so that source correspondences remain traceable. This repository
keeps the core theory graph separate from its applications. Source PDFs and
private research records are not distributed.

## Applications

The [Applications folder](Applications/README.md) contains one application:
[Goodman's Purity of Pure project](Applications/goodman-isabelle/README.md).
It includes verified results, a report and a contributor roadmap; Goodman's
consistency question remains open. It is an ordinary subfolder, not a
submodule or a separate-access private component.

The default checker above remains a core check. To check Goodman and export
its audit statements, run the following separately, never concurrently with
another Isabelle build or export:

```sh
./Applications/goodman-isabelle/check_isabelle.sh --export
```

The core's mathematical status and audit coverage are not enlarged merely
by including an application.

## Contributing

You do not need to undertake an entire completeness proof. A source comparison,
an explanatory comment, a small missing lemma, or a reproducible example can be
a useful contribution. [CONTRIBUTING.md](CONTRIBUTING.md) gives bounded starting
points and specifies what counts as finishing each one.

The implementation was developed by Branden Fitelson with AI assistance.
Bacon and Dorr are the authors of the underlying philosophical and mathematical
work; this repository is not presented as their implementation or endorsement.

Software is available under the [BSD 2-Clause license](LICENSE). The license
does not license the source publications.
