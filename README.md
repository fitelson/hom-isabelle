# Higher-Order Logic and Classicism in Isabelle

This is an open formalization of the higher-order logic H and Classicism C
developed by Andrew Bacon and Cian Dorr. It is offered as a resource for
research and teaching, and as an invitation to graduate students and other
scholars to help complete the formalization.

There is a substantial checked development here, but **the project is not
finished**. In particular, the paper's relational-type Classicism results
must not be confused with the still unfinished full-type modal completeness
development for Bacon's book.

## Start here

- [What is proved, with exact scope](STATUS.md)
- [Reading the Isabelle theories](docs/READING_GUIDE.md)
- [Source statements and theorem names](docs/SOURCE_CORRESPONDENCE.md)
- [Published notation and Isabelle notation](docs/NOTATION.md)
- [Open problems and contributor projects](CONTRIBUTING.md)
- [Sources, credits, and provenance](docs/SOURCES_AND_CREDITS.md)

## Check the development

Install **Isabelle2025-2**, put its `bin` directory on your PATH, and install
Python 3. Run from the repository root:

```sh
isabelle version
./check_isabelle.sh
```

This checks the selected core sessions and their theorem-object audits.
Builds are serialized and use a 60-second limit **per session**, not for the
whole repository. A first build also builds dependencies and takes longer
than a cached run. No Vampire, Claude, Codex, account, or API key is needed.

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

The theorem names and relative theory paths are preserved from the parent
development so that source correspondences remain traceable. This repository
contains no applications of these theories. Source PDFs and private research
records are not distributed.

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
