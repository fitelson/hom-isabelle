# Higher-Order Metaphysics in Isabelle

This is an open formalization of the higher-order logic H and Classicism C
developed by Andrew Bacon and Cian Dorr. It is offered as a resource for
research and teaching, and as an invitation to graduate students and other
scholars to help complete the formalization.

There is a substantial checked development here, but **the project is not
finished**. The paper's relational-type Classicism results and the book's
full-type modal results are distinct developments with distinct scopes;
read each theorem's hypotheses, not its name.

H soundness and completeness are proved in the scopes described in the
[source guide](docs/SOURCE_CORRESPONDENCE.md). For the book's full-type
Classicism C, generic modal soundness is proved for every independent
nontrivial modal model with an admissible interpretation. Original-signature
model existence and completeness are proved under one signature-size
hypothesis: the union of the declared constants admits an injective code
into the elements of some ZF set, on an arbitrary name carrier. This covers
countably declared signatures, ZF-small carriers such as `nat set` with
every constant declared, and the type `ZF` itself with a set-bounded
declared union; those earlier scopes remain available as retained theorems
and as corollaries.

For a rich variable stock and well-formed formulas in the full minimal
language, derivability from a theory is equivalent to root consequence
over the nontrivial class, and consistency is equivalent to satisfiability
([`Bacon_Book_ZF_Full_C_Declared_Names_Completeness.thy`](theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Full_C_Declared_Names_Completeness.thy)
for the declared-union scope; the retained countable and small-carrier
versions are in
[`Bacon_Book_ZF_Full_C_Completeness.thy`](theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Full_C_Completeness.thy) and
[`Bacon_Book_ZF_Full_C_Small_Carrier_Completeness.thy`](theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Full_C_Small_Carrier_Completeness.thy)).
Open formulas and arbitrary premise sets are allowed. The constructed
models have inhabited domains and a false proposition at every world;
the [nontriviality clarification](docs/MODAL_NONTRIVIALITY.md) explains
why this class is distinguished from the broader structural definition.
Generic interpretation existence also remains available for the structural
class, with exact future abstraction and uniqueness on typed inputs.

This is not unrestricted completeness for every signature: declared
unions with no injection bounded by a ZF set are outside the construction
(a limitation of the injective syntax coding, not a proof that such
theories lack models). Other general λ-sublanguages (beyond the checked
relevant (λI) instance) and richer primitive profiles remain open. The results use HOL–ZF representation, root
consequence, the documented future-restricted implication and the literal
box `λp.(p =ₜ ⊤)`; see [STATUS.md](STATUS.md) for verification evidence
and exact boundaries.

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
| `theories/base/` | Types, syntax, H, BBK/general models, the relevant (λI) language development (`book_lambda_I/`), and source-language bridges |
| `theories/classicism/action_models/` | Bacon–Dorr's relational-type C, categories, actions, and semantic results |
| `theories/classicism/book/` | Bacon's full-type C and the Chapter 18 modal development, including generic soundness and completeness |
| `theories/classicism/presentation_reconciliation/`, `h_only_presentations/`, `equivalence_development/`, `auxiliary_bridges/` and the top-level `theories/classicism/*.thy` | Represented full-F C: the Appendix A reconstruction, the proved presentation correspondences (Theorem 6.1, `Bacon_Theorem_6_1_represented`), the S4 package and auxiliary semantic bridges; their principal results are audited endpoints in the core catalog, not merely dependencies |
| `theories/classicism/h_bbk_canonical/`, `h_bbk_strong_completeness/`, `h_bbk_countable/`, `general_model_development/` and the remaining `theories/classicism/` subdirectories | Earlier H-BBK canonical/countable and general-model developments (leaf sessions superseded by the parametric and named endpoints, retained for reference) and supporting developments retained as dependencies |
| `theories/core_audit/` | Explicit theorem catalogs and kernel-object checks |
| `tools/` | Verification guards and Isabelle-native dependency inspection |
| `Applications/` | Separately documented applications with independent sessions and checks |

The theorem names and relative theory paths are preserved from the parent
development so that source correspondences remain traceable. This repository
keeps the core theory graph separate from its applications. Source PDFs and
private research records are not distributed.

## Applications

The [Applications folder](Applications/README.md) includes
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
