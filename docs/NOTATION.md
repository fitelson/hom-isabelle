# Source notation and Isabelle input

These correspondences are a reading aid. A declaration's actual type and
guards remain authoritative.

| Source notation | Isabelle representation | Meaning |
|---|---|---|
| e, t | `Ind`, `Prop` | Object-language individual and proposition types |
| σ → τ | `Arr σ τ` | Object-language function type, not a host function space |
| A B | `NApp A B` | Named object-language application |
| λx.A | `NLam n A` | Named abstraction; the variable stock G supplies n's type |
| x | `NVar n` | Named variable |
| c:σ | `NConst c σ` | A nonlogical constant with its occurrence type |
| A logical constant | `NLogical l` | The logical-symbol datatype differs between paper and book |
| Σ | `Σ :: 'c ssignature`, or a locale's `signature` | A function assigning each type its set of declared constant names |
| A:τ in ℒ(Σ), paper F | `named_in_language paper_logical_type Σ G A τ` | Well-typed named term using declared constants |
| A:τ in ℒ(Σ), paper R | `paper_R_in_language Σ G A τ` | The additional relational-language restriction |
| A:τ in ℒ(Σ), book minimal | `book_in_language book_minimal_logical_type UNIV Σ G A τ` | Full grammar over the book's two primitive logical-symbol families |
| ⊢H A | `paper_named_H Σ G A` / `book_H Σ G A` | Distinct source-specific H presentations |
| S ⊢H A, project local relation | `paper_named_derivable Σ G S A` | Project-defined local closure using paper H theorems; not a displayed source definition or the book's global theory closure |
| S ⊢ A, book | `book_theory_derivable Σ G S A` | Book theory derivability |
| ⊢C A, default R | `paper_R_classicism_proves Σ G A` | Paper's native R Classicism |
| Full-type C | `book_full_C_proves Σ G A` | Book MF+PE presentation |
| ⟦A⟧ᴹᵍ | `J g A` or `J w g A` | Interpretation; consult the model interface |
| hσ:Mσ→Nσ | `paper_R_bbk_homomorphism` | Typed interpretation-preserving map, not valuation preservation |
| @, W↑w | `root`, `book_ZF_future W R w` | Distinguished world and its accessible future |
| iᵂᵛσ(a) | `i σ w v a` | Typed counterpart map |
| Elements of internal A | `explode A` | HOL extension of an HOL–ZF set |
| A function graph | `Lambda A f` | Exact graph on the specified internal domain |
| Equality of values | host `=` | Distinguish from the encoded identity formulas below |

Two book modal-model predicates must also be distinguished:
`book_ZF_modal_model` is the preserved structural class;
`book_ZF_nontrivial_modal_model` adds an inhabited domain at every type
and world, and a proposition false at each world. This is an explicit
source-directed refinement, not a claim that Definition 18.1 prints all
these conditions. See [the refinement's source comment](../theories/classicism/book/modal_semantics/hol_zf/Bacon_Book_ZF_Nontrivial_Model.thy)
and [current status](../STATUS.md).

F permits the full function-type grammar. R is the paper's relational-type
restriction. Never silently apply an F theorem as an R conservativity result.

## Logical formulas: paper and book

Here A and B are object-language formulas, x is the variable named n, and
G n is its fixed type. For the quantifier-operator rows, F is a term of type
σ → t. The stock condition `sg_rich G` supplies infinitely many names of
each full simple type; it supports the fresh choices in defined operators.

| Source formula | Paper's named F language | Book's minimal F language |
|---|---|---|
| A → B | `named_paper_imp G A B` | `book_imp A B` |
| A ↔ B | `named_paper_iff G A B` | `book_iff G A B` |
| ¬A | `named_paper_not A` | `book_not G A` |
| A ∧ B | `named_paper_and A B` | `book_and G A B` |
| A ∨ B | `named_paper_or A B` | `book_or G A B` |
| ∀σ F | `named_paper_all σ F` | `NApp (NLogical (SBAll σ)) F` |
| ∀x.A | `named_paper_all (G n) (NLam n A)` | `book_all G n A` |
| ∃σ F | `named_paper_ex σ F` | No primitive existential in the minimal basis |
| A =σ B, now A and B of type σ | `named_paper_eq σ A B` | `book_leibniz G σ A B` |

The paper's implication and biconditional are applications of closed
λ-defined operators; the book's implication is primitive. Conversely, the
paper has primitive equality, while the book's minimal-language identity
is λ-defined Leibniz identity. These are representations of source
expressions, not assertions that differently encoded terms are equal.
In particular, a λ-defined application is not silently replaced by its
β-reduced body.

Inspect the definitions in
[paper logical syntax](../theories/base/source_vocabulary/Bacon_Source_Named_Logical_Syntax.thy),
[book formula syntax](../theories/base/book_models/Bacon_Book_Minimal_Formula_Syntax.thy),
[book Boolean syntax](../theories/base/book_models/Bacon_Book_Minimal_Boolean_Syntax.thy), and
[book Leibniz syntax](../theories/base/book_models/Bacon_Book_Minimal_Leibniz_Syntax.thy).
The [worked theorem](READING_GUIDE.md#one-small-checked-proof) distinguishes
forming a formula from proving it.

The model documentation uses the authors' symbols where practical. Isabelle
theory files retain escaped symbols for portable source input and Unicode
explanatory comments.
