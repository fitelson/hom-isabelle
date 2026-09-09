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
| Σ, ℒ(Σ) | `signature`, `book_in_language` / `paper_R_in_language` | Declared constants and the guarded typed language |
| ⊢H A | `paper_named_H Σ G A` / `book_H Σ G A` | Distinct source-specific H presentations |
| S ⊢H A | `paper_named_derivable Σ G S A` | Paper local consequence; not the book's global theory closure |
| S ⊢ A, book | `book_theory_derivable Σ G S A` | Book theory derivability |
| ⊢C A, default R | `paper_R_classicism_proves Σ G A` | Paper's native R Classicism |
| Full-type C | `book_full_C_proves Σ G A` | Book MF+PE presentation |
| ⟦A⟧ᴹᵍ | `J g A` or `J w g A` | Interpretation; consult the model interface |
| hσ:Mσ→Nσ | `paper_R_bbk_homomorphism` | Typed interpretation-preserving map, not valuation preservation |
| @, W↑w | `root`, `book_ZF_future W R w` | Distinguished world and its accessible future |
| iᵂᵛσ(a) | `i σ w v a` | Typed counterpart map |
| Elements of internal A | `explode A` | HOL extension of an HOL–ZF set |
| A function graph | `Lambda A f` | Exact graph on the specified internal domain |
| Equality of values | host `=` | Distinguish from encoded object-language Leibniz identity |

F permits the full function-type grammar. R is the paper's relational-type
restriction. Never silently apply an F theorem as an R conservativity result.

The model documentation uses the authors' symbols where practical. Isabelle
theory files retain escaped symbols for portable source input and Unicode
explanatory comments.
