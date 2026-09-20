# Notation and formal scope

These correspondences are a reading aid. The actual declaration, its type,
and its surrounding locale determine the precise statement.

## Types, terms, and proof assertions

| Source notation | Isabelle representation | Reading |
|---|---|---|
| e, t | `Ind`, `Prop` | Individual and proposition types |
| σ→τ | `Arr σ τ` | Object-language function type |
| t→t | `gb_unary` | Unary proposition-operator type |
| x, c, λx.A, A B | `NVar`, `NConst`, `NLam`, `NApp` | Named syntax; G assigns types to variable names |
| Σ | A typed constant signature | Declared names, distinguished from names merely occurring in one term |
| G | `sgcontext`; `sg_rich G` | Variable-name type assignment; richness supplies fresh names at each type |
| Γ | Constructor-side typing context | A list of types, not the named variable stock G |
| C+[T] ⊢ A | `goodman_book_proves Σ G T A` | Native theoremhood over added axioms T |
| Γ;T ⊢CEV⁺ A | `CEV_axiom_proves` | Older constructor-calculus theoremhood |
| Γ;T;S ⊢CEV⁺ₛ A | `CEV_axiom_from` | Temporary assumptions S above fixed added axioms T |
| Translation of A | `gi_to_book G ns cmap A` | Translation using a typed name chart ns and constant map cmap |
| ⟦A⟧ | A `denote`/`eval` expression | A value, not a truth assertion or a proof |

The full function-type language F and the relational restriction R are
different source languages. This integration uses the full-F minimal book
language; an F theorem does not by itself establish R conservativity.
The original `App`, `Lam`, and `Eq` constructors in preserved proofs are
not the named constructors merely spelled differently.

## Goodman vocabulary

The primary declarations are in
[Goodman_Book_Vocabulary.thy](../theories/axiom_extension/Goodman_Book_Vocabulary.thy).
Pure and Fun are two object-language names, each declared at every type
σ→t. They are not host predicates supplied by Isabelle.

| Source expression | Native representation | Scope |
|---|---|---|
| Pureσ | `gb_Pure σ` | A predicate constant of type σ→t |
| Pureσ(a) | `gb_pure σ a` | An object-language formula |
| Funσ(a) | `gb_fun σ a` | Fundamentality at type σ |
| Pure(Pureσ) | `gb_purity_of_pure σ` | Purity of the σ-purity predicate |
| Pure(Funσ) | `gb_purity_of_fun σ` | Separate from purity of Pure |
| Target PP | `gb_target_PP` | `gb_purity_of_pure gb_unary`, not every type instance at once |
| Pure(f)∧Pure(a) → Pure(fa) | `gb_application_closure G σ τ` | Universally closed schema for f:σ→τ and a:σ |
| Pure(a) → □Pure(a) | `gb_persistence G σ` | A separate Persistence schema; do not silently add it to a no-PP background |
| ∃!x:σ.Fun(x) | `gb_unique_fundamental G σ` | Object-level existence and uniqueness |
| fun′(p) | `gb_fun_prime_with_names G x y p`, or `gb_fun_prime_on_chart G ns p` | Evaluation at p is injective on pure unary operators |

The formula fun′(p) says that for pure X,Y:t→t, identity Xp = Yp implies
identity X = Y. It is not the same as Fun(p). The explicit binder names
must be distinct and fresh for p. An ∃fun′ premise is not supplied merely
by writing this definition.

The letter G has two uses in source-facing discussion. In `sg_rich G` it
is the variable stock; in Goodman's group notation, G is the group of pure
invertible unary operators. The Isabelle names `gb_group_member_on_chart`
and `gi_T9_root_group` disambiguate the latter.

## Identity, truth, and modality

For formulas A,B, the native constructors include `book_imp A B`,
`book_iff G A B`, `book_not G A`, `book_and G A B`, `book_or G A B`,
and `book_all G n A`. Equality of terms of type σ is the formula
`book_leibniz G σ A B`. The book's minimal language defines Leibniz
identity rather than introducing host equality as an object-language rule.

| Expression | Meaning |
|---|---|
| A ↔ B | Material biconditional, not identity of propositions |
| A =σ B | Object-language Leibniz identity at type σ |
| A ≠σ B | Negation of that identity |
| □A | Necessity, defined using identity with ⊤; native `book_box G A` |
| ◇A | Possibility, ¬□¬A |
| NC(A) | □A ∨ □¬A; preserved `pp_noncontingent A` |
| host `A = B` | Equality of represented syntax or semantic values at the host type |

Theorem-level PE/Equivalence can turn an appropriately proved material
equivalence into proposition identity. Agreement of truth values at one
world is not enough. A local assumption cannot be treated as an added
axiom merely to use theorem-level rules: see the
[worked M5 proof](READING_GUIDE.md#one-checked-proof-the-repaired-m5-collision).

## Classification and comprehension

Read the independent definitions in
[Goodman_Native_T6_Extras.thy](../theories/native_extras/Goodman_Native_T6_Extras.thy).

| Notation | Native declaration | Qualification |
|---|---|---|
| Reversible(Z) | `gb_reversible_on_chart` | A pure two-sided inverse exists; purity of Z is an additional group condition |
| Z∈G | `gb_group_member_on_chart` | Z is pure and reversible |
| X≈Y | `gb_same_kind_on_chart` | There is Z∈G with X = Y∘Z |
| L2 | `gb_L2` | Pure X,Y and fun′ p,q with Xp = Yq imply X≈Y |
| Strong L2 | `gb_strong_L2` | The same witness also satisfies q = Zp |
| Inv | `gb_Inv` | Group members are exactly identity and negation |
| WI | `gb_WI` | Every group member is a biconditional operator with a pure proposition parameter |
| TU | `gb_TU` | Every group member is truth-preserving or truth-flipping |
| RS | `gb_RS` | An instantiated pure rigid specification selecting only fun′ propositions exists |

Composition is on the input side in the kind relation: X = Y∘Z. The strong
input equation is q = Zp, not its reversal. For TU, truth preservation
means a material biconditional at every input; it is not identity with the
identity operator. Recombination and Exhaustion also remain distinct
principles; the repaired central witness/QSS route includes zeroary
Exhaustion.

PC here means pure comprehension when discussing Goodman's semantic
classification principles. Some proof-helper names use PC for propositional
calculus. Context matters: a Boolean tautology rule does not yield pure
comprehension. Finite pure comprehension, comprehension for internally
represented subsets, and T9's full external PC are different strengths.
The latter ranges over every external subset of the stated pure carrier.

## Exact semantic stocks

A raw denotational stock collects values of all closed logical terms at a
specified type. A world-relative native stock additionally uses the exact
model's local Leibniz agreement. The complete old/new stock correspondence
is proved separately from soundness; preserving truth of sentences alone
would not establish it.

An invariant operator is not automatically logically pure. The exact L2
counterexample concerns the specified complete logical stock, not every
possible enlargement of Pure. The M5 enlarged stock includes all closed
typed terms over its new operator, not just a finite list of applications.

The exact construction uses HOL–ZF: `ZF` is the type of internal sets,
`Elem a A` is internal membership, `explode A` is the external HOL set of
members, and `Lambda A f` is a graph on the specified domain. This is not
Isabelle's separate ZF object logic. Exact arrow carriers satisfy Bacon's
action-compatibility condition; they are not arbitrary full function spaces.

Root truth, global validity at all worlds and typed assignments, theoremhood
over a stock, and consistency of that stock are separate assertions.
Likewise a conditional classifier-membership criterion is not a proof of
membership. These distinctions account for the principal scope conditions
in [STATUS.md](../STATUS.md) and the remaining contributor tasks.
