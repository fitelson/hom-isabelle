# Reading the formalization

Start with one source theorem rather than reading the repository in file order.
The [source table](SOURCE_CORRESPONDENCE.md) points to a definition, its result,
and the scope of the formal claim.

## A first route through H

Begin with the small proof below, then follow this route as needed:

1. `theories/base/source_vocabulary/Bacon_Source_Named_Syntax.thy`:
   named expressions, types, and their representation.
2. `Bacon_Source_Named_H.thy` in that directory:
   the independent source-style H rules.
3. `theories/base/source_models/Bacon_Source_Named_H_Soundness.thy`:
   native soundness.
4. `Bacon_Source_Named_Closed_Strong_Completeness.thy`:
   the quantified semantic consequence definition and the two directions.

For the book's own minimal language, use
`theories/base/book_models/Bacon_Book_Printed_Completeness.thy` and follow
its imports to the independent calculus, model class and canonical construction.

The relevant (λI) language of Definition 9.2 has its own session,
`Bacon_Book_Lambda_I_Development` under `theories/base/book_lambda_I/`,
which replays the same route inside the fragment and ends in
`Bacon_Book_Lambda_I_Canonical_Completeness.thy`; its audit theory lists the
checked endpoints and the open identification questions.

## One small checked proof

Open
[Bacon_Source_Named_H_PC_Basics.thy](../theories/base/source_vocabulary/Bacon_Source_Named_H_PC_Basics.thy)
and find `paper_named_H_iff_refl`. This is an existing checked lemma,
not an unfinished exercise. Its statement is:

```isabelle
lemma paper_named_H_iff_refl:
  assumes rich: "sg_rich G" and A: "named_in_language paper_logical_type \<Sigma> G A Prop"
  shows "paper_named_H \<Sigma> G (named_paper_iff G A A)"
```

We fix a declared signature Σ, a rich stock G of typed variable names,
and a formula A in that language. The conclusion says that H proves
A ↔ A. It does not assume that A is true or that H proves A.

Proof. The finite Boolean template `SPIff (SPAtom 0) (SPAtom 0)` is a
tautology: each Boolean value agrees with itself. The proof instantiates
its atom by the object-language formula A. The lemma
`paper_named_H_PC_instance` applies H's propositional rule to this
tautology; its remaining obligations are exactly the rich-stock and
formula-language assumptions. Expanding the template instantiation gives
`named_paper_iff G A A`, so H proves A ↔ A. ▪

The source proof uses `let ?P` to name the template, `have` to establish
intermediate facts, and `show ?thesis` to finish the stated conclusion.
The notation `[OF rich taut]` supplies already proved facts to a lemma.
None of those commands adds a rule to the object-language calculus.

Keep these different expressions apart:

| Isabelle expression | What it says |
|---|---|
| `named_paper_iff G A A` | The object-language formula A ↔ A, not a proof assertion |
| `paper_named_H Σ G (named_paper_iff G A A)` | H proves that formula |
| `paper_named_derivable Σ G {A} A` | A is derivable in the project's local relation with A as a premise, provided A is in the language; use `paper_named_derivable.Assumption` |
| `A = A` | Isabelle/HOL equality of the represented syntax with itself |
| `named_paper_eq σ A B` | An object-language identity formula, when A and B have type σ |

In particular, local derivability from `{A}` is not theoremhood with no
premises, and H's theorem A ↔ A is not an identity of propositions licensed
merely by host equality. The [notation guide](NOTATION.md) gives the actual
paper/book constructors for the logical symbols.

To inspect this proof interactively, run from the repository root:

```sh
isabelle jedit -d . -R Bacon_Source_Vocabulary_Development theories/base/source_vocabulary/Bacon_Source_Named_H_PC_Basics.thy
```

The `-R` option prepares the session's requirements and lets the selected
session's source theories be explored. It may build a session image, so do
not start it beside another Isabelle build or graph extraction. A focused
terminal check is
`isabelle build -j 1 -d . -o timeout=60 -o export_theory=true Bacon_Source_Vocabulary_Development`.

## A route through Classicism

For the paper, start in `theories/classicism/action_models/`.
`Bacon_Source_Relational_Arbitrary_Signature_Classicism_Completeness.thy`
states the BBK-category endpoint; its proof refers to the constructed
bounded category rather than assuming the desired representation.

Then read
`hol_zf/Bacon_Source_ZF_Arbitrary_Signature_Action_Completeness.thy`.
The source R-language guard and explicit world-label carrier are part of
the theorem, not cosmetic annotations.

For the book's full-type C, start with
`theories/classicism/book/Bacon_Book_Full_Classicism_Calculus.thy`.
Its rules include all-type Modalized Functionality and Propositional
Equivalence. The older `book_C_proves` is a separately defined base.
Do not transfer consistency merely by adding axioms.

The source-directed model-existence endpoint is
[`book_full_C_small_declared_nontrivial_modal_model_exists`](../theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Declared_Names_Existence.thy).
It constructs an original-signature model satisfying the consistent theory,
with every type domain inhabited at every world and a proposition false at
each world. Its signature hypothesis is that the union of the declared
constants admits an injective code into the elements of some ZF set, on an
arbitrary name carrier; the countably declared instance
[`book_full_C_countable_nontrivial_modal_model_exists`](../theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Countable_Nontrivial_Existence.thy)
is retained and re-derived from it. The rich-stock and
full-minimal-language conditions remain. Follow its imports to the
small-carrier, fixed-ambient and canonical nontrivial constructions.

Compare the explicit refinement
[`book_ZF_nontrivial_modal_model`](../theories/classicism/book/modal_semantics/hol_zf/Bacon_Book_ZF_Nontrivial_Model.thy)
with the unchanged weaker `book_ZF_modal_model`. The older endpoint in
`Bacon_Book_ZF_Countable_Model_Existence.thy` remains available; it does not
state the additional worldwise conditions. The refinement's source comment
explains the Chapter 15/18 issue motivating the stronger model class.

For generic interpretation existence, start with
`theories/classicism/book/modal_semantics/interpretation/Bacon_Book_ZF_Generic_Interpretation_Existence.thy`.
Its imports separate typed combinatory translation, generic evaluation,
and the proof that abstraction has the exact future Lambda graph. It uses
the weaker independent model fields, not the canonical construction, and
therefore also applies to the nontrivial subclass. The generic connective
truth clauses and full-C soundness are proved in
`theories/classicism/book/modal_semantics/soundness/`
(`Bacon_Book_ZF_Modal_Truth_Clauses.thy`, `Bacon_Book_ZF_Full_C_Soundness.thy`;
see [STATUS.md](../STATUS.md)); rerooting remains a separate task.

## Reading a theorem

Read its `fixes`, `assumes`, and `shows`, and any surrounding `locale`
or `context`. A theorem inside a model locale carries that model's hypotheses.
An existential conclusion constructs data; a locale assumption supplies it.

The ASCII input `\<forall>` renders as ∀ in Isabelle/jEdit.
[Notation](NOTATION.md) explains the major object-language constructors.
The host's implication and equality must not be confused with object-language
formulas represented by those constructors.

Earlier supporting theories are retained because checked source-oriented
proofs and presentation bridges depend on them. Retention does not identify
every historical interface with the source's model definition.

For dependency navigation, use the [native graph](KNOWLEDGE_GRAPH.md) to
locate named declarations rather than reading every imported theory in
order. If a short name is ambiguous, run `search` and copy the complete
returned node ID into `explain`, for example
`constant:Bacon_Book_Full_Classicism_Calculus.book_full_C_proves`.
The graph's exported term trees are machine representations; the linked
theory statement is the readable mathematical entry point. Older retained
files can be much longer than the source-facing theories listed here.
