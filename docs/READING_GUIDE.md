# Reading the formalization

Start with one source theorem rather than reading the repository in file order.
The [source table](SOURCE_CORRESPONDENCE.md) points to a definition, its result,
and the scope of the formal claim.

## A first route through H

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

The current modal endpoint is
`book/representation/hol_zf/Bacon_Book_ZF_Ambient_Model_Existence.thy`.
Follow its imports to the canonical interpretation, then compare that
interpretation with the independently defined model and interpretation in
`book/modal_semantics/`.

## Reading a theorem

Read its `fixes`, `assumes`, and `shows`, and any surrounding `locale`
or `context`. A theorem inside a model locale carries that model's hypotheses.
An existential conclusion constructs data; a locale assumption supplies it.

The ASCII input `\\<forall>` renders as ∀ in Isabelle/jEdit.
[Notation](NOTATION.md) explains the major object-language constructors.
The host's implication and equality must not be confused with object-language
formulas represented by those constructors.

Earlier supporting theories are retained because checked source-oriented
proofs and presentation bridges depend on them. Retention does not identify
every historical interface with the source's model definition.
