# A model concerning Classicism Proposition 2.11

This application investigates the normalization in footnote 42 and the
claim that **□Atomicity, Boolean Completeness, and BF imply Rigid
Comprehension**, in the 1 July 2022 draft of Bacon and Dorr's *Classicism*
(Proposition 2.11, printed p. 30).

The [technical note](reports/NOTE_ON_PROPOSITION_2_11.pdf) gives the
counterexample and its mathematical argument. **Isabelle now certifies the
refutation end to end**: in the concrete action model every Classicism theorem
and every instance of □Atomicity, Boolean Completeness and BF is valid,
while the Rigid Comprehension instance for properties of propositions is
false, so that instance is not derivable in the smallest H-theory
containing Classicism and the hypotheses (`proposition_2_11_refuted`, with
no premises).

## The idea

The worlds are a root o, an intermediate world s, a terminal world u,
and countably many other terminal worlds n. The nonidentity arrows are
o→s→u (including the composite) and o→n. A free ultrafilter U relates
truth at u to truth along the n-worlds.

A root proposition is represented initially by three independent pieces
of data: its o-bit, its s-bit, and its sequence of n-bits. Its u-bit is
the U-limit. The resulting Boolean algebra is complete and atomic, but
the map to the intermediate Boolean algebra does not preserve arbitrary
meets. A fiber whose every member maps to the atom (0,1) has meet ⊥,
which maps to (0,0). This is the normalization failure tested here.

Constructing only that Boolean algebra would not suffice. The theories
also build domains at every simple type, prove the naturality and
surjectivity of their maps, construct logical operations and K/S, recode
values as the prescribed sets and graphs, and verify total interpretation
of the paper's typed terms, including abstraction at all future arguments.
The refutation layer (`theories/refutation/`) then writes the source's
formulas as object-language terms, proves what they mean in every action
model, establishes the complete atomic relational algebras at every world
of the concrete model, and refutes the Rigid Comprehension instance.

## Read or check

- [Exact checked scope and remaining work](STATUS.md)
- [Source statements and theorem entry points](docs/SOURCE_CORRESPONDENCE.md)
- [Contributor projects](CONTRIBUTING.md)
- [Verification and foundations](docs/VERIFICATION.md)
- [Technical note source](reports/NOTE_ON_PROPOSITION_2_11.tex)

From the repository root, with Isabelle2025-2 and Python 3.9+ available:

```sh
./Applications/2.11/check_isabelle.sh
```

Run this separately from the core and Goodman checks. The application has
its own ROOT and audits; the core ROOT is unchanged. No AI service, Vampire,
or access to the original research directory is needed. TeX Live and Lucida
are needed only to rebuild the optional PDF, not to check the proofs.

The application uses the enclosing core and standard Isabelle libraries,
including HOL–ZF. Its source-model bridge does not postulate modelhood,
an interpreter, logical closure, or a full function space at the root.

## Sources and credit

Andrew Bacon and Cian Dorr, [*Classicism*, 1 July 2022 draft](https://andrew-bacon.github.io/papers/Classicism.pdf),
especially Proposition 2.11, footnote 42 and Definitions 3.18–3.20.
The intermediate modal-model construction uses Chapters 17–18 of Bacon's
*A Philosophical Introduction to Higher-order Logics*, with the enclosing
core's documented future-restricted implication convention. The paper-side
endpoint separately checks the paper's own six primitive clauses.

Branden Fitelson developed this application with AI assistance. The proposed
counterexample is not attributed to Bacon or Dorr, and no endorsement by
them is implied. The enclosing BSD-2-Clause software license applies;
source publications are not redistributed or licensed by it.
