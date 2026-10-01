# Checked scope

30 September 2026. **Proposition 2.11, with its intended lower-bound
clause, is refuted by an end-to-end Isabelle certificate.** The main theorem

```
proposition_2_11_refuted:
  ¬ c211_proves S c211_G (c211_hypotheses S) c211_conclusion
```

has no premises. It says that the Rigid Comprehension instance for
properties of propositions (type t→t) is not derivable in the smallest
H-theory containing Classicism and every instance of □Atomicity, Boolean
Completeness and BF, for an arbitrary signature S over the standard rich
variable stock. Build evidence and the trust boundary are recorded in
[verification](docs/VERIFICATION.md). Commit and push await explicit
direction.

| Claim | Status |
|---|---|
| Equality-fiber meet is ⊥ and its intermediate image loses the original atom | Checked in the concrete Boolean algebra |
| Actual carriers at every simple type; joint surjectivity, natural application, extensionality | Checked in HOL–ZF |
| Bacon's book model predicate and full typed interpretation; paper Definitions 3.18–3.20 | Checked; the paper model is literal, with an explicit standard rich stock |
| Every paper-R Classicism theorem is valid in the concrete model | Checked (core action-model soundness) |
| Object-language formulas of Figure 1, Atom, Atomicity, □Atomicity, LB/GLB, Boolean Completeness, BF, Rigid and Rigid Comprehension | Defined literally as named-syntax terms over the standard stock; language membership checked; operator constants and designated sentences are closed; BF instances may be open |
| "Jointly imply": smallest H-theory containing C and the hypothesis instances (MP, Gen, Inst; no Necessitation for the hypotheses) | Defined (`c211_proves`); soundness for every action model checked |
| In every action model: □ is truth at every outgoing arrow; ≤ is leafwise inclusion; x ≤ ¬x is emptiness; Atom, Atomicity, □Atomicity read order-theoretically; external completeness implies Boolean Completeness; Rigid and Rigid Comprehension at t→t have their intended readings | Checked generically |
| Proposition 3.24(ii): surjective root actions give every BF instance | Checked generically, and in the concrete model |
| Concrete relational carriers: realization (existence and uniqueness from free coordinates), coordinate order, ultralimit of relations, GLB-completeness and atomicity at every world | Checked; the limit coordinate is always rebuilt by ultralimit, never intersected |
| Every instance of □Atomicity and Boolean Completeness (all relational types) and BF (all R types, all formulas) is valid in the concrete model | Checked (`c211_hypotheses_valid`) |
| The Rigid Comprehension instance at t→t is false at the root | Checked (`c211_conclusion_not_valid`) |
| **Proposition 2.11 (corrected LB) does not hold** | **Checked (`proposition_2_11_refuted`)** |

The refutation concerns the intended lower-bound clause ∀y(Xy → z ≤ y).
The printed clause on p. 24 has the inequality reversed; with it Boolean
Completeness contradicts Booleanism, so no countermodel to the literal text
exists. The printed clause is kept in the sources as `c211_LB_printed` but is
not used. The reference to Proposition 2.6 in footnote 42(ii) should be to
2.7. Neither repair supplies the meet preservation used by the normalization.

Not machine-checked, and not needed for the refutation: the boxed forms
□Boolean Completeness and □BF, the identification of the footnote's X* with
an actual LUB, and an object-language proof that the printed LB clause is
inconsistent. The note's mathematical argument for these remains review
evidence only.

Independent review: the joint Opus 5.5 High / Astra High audit of the note
reached consensus on 30 September 2026 ([response](docs/CONSENSUS_AUDIT_2026-09-30.md)).
The formalization plan and each of its phases were then reviewed by Astra
(gpt-6-astra, High); every finding was resolved before the next phase.
Review is additional source checking, not a replacement for the kernel.
