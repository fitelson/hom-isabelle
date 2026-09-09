# Source statements and formal endpoints

The numbering for the paper refers to the 1 July 2022 draft.
This is a curated entry-point table, not a claim that every statement in
either source has been formalized. Search theorem names in Isabelle/jEdit
or the [native graph](KNOWLEDGE_GRAPH.md).

| Source | Formal endpoint | Exact reading |
|---|---|---|
| Bacon–Dorr, Figure 2 | `paper_named_H` | Independent ten-constructor named H presentation |
| Bacon–Dorr, Theorem 3.2 | `paper_named_BBK_model_existence`, `paper_named_closed_strong_completeness` | Full-F sentence-set model existence and closed strong completeness; rich stock and explicit carrier |
| Theorem 3.2, countable refinement | `paper_named_BBK_countable_signature_model_existence`, `paper_named_nat_closed_strong_completeness` | Countably declared signatures, literal natural-number domains; not a countability assumption on the ambient name type |
| Bacon, Definition 14.13 | `book_environment_conditions` and its equivalence lemmas | Exact environment condition with agreement on the intersection of free-variable sets |
| Bacon, Proposition 15.5 | `book_proposition_15_5_full_minimal` | Actual Leibniz quotient for the full minimal profile, with explicit definedness assumptions |
| Bacon, Theorem 15.3 / Corollary 15.2 | `book_printed_canonical_model_existence`, `book_printed_canonical_strong_completeness` | Original-signature full-minimal models and global consequence, including open S and A |
| Bacon–Dorr, Appendix A.2–A.3 | `paper_R_classicism_proves` / `paper_R_equivalence_proves` correspondence | Native R p.12/p.14 presentations; not an automatic claim about every finite presentation |
| Bacon–Dorr, Theorem 3.12 | `paper_R_arbitrary_signature_classicism_selected_category_iff` | All independent intensional selected categories on the displayed sufficiently large value carrier |
| Bacon–Dorr, Theorem 3.23 | `paper_ZF_arbitrary_signature_action_iff` | R single-formula action completeness at arbitrary signatures; explicit HOL–ZF and world-label scope |
| Bacon, p.160 and p.178 endnote 5 | `book_full_C_proves` | Full-F H+MF+PE, distinct from the older Equivalence-rule base |
| Bacon, Definition 18.1 | `book_ZF_modal_model` | Independent modal model definition, with the explicitly documented future-restricted implication convention |
| Bacon, Proposition 18.5 | `full_ZF_canonical_modal_model` | Complete canonical model certificate under the current countable-ambient frame assumptions |
| Bacon, Definition 17.13 | `full_ZF_canonical_interpretation` | Canonical instance of the independent interpretation clauses; generic existence remains open |
| Bacon, Proposition 18.6, truth step | `full_ZF_original_theory_satisfied` | Original-theory satisfaction when the root contains its universal closures |
| Bacon, Theorem 18.4, existence direction | `book_full_C_ambient_modal_model_exists` | Actual model existence in a fixed countable ambient signature with infinite reserves; not full completeness |
| Bacon, Theorem 18.4, countably declared signature instance | `book_full_C_countable_modal_model_exists` | Actual original-signature model and interpretation satisfying the entire consistent theory, including open formulas and infinite premise sets; arbitrary name carrier, countably many declared constants per type, no original spare-name premise; not generic soundness or unrestricted completeness |
| Auxiliary signature transport | `signature_pullback_model`, `signature_pullback_interpretation` | Generic semantic pullback, without injectivity or countability assumptions |

## Avoiding overstatement

For each entry, inspect the surrounding locale and the actual theorem.
Do not discard signature restrictions, richness, closedness, carrier bounds,
adequacy, or model premises when presenting a result.

The local source has explicit comments about corrections and representation
choices. The future-restricted implication convention and the book proof's
universal-closure treatment of open premises are especially important
source-review points. They are not silently interchangeable with a literal
transcription of every printed clause.
