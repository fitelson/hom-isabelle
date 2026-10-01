# Source correspondence and reading order

Page and result numbers refer to *Classicism*, draft of 1 July 2022.
The model is a new construction investigating that source claim, not a
claim that Bacon or Dorr supplied this particular model.

| Source or mathematical obligation | Isabelle entry point | Scope |
|---|---|---|
| Proposition 2.11, footnote 42(iv), p. 30 | `normalization_fiber_Inf_bottom`, `normalization_does_not_preserve_fiber` | Concrete complete Boolean algebra and its intermediate map |
| The preceding witness conditions in footnote 42 | `footnote_setup_and_normalization_loss` | Concrete profile calculation; the source-formula/actual-LUB bridge for the footnote is not certified (not needed for the refutation) |
| Rigid Comprehension, pp. 27–28 (earlier profile component) | `no_rigid_profile_for_zero_fiber` | Explicit HOL profile definitions; superseded by the source-formula endpoints below |
| All-type construction supporting the proposed example | `typed_R_joint_surjective`, `typed_R_extensional` | Genuine recursive ZF carriers; finite terminal domains and a free ultrafilter |
| Book Definition 18.1 | `src_model`, `src_nontrivial_model` | Prescribed future-set/function graphs and operations; includes worldwise nontriviality |
| Book Definition 17.13 / interpretation existence | `src_interpretation_exists` | Constructed from modelhood via the core's checked generic theorem, not a supplied interpreter |
| Full-type C soundness for that interpretation | `src_full_C_interpretation` | Book minimal language; rich-stock guard retained |
| Paper Definition 3.18, p. 55 | `paper_premodel` | Actual coded category and literal powerset/exponential subactions |
| Paper Definition 3.19, p. 56 | `paper_primitive_identification` | All six literal primitive graph clauses |
| Paper Definition 3.20, p. 56 | `concrete_paper_action_model`, `concrete_paper_standard_model` | Exact independent model predicate; second endpoint supplies the standard variable stock |
| Definition 3.20, term-level totality | `concrete_paper_term_totality` | Every R-language term, legitimate root arrow, typed adequate partial assignment |
| Theorem 3.23, soundness corollary | `concrete_paper_classicism_truth` | Every paper-R C theorem is true at every root arrow under a typed adequate assignment in the constructed model |
| Figure 1, p.6: lifted ¬, ∧, ∨; □; ≤ | `c211_not`, `c211_and`, `c211_or`, `paper_R_named_box`, `c211_leq` | Closed named-syntax λ-terms over the standard stock |
| Boolean Completeness, GLB, LB, pp.23–24 | `c211_BC`, `c211_GLB`, `c211_LB` (`c211_LB_printed`) | Intended LB clause ∀y(Xy → z ≤ y); the printed clause is kept separately and unused |
| Atom, Atomicity, p.24; □Atomicity | `c211_atom`, `c211_atomicity`, `c211_box_atomicity` | Literal biconditional and disjunction |
| BF, p.20 | `c211_BF` | Every R type σ, binder, formula P (open or closed) |
| Rigid, Rigid Comprehension, pp.27–28 | `c211_rigid`, `c211_RC` | Vector form; refuted instance `c211_RC [Prop]` (type t→t) |
| "jointly imply": H-theories, pp.7–8; C, p.12 | `c211_proves`, `c211_proves_least`, `c211_soundness` | Smallest set containing C and the hypotheses, closed under MP, Gen, Inst; no Necessitation for hypotheses |
| Proposition 2.11 hypotheses and conclusion, p.30 | `c211_hypotheses`, `c211_conclusion` | All relational types for □Atomicity and BC; all R types for BF |
| Definition 3.19 truth clauses, generic | `c211_box_holds`, `c211_le_holds`, `c211_le_neg_holds`, `c211_atom_holds`, `c211_atomicity_holds`, `c211_BC_valid`, `c211_rigid_holds`, `c211_RC_holds_root` | Every action model; semantic application of closed constants, no syntactic β |
| Proposition 3.24(ii), p.58 and fn.80 | `c211_BF_valid`, `c211_BF_concrete` | Root-arrow surjectivity gives every BF instance |
| Complete atomic relational algebras (note §4) | `c211_root_realize_ex1`, `c211_rleq_root`, `c211_rcur_limit_ulim`, `c211_raw_complete`, `c211_raw_atomic`, `c211_transfer_complete`, `c211_transfer_atomic` | Every world; limit coordinate rebuilt by ultralimit |
| Failure of Rigid Comprehension (note §6) | `c211_raw_rigid_A0_fails`, `c211_prigid_transfer`, `c211_concrete_pRC_false`, `c211_conclusion_not_valid` | Outer □ instance at the intermediate world |
| **Proposition 2.11 refuted** | **`proposition_2_11_refuted`** | Premise-free; intended LB clause |

The three representations must not be conflated. `Typed_*` first constructs
compatible tuples and graphs; `Typed_Source_*` encodes them as the book's
future-world sets and function graphs; `Typed_Paper_*` relabels coordinates
as the paper's outgoing arrows. Both encodings are proved injective and
application preserving. The last interpretation proof compares the actual
paper evaluator with a constructed book interpreter, preserving partial
assignment adequacy and arbitrary future arguments under abstraction.

The metatheory is standard Isabelle/HOL plus HOL–ZF and the standard free
ultrafilter existence theorem. The use of metatheoretic choice is not an
object-language choice axiom. No PER domains, new axioms, or assumed
logical-stock/modelhood fields replace the source constructions.

Start with `Classicism_Normalization_Core.thy`, then
`Typed_Root_Hierarchy.thy`, `Typed_Source_Model.thy`,
`Typed_Paper_Model.thy`, and, for the refutation,
`refutation/assembly/Classicism_2_11_Refutation.thy`. Follow their imports for the supporting proofs.
`Classicism_2_11_Audit.thy` exports the selected endpoint statements and
their proof-dependency checks. `Classicism_2_11_Refutation_Audit.thy` does the same for the refutation
endpoints and requires the main theorem to be premise-free.

The note numbers the terminal worlds n from 1. Isabelle numbers their
labels from 0 and sets `raw_leaf n = nat2Nat (n+3)`, reserving 0, 1 and 2
for o, s and u. This is an index renaming, not a different frame.
