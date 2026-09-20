# Source claims and Isabelle entry points

Current detailed ledger: [20 September reconciliation](RECONCILIATION_2026-09-20.md).
The [report](../reports/GOODMAN_VERIFICATION_REPORT_2026-09-20.pdf) incorporates
accepted tasks 1–5; tasks 6–9 remain open contributor projects.

This is a navigation and scope guide, not a claim that every determinate
statement in the sources has been verified. Numbering follows Goodman's
July 2026 notes and the editions listed in
[SOURCES_AND_CREDITS.md](SOURCES_AND_CREDITS.md). Read each theorem's actual
premises and enclosing locale before reusing it.

## Object-language claims

| Source item | Entry point | Scope or correction |
|---|---|---|
| H and CEV+ background | [Whole-proof preservation](../theories/replay/Goodman_CEV_Axiom_Preservation.thy) | Forward transfer into the independent named axiom extension; closed source axioms, typing and signature conditions remain. |
| Recombination/QSS/∃fun′ | [Central-stock T6](../theories/central_stock/Goodman_Central_Stock_T6.thy) | Zeroary Exhaustion is explicit in the repaired bridge. |
| T1 | [T1 transfer](../theories/individual/Goodman_T1_Transfer.thy) | Read the actual zeroary Exhaustion and purity stock. |
| T2 | [T2a](../theories/individual/Goodman_T2a_Transfer.thy), [T2b/c](../theories/individual/Goodman_T2bc_Transfer.thy), [T2d/e/f](../theories/individual/Goodman_T2def_Transfer.thy) | Separate nontriviality, attainment, closure and distinctness hypotheses. T2f is not an unguarded assertion about all propositions. |
| T3 | [Corrected T3](../theories/individual/Goodman_T3_Transfer.thy) | Distinct modal and repaired heredity claims; not the original unqualified statement. |
| T4–T5 | [T4/T5 transfer](../theories/individual/Goodman_T45_Transfer.thy) | T5's stated antecedent remains part of the theorem. |
| Biconditional operators, p.2 | [Native algebra](../theories/wi_master/Goodman_Native_Biconditional_Algebra.thy) | `gi_native_bic_self_inverse` (any stock), `gi_native_bic_operator_pure`, `gi_native_bic_group_member` (proved here over the T6 PP core): "for any pure proposition A, λp.(p ↔ A) is in G and is its own inverse" (independently checked and accepted, 20 Sept 2026). Necessity of PP is not established. Not WI or Inv. |
| T6 | [Native extras](../theories/native_extras/Goodman_Native_T6_Extras.thy), [native routes](../theories/native_extras/Goodman_Native_T6_Routes.thy) | Inv, TU, WI and strong-L2+RS routes retain their extra premises; none is PP-alone inconsistency. |
| T7a | [T7 transfer](../theories/numbered/Goodman_T7_Transfer.thy), `gi_T7a_closed` | Absorption with the stated L2/purity stock. T7b lacks a uniquely specified source formula. |
| T8 | [T8 transfer](../theories/t8/Goodman_T8_Transfer.thy) | Separate purity, kind and cardinal-growth claims; does not supply arbitrary-finite all-type PC automatically. |
| T9 / Attack 3 | [Native conclusion](../theories/t9/Goodman_T9_Native_Conclusion.thy), [infinitude](../theories/t9/Goodman_T9_Infinitude.thy) | Abstract conditional theorem and exact-carrier instantiation; full external PC. General-model quotient bridge remains. |
| TU and RS, pp.2–3 | [Explicit witness](../theories/individual/Goodman_TU_RS_Witness.thy), [native transfer](../theories/native_extras/Goodman_Native_TU_RS_Witness.thy) | Constructor proof with zeroary Exhaustion; native `gb_RS`, witness-purity and uniform witness-specification endpoints over `gb_TU_RS_axioms` (independently checked and accepted, 20 Sept 2026). The conflicting source remarks remain unresolved; no claim is made that Goodman intended the incomparability remark only for the weaker scope without Exhaustion. |
| Finite PC, p.3 | [Native finite PC](../theories/native_extras/Goodman_Native_Finite_PC.thy) | `gi_native_finite_PC`: all-type, arbitrary-n finite pure comprehension from the logical-purity and application-closure schemas alone (independently checked and accepted, 20 Sept 2026). Finite only; not comprehension for arbitrary, potentially infinite external subsets and not T9's external full PC. |

## L- and model claims

| Source item | Entry point | Scope or correction |
|---|---|---|
| L2 | [Actual formula refutation](../theories/exact_l2/Goodman_Exact_L2_Object_Refutation.thy) | `gi_exact_generic_L2_false_at_root` and `gi_exact_QLN_background_not_proves_L2`; full fixed logical stock, specified no-PP model. |
| Complete logical stock | [Stock correspondence](../theories/logical_stock/Goodman_Exact_Stock_Correspondence.thy) | Denotation-set equality and worldwise saturation, not merely truth preservation of sentences. |
| M1, bottom type | [Bottom classifier](../theories/m_claims/Goodman_Exact_M1_Bottom.thy) | `gi_M1_exact_bottom_PP_gvalid`; higher-type PP is a different instance. |
| M1 / Bacon footnote 59 | [Exact diagonal](../theories/m_claims/Goodman_Exact_M1_Fn59.thy), [general native bridge](../theories/general_m1/Goodman_General_M1_Native_Semantics.thy) | Qualified obstruction with Pure(Fun), fundamentality and the appropriate extension-soundness interface; not unconditional classifier nonmembership. |
| M2 | [Exact M2](../theories/m_claims/Goodman_Exact_M2_Transfer.thy) | Invariant-carrier/cardinality obstruction; invariance is not logical purity. |
| M3 | [Algebra](../theories/m_claims/Goodman_Exact_M3_Algebra.thy), [topology](../theories/m_claims/Goodman_Exact_M3_Topology.thy) | Exact freeness/algebra and explicit product-meagerness formulation; generic seed not silently identified with arbitrary gluing. |
| M4 | [Repaired M4](../theories/m_claims/Goodman_Exact_M4_Repair.thy) | Actual chosen branch-lift construction for the stated fun′ input, not a predetermined branch in all cases. Multiple-fundamental proposal remains underspecified. |
| M5 rebuilt model | [Exact rebuild](../theories/m5/Goodman_Exact_M5_Rebuilt_Model.thy), [fixed pair](../theories/m5/Goodman_Exact_M5_Fixed_Pair_Model.thy) | Actual complete expanded-language stock on exact carriers; explicit no-PP background. |
| M5 classifications | [Inv/WI consequences](../theories/m5/Goodman_Exact_M5_Classifications.thy) | Root failures where proved, and separate theorem-level nonderivability; not an unproved root WI⇒TU implication. |
| M5 collision | [Counterexample](../theories/m5/Goodman_M5_Local_Collision_Counterexample.thy), [nested repair](../theories/m5_object/Goodman_M5_Nested_Collision.thy) | Old NC(r) pair refuted locally; replacement NC(□r) conditional collision and nonreversibility verified. |
| M6 | [Repaired M6](../theories/m_claims/Goodman_Exact_M6_Repair.thy) | Exact separation/orbit constructions without the impossible old all-view premise. Missing arbitrary target need not itself be fun′. |
| M7 | [Exact M7](../theories/m_claims/Goodman_Exact_M7_Transfer.thy) | Complete-stock diagonal and generic/fun′ orbit collision; particular glued-seed identification remains separate. |

L2's failure in the no-PP model does not decide whether L2 follows after
adding PP. Earlier failed Vampire searches are not proofs of underivability.
Other L-principles must be read through their definitions and the conditional
T6/T7/T9 dependencies, not treated as unconditional consequences merely
because they occur in a successfully checked proof.

## Bacon's exact appendix construction

Proposition 8 and Theorem 10.1 here are in *Logical Combinatorialism*.
The exact recursion begins in
[Bacon_PP_ZF_Full_MSet.thy](../theories/preserved-additions/exact-first/stage02/Bacon_PP_ZF_Full_MSet.thy).
It implements the constrained function-space action, not PER substitute
domains. Its proposition carrier is the represented finite-word tree
instance and the individual carrier is the chosen singleton instance;
this is not an all-monoid/all-individual-carrier generalization.

[Named Theorem 10.1](../theories/exact_qln/Goodman_Exact_10_1_Transfer.thy)
retains string names and the t-generated fragment; the
[name-parametric version](../theories/exact_qln/Goodman_Exact_10_1_Parametric.thy)
(task 5, independently checked and accepted) extends it to an arbitrary type of constant
names, keeping the t-generated fragment and the countable branch family. The
[native extension soundness theorem](../theories/semantics/Goodman_Exact_Goodman_Soundness.thy)
assumes global validity of the added stock, as soundness requires.
The two preserved enumeration/frame-representation files are now selected
(task 4, independently checked and accepted); both the satisfiability/possibility
and validity/necessity characterizations are transferred to closed named sentences in
[Goodman_Exact_Frame_Representation.thy](../theories/exact_frame/Goodman_Exact_Frame_Representation.thy),
where consistency means satisfiability on the fixed frame, not syntactic H
consistency. See [STATUS.md](../STATUS.md#formerly-included-but-not-selected).

## Audits and outstanding reconciliation

The retained [object audit](FINAL_OBJECT_CLAIM_AUDIT.md) and
[model audit](FINAL_MODEL_CLAIM_AUDIT.md) reviewed the integration against
the seven-page notes and the historical report
`GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.tex`.
The latter remains a private reference outside this repository. Ask the
maintainer for the relevant authorized material when reconciling its claims.
The audits contain dated baselines, followed by the M5 completion notice;
they are not evidence that every theory file received a complete review.

The corrected report and current claim ledger are now supplied for the
agreed reporting checkpoint. The open mathematics and exhaustive source-audit
work remain contributor projects. This guide intentionally marks unresolved
claims rather than repeating the old report's blanket verification language.
