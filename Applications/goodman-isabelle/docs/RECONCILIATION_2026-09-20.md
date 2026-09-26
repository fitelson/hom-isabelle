# Goodman report reconciliation, 20 September 2026

This is the current claim ledger for the report in
[LaTeX](../reports/GOODMAN_VERIFICATION_REPORT_2026-09-20.tex) and
[PDF](../reports/GOODMAN_VERIFICATION_REPORT_2026-09-20.pdf).
It reconciles the seven printed pages of Goodman's July 2026 notes and the
earlier `GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.tex` (updated
5 September) against the present integration, including accepted tasks 1–5.
The earlier report remains unchanged outside this repository.

## Completion boundary

**26 September addendum:** core generic full-C soundness and countably
declared-signature completeness are complete in their explicit nontrivial-
model/minimal-language scope. The application adopts the reviewed source
checkpoint; no Goodman claim classification below changes. Root
consequence does not replace the added-axiom extension. See
[the compatibility review](CORE_UPDATE_2026-09-26.md).

**Task 10's agreed reporting checkpoint is completed; the entire original
formalization goal is not.** Branden explicitly left contributor tasks 6–9
open. Resolving their missing premises by relabeling a conditional theorem
would not be mathematical completion. This ledger marks them open.

This is a statement/scope reconciliation, not a new exhaustive file-by-file
source-fidelity audit of all 303 theories and their core dependencies. The
two retained final-readiness audits supply further review history. Current
formal evidence is the selected serial build, the 87 audit catalogs, and
the actual theorem statements under `verification/audits/`.

**Labels:** checked = verified in the displayed scope; repaired = a corrected
claim is verified while the old version is not endorsed; conditional = the
stated model/stock assumptions remain essential; open = unresolved or
underspecified; historical = not a current verification certificate.

## Background, definitions and proof transfer

| Claim/source | Current evidence | Reconciled statement |
|---|---|---|
| Named H/Classicism/CEV+ transfer | [CEV+ preservation](../theories/replay/Goodman_CEV_Axiom_Preservation.thy), [restricted-signature transfer](../theories/replay/Goodman_Restricted_Signature_Transfer.thy) | Checked forward whole-proof preservation, with closed added source axioms, typed charts, rich names and signature admission. Not unrestricted bidirectional calculus equivalence. |
| Pure/Fun and PP, notes pp.1–2 | [Vocabulary](../theories/axiom_extension/Goodman_Book_Vocabulary.thy), [packages](../theories/axiom_extension/Goodman_Book_Axiom_Packages.thy) | PP at u=t→t is purity of the unary-operator purity predicate. Keep the full QLN and Recombination-only packages distinct; Pure(Fun) is not in the target. |
| QLN arities, notes p.1 | [QLN formulas](../theories/axiom_extension/Goodman_Book_QLN.thy), [exact QLN model](../theories/exact_qln/Goodman_Exact_QLN_Model.thy) | Zeroary/unary instances are checked. Higher arities are vacuous under the single-fundamental, pairwise-distinct premise; that last reduction is a documented mathematical observation, not a separate exported theorem. |
| Recombination ⇒ QSS, notes p.1 | [Preserved bridge](../theories/preserved-additions/central-stock/Bacon_PP_QSS_Recombination_Bridge.thy), [native witness](../theories/central_stock/Goodman_Central_Stock_T6.thy) | Checked modal/unboxed consequence; the QSS and ∃fun′ route uses zeroary Exhaustion and unique fundamentality. A gap in the proposed Recombination-only proof is not itself a nonderivability theorem. |
| Modalized Functionality | [Derived proposition-valued result](../theories/preserved/stage01/Bacon_PP_Modalized_Functionality_Derived.thy), [exact semantic result](../theories/semantics/Goodman_Exact_Modal_Functionality.thy) | CEV derivability at σ→t is distinguished from all-result-type validity in the exact model. Do not claim the full schema redundant over bare CEV. |
| Complete logical stock | [Stock correspondence](../theories/logical_stock/Goodman_Exact_Stock_Correspondence.thy) | `gi_exact_logical_denotation_sets_equal` and `gi_exact_native_stock_iff_original` give full denotation and worldwise correspondence, not merely truth agreement of sentences. |
| Finite support/compactness | [T1/QSS/compactness audit](../theories/individual/Goodman_T1_QSS_Compactness_Audit.thy), [finite support](../theories/replay/Goodman_Extension_Finite_Support.thy) | Checked proof-theoretic finite support. Not semantic compactness, a fair complete search, or models for all finite axiom sets. |
| Elementary biconditional algebra, notes p.2 | [Native algebra](../theories/wi_master/Goodman_Native_Biconditional_Algebra.thy) | Task 3 accepted: self-inverseness over empty stock; companion purity/group membership proved over PP core, not proof of necessity of PP. General composition is an optional additional package. |
| Finite PC, notes p.3 | [Finite PC](../theories/native_extras/Goodman_Native_Finite_PC.thy) | Task 2 accepted: `gi_native_finite_PC`, all types/all finite lengths, empty case, logical purity/application closure only. Not full external PC. Relative consistency follows by weakening the existing no-PP QLN model. |
| TU/RS relation, notes pp.2–3 | [Native witness](../theories/native_extras/Goodman_Native_TU_RS_Witness.thy) | Task 1 accepted: RS, witness purity and specification over PP core + zeroary Exhaustion + ∃fun′ + TU. The contradictory source prose and weaker no-Exhaustion question remain unresolved. Derivability does not presume stock consistency. |

## T- and L-claims

| Source item | Current evidence | Disposition/guard |
|---|---|---|
| T1, p.3 | [T1 transfer](../theories/individual/Goodman_T1_Transfer.thy) | Checked triviality under zeroary Exhaustion and the stated purity/application stock; associated WI/Inv consequence retains its stock. |
| T2a, p.3 | [T2a](../theories/individual/Goodman_T2a_Transfer.thy) | Checked fun′ closure under pure reversibles; negation instance retained. |
| T2b, p.3 | [T2b/c](../theories/individual/Goodman_T2bc_Transfer.thy) | Checked exclusion of truth/falsity and nontriviality under the explicit fun′ antecedent. |
| T2c, p.3 | [T2b/c](../theories/individual/Goodman_T2bc_Transfer.thy) | Checked pure-proposition attainment, without PP. |
| T2d/e/f, p.3 | [T2d/e/f](../theories/individual/Goodman_T2def_Transfer.thy), `gi_T2f_six_distinct` | Possible purity has a route without Persistence; NC(r) false-but-possible and six pairwise distinctions are checked with the required fun′(r) antecedent. Do not globalize a fixed witness assumption. |
| T3, p.3 | [T3](../theories/individual/Goodman_T3_Transfer.thy), `gi_T3_modal_core`, `gi_T3_heredity_with_exhaustion`, `gi_T3_heredity_with_pure_rigidity` | Repaired. Possible identity is not identity. The repaired stocks retain QSS/purity/persistence as stated. The modal-skeleton counterexample is not a full CEV+ countermodel to unqualified heredity. |
| T4, p.3 | [T4/T5](../theories/individual/Goodman_T45_Transfer.thy), `gi_T4_no_higher_fun_prime` | Checked stronger result over T2-min; no PP or fun′(r) premise. Typing/purity of the relevant operator remains. |
| T5, p.3 | [T4/T5](../theories/individual/Goodman_T45_Transfer.thy), `gi_T5_proliferation`, `gi_T5_no_two` | Checked conditional proliferation over PP core, not unconditional witness existence. |
| T6, p.3 | [Native routes](../theories/native_extras/Goodman_Native_T6_Routes.thy), [central-stock routes](../theories/central_stock/Goodman_Central_Stock_T6.thy) | Checked Inv/TU/WI routes with L2, and RS route with strong L2. Original ∃fun′ stocks and repaired fundamental-witness stocks remain different. No PP-alone contradiction. |
| T6 WI master equations, p.3 | [Direct WI transfer](../theories/wi_master/Goodman_WI_Master_Transfer.thy) and its audit | Checked direct argument, with dependency exclusion of completed refutation/ex-falso endpoints; not proof that the WI stock is consistent. |
| T7a, pp.3–4 | [T7](../theories/numbered/Goodman_T7_Transfer.thy), `gi_T7a_closed` | Checked absorption with L2 and actual existence/purity stock. |
| T7b, p.4 | [Contributor task 9](../CONTRIBUTING.md#9-clarify-t7b-and-the-multiple-fundamental-m4-proposal) | Open: the kind-level term, binders and fixed/shifted relations are not uniquely specified. |
| T8, p.4 | [T8](../theories/t8/Goodman_T8_Transfer.thy) | Checked base-kind distinctions, kind uniqueness and 31-element bounds under their separate assumptions; not automatically unbounded growth. |
| T9, p.4 | [Native conclusion](../theories/t9/Goodman_T9_Native_Conclusion.thy), [infinitude](../theories/t9/Goodman_T9_Infinitude.thy) | Conditional abstract argument and actual exact-carrier instance checked. Global purity stock, root L2/∃fun′, and full external PC remain. Arbitrary-model quotient bridge open (task 7). |
| Weak/strong L2, p.2 | [Definitions](../theories/native_extras/Goodman_Native_T6_Extras.thy), [actual counterexample](../theories/exact_l2/Goodman_Exact_L2_Object_Refutation.thy) | Both encoded; fixed complete-stock failure and native root falsity checked. Notes have no separate L1. No countermodel to PP⇒L2 or to arbitrary enlarged-stock L2. |

## Exact M-claims and appendix results

| Claim/source | Current evidence | Reconciled statement |
|---|---|---|
| Exact carriers / Proposition 8 | [Full M-set recursion](../theories/preserved-additions/exact-first/stage02/Bacon_PP_ZF_Full_MSet.thy) | Checked source-constrained domains, action and surjectivity for the represented finite-natural-word construction and chosen individual carrier. No PER replacement or all-monoid generalization. |
| M1 bottom, p.4 | [Bottom classifier](../theories/m_claims/Goodman_Exact_M1_Bottom.thy), `gi_M1_exact_bottom_PP_gvalid` | Checked actual bottom classifier/noncontingency denotation and bottom PP. Not higher-type PP. |
| M1 / fn.59 obstruction | [Exact fn.59](../theories/m_claims/Goodman_Exact_M1_Fn59.thy), [general native semantics](../theories/general_m1/Goodman_General_M1_Native_Semantics.thy) | Checked with Pure(Fun), QSS, fundamental existence/uniqueness, and actual compositional/extension-soundness conditions. Not all H models, and not the PP question without Pure(Fun). |
| M1 unconditional nonmembership | [Exact QLN classifier criterion](../theories/exact_qln/Goodman_Exact_QLN_Model.thy) | Open (task 6). The iff between PP and classifier membership, plus the stronger fn.59 exclusion, does not decide membership unconditionally. |
| M2, p.4 | [Exact M2](../theories/m_claims/Goodman_Exact_M2_Transfer.thy) | Checked invariant-classifier bijection, cardinal comparison and actual collisions. Rejects all-invariants-as-pure under QSS, not logical purity. |
| M3, p.5 | [Algebra](../theories/m_claims/Goodman_Exact_M3_Algebra.thy), [extreme views](../theories/m_claims/Goodman_Exact_M3_Extreme_Views.thy), [topology](../theories/m_claims/Goodman_Exact_M3_Topology.thy) | Actual exact-stock freeness, extreme views and explicit product-meagerness result checked. Generic seed is verified; a particular gluing identification remains task 8. |
| M4, p.5 | [M4 repair](../theories/m_claims/Goodman_Exact_M4_Repair.thy), [no all-view generator](../theories/m_claims/Goodman_Exact_M3_No_All_View_Generator.thy) | Repaired exact-stock construction checked for a suitably chosen branch. Old all-view-fun′ premise proved impossible and removed, not assumed. Multi-fundamental proposal open (task 9). |
| M5 displayed operator, pp.5–6 | [Exotic operators](../theories/m5/Goodman_M5_Exotic_Operators.thy) | Checked fixed length-one pair and a corrected uniform pair. The countable world-indexed family does not support the source's uncountability argument. |
| M5 pre-rebuild QSS obstruction | Same file, `gi_M5_diagonal_pair_avoids_orbit`, `gi_M5_old_seed_QSS_obstruction` | Checked uniform replacement for the failed cardinal selection. Retaining an old seed while enlarging Pure can destroy its fun′ property. |
| M5 actual rebuild | [Rebuilt model](../theories/m5/Goodman_Exact_M5_Rebuilt_Model.thy), [fixed displayed pair](../theories/m5/Goodman_Exact_M5_Fixed_Pair_Model.thy) | Exact-carrier model, complete expanded-language stock and rebuilt seed checked. Explicit no-PP background and QSS; not a PP model and not merely the old secondary comparison model. |
| M5 Inv/WI/TU | [Classification results](../theories/m5/Goodman_Exact_M5_Classifications.thy), [TU](../theories/m5/Goodman_Exact_M5_TU_Refutation.thy) | Actual Inv/TU root failures and native nonderivability. WI nonderivability/global failure uses theorem-level WI⇒TU, not an unproved root implication. |
| M5 local NC(r) collision | [Counterexample](../theories/m5/Goodman_M5_Local_Collision_Counterexample.thy), [fixed axiom collapse](../theories/m5_object/Goodman_Fixed_Fun_Prime_Axiom.thy) | Refuted locally; the older axiom-stock proof is vacuous because a fixed fun′ theorem collapses that stock. Neither fact refutes a local/existential fun′ premise. |
| M5 corrected collision | [Nested proof](../theories/m5_object/Goodman_M5_Nested_Collision.thy), `gi_M5_nested_local_collision`, `gi_M5_nested_local_nonreversibility` | Checked with q=NC(□r), output identity over empty added stock before the local fun′ assumption. Separate exact punctured-truth collision is preserved, not substituted for the object proof. |
| M5 existential-inverse proposal | [Inverse transfer](../theories/m5_object/Goodman_M5_Object_Transfer.thy) and actual exotic model | Inverse ⇒ injective is checked. An unrestricted nonuniform-invertible collision strategy fails; an additional PP-specific constraint is not refuted or supplied. |
| M6, p.6 | [M6 repair](../theories/m_claims/Goodman_Exact_M6_Repair.thy) | Exact instantiations checked, without the old impossible premise. Arbitrary missing target is not promised fun′; distinct kinds do not imply independent realizability. |
| M7, p.6 | [M7](../theories/m_claims/Goodman_Exact_M7_Transfer.thy) | Exact diagonal for every typed R; invariant reachability iff orbit injective; noninjective orbit for exact-stock fun′ inputs and generic seed. Specific gluing identification remains open. |
| Theorem 10.1 | [Parametric gluing](../theories/exact_qln/Goodman_Exact_10_1_Parametric.thy), `gi_exact_Bacon_10_1_parametric` | Task 5 accepted: arbitrary name type, one uniform C, countable branch family, closed t-generated terms. Per-term finite coding is not a global signature injection. Open-term/all-type-e extensions not included. |
| Exact global soundness | [Native soundness](../theories/semantics/Goodman_Exact_Goodman_Soundness.thy), `gi_exact_goodman_extension_global_sound` | Checked in the exact model; global validity of added axioms is a genuine premise, not an omitted proof that the PP stock holds. |
| Appendix QLN assertion | [Exact QLN model](../theories/exact_qln/Goodman_Exact_QLN_Model.thy) | Actual unique-proposition specialization checked. Does not identify this generic interpreter with every Theorem-10.1 gluing or prove the source's broader individual/multiple-fundamental suggestion. |
| Enumeration / frame completeness | [Named representation](../theories/exact_frame/Goodman_Exact_Frame_Representation.thy) and both preserved snapshots | Task 4 accepted, including necessity companion: satisfiable iff ◇ in complete model, valid iff □, with closed string/t-fragment guards. Not H completeness or decidability. Arbitrary-name gluing alone does not extend enumeration. |

## Old report: material corrections and exclusions

| Earlier report passage | Current disposition |
|---|---|
| Opening and conclusion: every determinate claim settled by proving/refuting/qualifying | Withdrawn. Qualifying a missing-premise claim is not completion. Tasks 6–9 remain explicit contributor obligations. |
| Arbitrary-signature 10.1 already complete | Previously too broad for the string theorem; the new task-5 parametric closed-term result now fills that stated name gap, with its remaining fragment/closedness limits. |
| M4/M6 exact-stock instantiations still missing | Outdated: new exact repairs supply them and reject the false all-view-fun′ premise. |
| M5 rebuild only a secondary Boolean-tree comparison | Outdated: current actual exact-carrier rebuild supplies the qualified no-PP independence model. |
| NC(r),⊤ collision whenever fun′(r) | False locally; replaced by the independently checked NC(□r),⊤ conditional derivation. |
| M7 exact diagonal/open invariant instance | Exact diagonal and generic/fun′ invariant obstruction now checked; the particular-gluing question remains open. |
| Model-independent fn.59 with no remaining semantic caveat | Keep the actual native C+[T] soundness interface, QSS, Pure(Fun), and fundamental existence/uniqueness. No automatic adapter for every H or varying-domain model. |
| T9 full model-class conclusion | Exact-carrier/full-external-PC result is substantive but not the arbitrary-Henkin bridge. Neither PC nor L2 is derived from PP. |
| Recombination-only proof gap described as outright nonderivability | Correct to the exact checked bridge and missing modal step. Failure of one proof is not nonderivability from all background axioms. |
| Semantic escape disjunction | T6 excludes simultaneous global validity in a sound model of the relevant stock; no automatic distinguished-root disjunction. |
| PC versus Melianism; fn.60 citation | Retain coextension/identity distinction. Source main-text argument accompanies notes 57–58; note 60 points onward. Do not infer a generic complete-Boolean-lattice theorem from classifier existence alone. |
| Vampire experiments | Historical bounded searches, not rerun here. No failure-to-find-proof is promoted to nonderivability; prior positive solver experiments are not additional current Isabelle certificates. |
| J/S identities and control/range work | Checked conditional results remain in the repository with their exact stocks. Omitted from this source-focused report, rather than advertised as a model of PP or a completed search strategy. |
| Successive modal/Boolean models, SCC/enumerator/fixed-point searches | Outside this report's verified model inventory. No transfer or all-finite-fragment model claim is inferred; historical research remains outside this repo. |
| 167-object older audit and historical build commands | Replaced for this checkpoint by current selected sessions, 1,708 integration entries/87 catalogs plus nine separately counted replay entries, with the unchanged pinned core. |

## Suggested attacks and audit warnings

1. **Attack 1:** exact complete-stock L2 calibration answered negatively;
   PP⇒L2 and arbitrary enlarged-stock versions remain open.
2. **Attack 2:** [granularity](../theories/granularity/Goodman_Granularity_Transfer.thy)
   checks the surjective same-truth-value preservation criterion, the full
   unary QLN agreement/noncontingency equivalence, and conditional cardinal
   ceilings. It does not derive TU or a ceiling from PP.
3. **Attack 3:** the exact/full-external-PC conditional infinitude and
   exponential bound are checked, without iterating T8 or using its abandoned
   two-fun′ premise. General-model transfer is task 7.
4. **Attack 4:** no full PP model or inconsistent finite core is available.
   Proof-theoretic finite support is not semantic compactness/model construction.

For the five warnings on p.7: input/output negation is distinguished in
the native T6 definitions; type-correct local identity is not root truth;
model validity is separated from derivability; orbit injectivity is not
inferred from a stabilizer or monoid cancellation; and the actual M5/M6/M7
constructions keep orbit cardinality separate from fun′ separation.
These are specific safeguards and checked instances, not a claim that
every future use of the library is immune to these errors.

## Contributor disposition

Tasks 1–5 are accepted. Tasks 6–9 are intentionally open for contributors,
not assigned to an ongoing automated run. The revised report and this ledger
complete the agreed task-10 reporting/reconciliation scope. The original
open consistency question remains separate. There is no automatic research
continuation, Fable call, commit, push or publication associated with this report.
