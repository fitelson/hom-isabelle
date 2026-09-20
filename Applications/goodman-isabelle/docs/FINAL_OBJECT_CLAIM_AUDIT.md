# Final-readiness audit: object-language and proof-theoretic claims

**Standalone provenance note:** this is a retained review of the integration
workspace, not a new review of every file in this repository. Old relative
paths and export names below identify that workspace's historical evidence.
Use [SOURCE_CORRESPONDENCE.md](SOURCE_CORRESPONDENCE.md) for current paths,
[STATUS.md](../STATUS.md) for current coverage, and `verification/audits/`
for the standalone release's exported certificates. The old report and
source PDFs are not distributed here.

**20 September follow-up:** the M5 nested-input obligation below is now
discharged. The corrected local collision and nonreversibility implications
passed independent source review, serial rebuild, proof-node provenance
audit and export (21 endpoints). Read
[the completed repair](M5_NESTED_COLLISION_REPAIR.md).
This closes item 2 below, not the other audit obligations. The original
19 September findings are preserved at their stated baseline.

19 September 2026. Read-only audit, except for this document.

## Evidence and scope

I read the complete extracted text of all seven printed pages of
`Higher_Order_Metaphysics/sources/pdfs/Goodman_PP_Project_Notes.pdf`, not
merely the previous verification matrix. The source date is July 2026.
I also inspected the historical report
`GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.tex`, particularly its
opening claims, definitions, T1–T9 table, L2 section, J/S proof, T9 and
granularity arguments, remaining-work list, and conclusion.

For verification evidence I inspected the current theory definitions and
proofs and the exported statements in the object-and-exact, exact-QLN,
L2/10.1/T7-final, M123467/T8-final, and residual-results export snapshots.
The last checked baseline available for this audit is the 20:21:32 build:
1,553 cataloged theorem objects in 81 catalogs, 80 preserved proof bodies.
Those counts do not establish source correspondence or completeness.
The files were inspected; I did not run another build, export, or oracle
audit. The coordinator's successful build and exported catalogs provide
that separate evidence.

This is the **object/proof-claim** part of the final audit. Exact M1–M7
model constructions have a separate reviewer. Their consequences are
mentioned here where the report draws proof-theoretic conclusions.
The unfinished `Goodman_M5_Nested_Collision` candidate is not counted as
proved. No claim below relies on it.

## Verdict and priorities

The numbered object-language theorem transfers are substantially complete
in their expressly stated scopes. I found no new failure in their inspected
proof stock, binder orientation, or translated conclusion. This does not
license the unqualified sentence that every determinate statement in the
original notes has been proved in every intended model.

The main outstanding boundaries are:

1. **General-model T9/Attack 3:** the abstract counting/infinitude theorem is
   checked, and the new typed instantiation is checked for exact-carrier
   interpretations. The bridge from arbitrary appropriate native Henkin
   models to those abstract hypotheses is not supplied. This is a genuine
   remaining obligation if the goal includes the original notes' general
   model claim, rather than only the historical report's explicitly
   conditional theorem. See §5.
2. **M5's object-language repair:** the historical local collision pair is
   refuted. A semantically corrected pair is checked, but that alone is
   not a nonexplosive object-language proof over the minimal stock. The
   nested-input proof is still in progress at this baseline. See §6.
3. **Scope of TU/RS:** the explicit witness proof is checked with zeroary
   Exhaustion, PP, and ∃fun′. It does not settle the contradictory source
   prose in the weaker scope lacking Exhaustion. Its individual native
   transfer is also a small remaining packaging item. See §4.
4. **Finite PC and subsidiary algebra:** the original notes explicitly
   claim arbitrary finite PC instances are theorems. I found particular
   finite selectors and the necessary general purity machinery, but no
   separate arbitrary-finite, all-type native theorem. Several elementary
   classification/group facts similarly occur as checked source helpers
   rather than individually cataloged native statements. These are smaller
   coverage items, not reasons to discard the verified T6/T8 proofs.
5. **Final report corrections:** the old report's M5 wording, general-model
   qualifications and stale remaining-work sections require reconciliation.
   A newer milestone linked above an older claim matrix does not by itself
   make the old individual rows current.

T7b remains genuinely underspecified. No argument in this audit settles
Goodman's PP question, derives L2 or a classification principle from PP,
or constructs a model of the PP stock.

## 1. The exact calculus and the central packages

Original pp.1–2 distinguish Recombination from Exhaustion, explicitly define
necessity by identity with truth, and restrict the main problem to exactly
one fundamental proposition. The current development correctly separates:

- **H** and its typed lambda/propositional/quantifier rules;
- the core's full-F minimal classicist calculus;
- **C+[T]**, in which theorem-level PE and Generalization operate above
  the added axiom stock;
- a local temporary-assumption judgment, whose assumptions must be
  discharged before theorem-level rules are applied.

`Goodman_Book_Axiom_Extension` defines the native extension independently.
`Goodman_H_Proof_Preservation`, `Goodman_Classicist_Preservation`, and
`Goodman_CEV_Axiom_Preservation` supply whole-proof forward preservation.
The CEV+ induction covers Axiom, Base, vector Equivalence, MP, Gen and Inst.
Vector order and the language guards are explicit. Nothing inspected
silently replaces full F by R or assumes ordinary extensional HOL equality
as object-language identity.

The general CEV+ transfer requires **closed added source axioms**, a rich
named-variable stock, a distinct typed chart, and target-signature admission.
`Goodman_Restricted_Signature_Transfer` eliminates the old universal
signature restriction under its language guards; it does not eliminate the
closed-source-stock condition or establish reverse proof equivalence.
`Goodman_Extension_Retraction` proves native signature conservativity,
including open native axioms. These are different theorems with different
scope. The source of each nonderivability claim must therefore be stated:
a checked native countermodel is sufficient, whereas forward preservation
alone does not prove reverse consistency transfer in an arbitrary direction.

The source's claim that Recombination alone supplies ordinary QSS is not
what the repaired bridge proves. The checked weakest intermediate conclusion
is pointwise possible identity. `gi_repaired_native_QSS` adds zeroary
Exhaustion; `gi_native_exists_fun_prime_from_QSS` then uses unique
fundamentality to provide the ∃fun′ premise. The original T6 theorem stocks
instead assume ∃fun′ and need no QLN. The two routes must remain separate.

The statement that arity ≥2 QLN instances are vacuous with one fundamental
entity is a correct metatheoretic observation, explicitly qualified as such
in the old report. The native package represents zeroary and unary QLN;
there is no audited arbitrary-vector reduction theorem here. Do not call
that reduction itself an Isabelle theorem.

The old report correctly limits the derived Modalized Functionality theorem
to proposition-valued operators, with arbitrary argument type. A schema with
arbitrary result type must not be silently identified with that derived
theorem. Its exact-model validity and any additional axiomatization are
separate from derivability in the base calculus.

## 2. Numbered object-language claims

| Original claim | Current evidence | Required qualification |
|---|---|---|
| T1, p.3: pure propositions are truth or falsity; WI collapses to Inv | `gi_T1_pure_propositions_extreme`, `gi_T1_biconditional_classification`; fully native `gi_native_T1_WI_derives_Inv` | Logical purity/application plus zeroary Exhaustion. Not Recombination alone. |
| T2a: fun′ preserved by G and negation | `Goodman_T2a_Transfer`: reversible, group-member and negation endpoints, both translated and independent named variable instances | Group requires both pure Z and a pure two-sided inverse. Current transfer retains the PP core; no claim of a minimal stock. |
| T2b: truth/falsity not fun′; witness differs from truth, falsity and its negation | `gi_T2b_truth_not_fun_prime_translated`, `_falsity_not_fun_prime_translated`, `gi_T2b_nontriviality` | Minimal purity/application stock. The witness statements have an object-level fun′ antecedent, not a globally added fixed-witness axiom. |
| T2c: every pure proposition is possibly equal to a fun′ witness | `gi_T2c_parameter_translated`, `gi_T2c_quantified_translated`, `gi_T2c_attainment` | PP is unnecessary. Preserve Pure(p) and fun′(r) antecedents. |
| T2d: possible purity | `gi_T2d_possibly_pure` | Checked stronger than the displayed source route: no Persistence. Do not infer actual purity. |
| T2e: NC(r) is false but possible | `gi_T2e_false_but_possible` | Conditional on fun′(r); truth of NC(r) and identity of its denotation are not interchangeable. |
| T2f: six pairwise distinct propositions | `gi_T2f_six_distinct` and its explicit 15-inequality formula | Conditional on fun′(r); not a proof that the antecedent is consistent. |
| T3: ◇Fun(x)→fun′(x) | `gi_T3_modal_core`; repaired `gi_T3_heredity_with_exhaustion` and `_with_pure_rigidity` | The modal core reaches possible identity. Full heredity uses additional zeroary Exhaustion or pure-identity rigidity. The old two-world abstraction is not a full CEV+ countermodel. |
| T4: no higher-type fun′ value C(r) for pure C | `gi_T4_parameter_translated`, `gi_T4_no_higher_fun_prime` | Stronger checked statement: C and r need only be typed; Pure(C) remains an antecedent. No PP or fun′(r) needed. Higher-type fun′ uses predicates at the correct type. |
| T5: a third fun′ proposition | `gi_T5_proliferation`, `gi_T5_no_two` | PP core and local fun′(r) antecedent. No classification principle or fixed fun′ axiom is inserted. |
| T6: four refutations | `gi_native_T6_Inv_refutation`, `_TU_refutation`, `_WI_refutation`, `_RS_refutation`, plus four `gi_native_central_T6_*` counterparts and inconsistency corollaries | Fully native principles now exist. Weak routes retain ∃fun′+L2 plus classification; RS uses strong L2+RS and gets its witness from RS. Repaired-central variants require zeroary Exhaustion. |
| T7a: ¬a_id and some a_g | `gi_T7a_parameter`, `gi_T7a_closed`, `gi_T7a_repaired_central_stock` | Native conclusion, but L2 in its stock is explicitly translated. No classification premise. This is not a model/existence proof for the stock. |
| T7b: kind-level fixed/shifted diagonal | No unique source formula | Genuinely underspecified: term, binders, and fixed/shifted relations are absent. Do not invent a theorem and attribute it to Goodman. |
| T8a: five base kinds | All ten `gi_T8a_*` pair endpoints and combined theorem in `Goodman_T8_Transfer` | Fun′ antecedent retained. First three pairs use the PP core; seven constant-involving pairs have empty added stock. No L2. |
| T8b: uniqueness of represented kind | `gi_T8b_kind_uniqueness_translated` | Uses L2 and the two actual representation hypotheses. |
| T8c: 31 pure operators and 31 propositions | Growth endpoints in `Goodman_T8_Transfer`, audited in `t8-statements.txt` | Purity and pairwise distinctness are separate checked conclusions. This is not 31 kinds, let alone an indefinitely iterable growth theorem. |
| T9: cardinal dichotomy | Abstract `pp_T9_*` results and actual exact-carrier `gi_T9_native_formula_cardinal_dichotomy` | See §5: full external PC, native purity/core interpretation, L2 and ∃fun′ inputs; no general-Henkin instantiation yet. |

The source's T4 comment that higher-type fun′ entities “would have to be
independently fundamental” exceeds the proved negative definability theorem
unless “metaphysically definable” and “independently fundamental” are given
additional precise conditions. The report's narrower T4 formulation is the
one supported by its endpoint.

## 3. L2, strong L2 and negation orientation

There is **no L1** in the seven-page source. L2 and strong L2 are the two
versions on p.2. The current native formulas agree with their source:

    X ≈ Y  iff  ∃Z∈G. X = Y∘Z
    strong witness: X = Y∘Z and q = Zp.

`Goodman_Native_T6_Extras` defines these formulas without calling the
translator, then proves literal correspondences. Its chart lists protect
all surrounding free names. It also distinguishes the material
biconditional from Leibniz identity. Neither the weak conclusion nor its
stronger input equation was reversed in the inspected definitions.

The exact L2 counterexample now has the complete closed-logical denotational
stock bridge, not only a small list of operators. Raw-stock failure and
actual root failure of translated L2 are separate endpoints. It establishes
failure for that specified no-PP interpretation, not arbitrary enlarged
Pure stocks, all worlds simultaneously, or derivability from PP. The report
must keep its bounded unsuccessful Vampire searches as historical failures
to find proofs, not evidence of underivability.

For direct WI, the exported pointwise formula is exactly the advertised
family with local antecedent fun′(r)∧Pure(A). The family endpoint retains
fun′(r), and the closed theorem adds ∃fun′. The native stock has PP core,
L2, and WI, not Exhaustion. `Goodman_WI_Master_Transfer_Audit` additionally
checks proof dependencies against the designated refutation/ex-falso
endpoints. This is materially better evidence for “direct proof” than merely
deriving the formula in an inconsistent stock. The separately exported
master-family contradiction is not used as a replacement for that family
derivation.

## 4. Classification relations and finite PC

`gi_native_WI_derives_TU` works over the singleton WI axiom stock.
`gi_native_T1_WI_derives_Inv` and `gi_native_T1_TU_derives_Inv` require T1's
zeroary Exhaustion stock. The latter is a new direct proof, without PP,
L2, or ∃fun′. These are theorem-over-stock consequences, not automatically
local implication formulas.

The original source conflicts with itself: p.2 says TU⇒RS with witness
“true and fun′”; p.3 says RS and TU are incomparable. The checked explicit
witness `gi_CEV_TU_RS_exact_witness` and RS theorem
`gi_CEV_TU_RS_exact_stock` use

    logical purity + application closure + PP
    + zeroary Exhaustion + ∃fun′ + TU.

They are nonexplosive constructor-calculus proofs. Purity of the witness is
derived, not assumed, and no L2 or T6 refutation is used. They settle the
full-Exhaustion scope. They do not show TU⇒RS without Exhaustion or prove
either direction of an incomparability claim there. A native transfer of
this closed stock and its witness is feasible using the already-proved
whole-proof preservation; it is not separately present in the inspected
native catalog. This is a small explicit remaining transfer item.

The p.2 elementary assertions that pure biconditional operators are
self-inverse have checked source helper proofs, notably
`CEV_axiom_biconditional_self_inverse` and
`CEV_axiom_biconditional_group_member_from` in the frozen WI master theory.
Their use in transferred whole proofs is justified. General group/kind
algebra is also instantiated for actual exact root values in
`Goodman_T9_Root_Algebra`. This is not the same as separately exporting
every general native group axiom or the full all-type assertion in the
source's introductory “everything generalizes by type”.

Similarly, p.3 asserts finite PC for arbitrary finite pure collections.
The T8 proof supplies the particular finite selector constructions it uses;
logical constant-abstraction and application closure supply the expected
method for arbitrary finite collections. I did not locate a standalone
all-type, arbitrary-finite native PC theorem. If “every determinate claim”
includes this introductory assertion, it should receive a short explicit
induction, with the empty collection represented by constant falsity and
nonempty collections by finite disjunctions of identity predicates.

## 5. T9 and Attack 3: the essential generality boundary

The old report's formal T9 and infinitude statements were deliberately
conditional: a PC subset-selector injection, representation, orbit-fibre
coding, and the relevant L2/composition conditions were premises. In its
T9 row it expressly said that discharging these from the full object theory
remained separate. Those abstract theorems are checked, not outstanding.

The new work supplies a substantive instantiation, not just their re-export.
In `gi_T9_native_purity`, Pure is the actual interpretation of the native
constant at the root of **Bacon's exact carriers**, with global validity of
the native PP core. `gi_T9_full_unary_PC` ranges over **every external HOL
subset** of root-pure unary values, with a pure classifier of type
(t→t)→t. The lowering construction, pure composition, group inverses,
actual kinds, selected-set covariance and fibre coding are proved.
Actual native translated L2 and ∃fun′ root hypotheses supply the remaining
semantic inputs. Exports verify

    |Pow(K)| ≤ |Pure_(t→t)| ≤ |K × G|,
    K infinite,
    |Pow(K)| ≤ |G|.

This closes the exact-carrier instantiation. It does **not** prove that every
arbitrary Henkin model of a finitary second-order PC formula contains
classifiers for all external subsets. Nor is full external PC an axiom
already present in Goodman's central PP theory.

The original notes' p.4 prose speaks about a model of the theory+PP+L2+PC
without restricting it to this exact family. To verify that statement in
full generality requires an additional bridge. A suitable route is to
interpret the abstract counting and infinitude interfaces over the
Leibniz-equivalence quotient of an arbitrary appropriate full minimal model:

1. Define pure values, pure invertibles, and kinds on the quotient, or prove
   that their definitions are independent of representatives.
2. Derive typed constant-abstraction/pure-composition and the actual
   type-lowered PC selector from that model's native purity axioms.
3. Formulate full external PC over the quotient, rather than arbitrary
   nonsaturated subsets of raw values, and derive the subset injection.
4. Prove representation and the group action, then instantiate the already
   checked abstract fibre-counting and cardinality-preservation results.
5. Keep the native C+[T] soundness/per-world adapter explicit wherever it
   supplies purity theorems; minimal H-model fields alone do not give it.

The general native M1 bridge now discharges many relevant compositional and
Leibniz-congruence facts, but does not itself build this selector/group
quotient. Thus the old **conditional report claim** is fulfilled; the
original **unrestricted model-class connection** remains a real gap if it
is included in the comprehensive goal. It must not be erased merely by
rewording T9 as an exact-model theorem.

The actual T9 cardinal-ceiling corollaries are checked: kind-sized G,
kind-bounded injective descriptions, or countable G contradict the
PC/L2 bound. None derives such a ceiling for arbitrary pure stocks.

## 6. M5: consequences for object-language claims

This source issue cannot be left to a mere model-scope footnote. The
original p.6 displayed pair NC(r),⊤ was asserted to collide under fun′(r).
The historical constructor proof instead assumed `pp_fun_prime r ∈ T`
and used zeroary Equivalence above T. Its transferred theorem retains that
actual premise. The new fixed-fun′ collapse theorem shows the minimal stock
is already inconsistent when a fixed fun′(r) is a theorem, without PP.

The checked exact countermodel now refutes the stronger local implication
for that pair, and its native translation is underivable from the no-PP
QLN background and the smaller T2-min stock. Hence the historical report's
“whenever fun′” proof description is false as written and must be corrected.
This counterexample is not a PP countermodel and does not refute every
alternative noninjectivity argument for the same operator.

The corrected semantic collision at punctured truth and truth is checked.
The general inverse-witness/reversible injectivity implications are native
theorems over the empty added stock, with appropriate typing/signature
guards. The actual rebuilt nonuniform involution supplies the opposing
example to an unrestricted existentially-given-invertible collision method.
It does not rule out a stronger argument exploiting an additional
PP-specific hypothesis.

At this baseline the proposed **object-language** repair using NC(□r) is
unfinished. Do not merge the checked semantic repair and that candidate
into a single claimed derivation. The remaining task is to check the
nonexplosive local/theorem statement over its stated stock, or leave the
source claim refuted with the semantic repair clearly labeled.

## 7. J/S control, granularity and finite proof support

The J/S results in the historical report match the inspected native exports.
Purity of J and S and the conditional nonuniformity of S use the PP core.
The range/iteration theory additionally requires zeroary Exhaustion:

    S³=S; (S²)²=S²; E→S²=id;
    ∃fun′→(E↔S²=id);
    ∃fun′→(¬E→S²=¬∘S).

`gi_control_cube`, `_square_idempotent`, `_range_implies_identity`,
`_range_iff_identity`, and `_no_range_negative_square` are native
derivations with explicitly translated operator conclusions. Heredity and
reflection are transferred too. The equality is at unary-operator type,
not local agreement of truth values. The inspected stock and theorem
statements do not assume E, ¬E, reversibility of S, QSS or Pure(Fun).
The report's proof correctly uses separation in its negative-range step
rather than applying PE under a temporary assumption.

`gi_granularity_iff_truth_uniform` improves the old full-stock corollary:
logical purity/application and the two unary QLN directions suffice.
Pure(Z)∧Fun(r) is discharged as a local antecedent. PP, Persistence,
zeroary Exhaustion and reversibility are not needed for this equivalence.
The agreement/disagreement builders have derived purity. Abstract
truth-fibre theorems separately retain surjectivity and a true and false
value. This verifies the reduction, not TU from PP; indeed the displayed
noncontingency condition is equivalent to the desired TU instance.

`goodman_book_finite_support` is an induction on the actual native C+[T]
derivation, including PE and Generalization. Its finite-consistency and
finite-refutation corollaries preserve those rules. They need no global
closedness assumption on native T and do not invoke a model-existence or
completeness theorem. Thus the historical finite-core claim is verified
as **proof-theoretic compactness**. Calling it a semantic compactness
construction, fair automated proof search, or a consistency proof would
add something not established by these endpoints.

## 8. General M1 and final report language

The new `gi_M1_book_model.gi_book_native_fn59_contradiction` is an actual
arbitrary-carrier native-book interpretation theorem. The liar, QSS and
unique-fundamentality evaluations are proved from the independent full
minimal model interface; proposition truth agreement and application
congruence are derived, not axiomatized as shortcuts. It strictly improves
the old disconnected compositional-Henkin locale.

Its last corollary retains truth preservation of native C+[T] over the
specific purity stock. That is appropriate for a **sound CEV+ model**, not
automatic for every H model. Consequently the old report may continue to
state the qualified compositional obstruction, but “the remaining extra
premise is not semantic” should be revised: removing Pure(Fun) is the
mathematical open premise once a suitable CEV+ sound model interface has
been supplied; an arbitrary new model class still needs that adapter.

Finally, the report should not summarize these results as a completed
proof of the original unqualified T3, arbitrary-Henkin T9, or local M5 pair.
It should distinguish proved theorems, explicit corrections/refutations,
verified conditional reductions, precise missing bridges, and genuinely
underspecified claims. The original question and its open attack premises
are not failures of the present audit; they remain open research questions.
