# Contributing to the Goodman formalization

This application is an ordinary folder in the Bacon–Dorr repository and
shares its visibility and access permissions. Ask Branden for collaborator
access with your GitHub username when needed. Contributions may be mathematical, formal, or
expository; a small result with a precise statement is a useful contribution.

Start with [STATUS.md](STATUS.md), the
[source correspondence guide](docs/SOURCE_CORRESPONDENCE.md), and the
[worked M5 proof](docs/READING_GUIDE.md#one-checked-proof-the-repaired-m5-collision).
Propose an issue identifying the source page or result, the exact proposed
statement, and the files affected. Agree the scope before undertaking a
large proof or changing an existing model interface.

Goodman's PP question remains open. The completed 20 September M5 repair
is not an unfinished task: its 21 audited endpoints establish the corrected
local collision and nonreversibility implications. The integration baseline
contained 1,574 cataloged objects in 82 catalogs, with nine historical replay
endpoints counted separately; the accepted task-1, task-2 and task-3 catalogs add 17,
42 and 26 entries, the accepted task-4 catalog adds 21, and the accepted task-5
submission below adds 28 (1,708 objects in 87 catalogs). Counts measure selected evidence, not the number of source
claims proved. The two supplied enumeration and frame-completeness snapshots
are selected and checked following completion of task 4.

## Bounded first contributions

These items come from the remaining source obligations, not from an
assumption that every plausible strengthening is true. Each contribution
needs a source locator, an exact theorem statement or documented obstruction,
and a check appropriate to its scope.

### 1. Transfer the explicit TU–RS witness

Read Goodman's notes, pp.2–3, and
[Goodman_TU_RS_Witness.thy](theories/individual/Goodman_TU_RS_Witness.thy),
especially `gi_CEV_TU_RS_exact_witness` and `gi_CEV_TU_RS_exact_stock`.
The constructor-calculus proof already exists. Its stock contains logical
purity, application closure, PP, zeroary Exhaustion, ∃fun′, and TU.
It does not use L2 or a T6 contradiction.

The bounded task is to transfer this stock and its explicit pure witness to
the named calculus and connect the conclusion to `gb_RS` in
[Goodman_Native_T6_Extras.thy](theories/native_extras/Goodman_Native_T6_Extras.thy).
Completion means named witness-purity and RS endpoints, a stated stock
correspondence, and audit entries. Retain Exhaustion. The source says both
TU implies RS and TU/RS are incomparable in different passages; this
transfer does not settle the weaker scope without Exhaustion.

**Status (20 September 2026): completed and accepted after Codex's independent
proof review and checker/export run.** Two prose corrections retain the
unresolved source discrepancy and distinguish derivability from consistency;
no theorem or axiom package was changed.
[Goodman_Native_TU_RS_Witness.thy](theories/native_extras/Goodman_Native_TU_RS_Witness.thy)
defines `gb_TU_RS_axioms G = gb_T6_core G ∪ {gb_zeroary_exhaustion G, gb_exists_fun_prime G, gb_TU G}`
and the named witness `gb_RS_plus G`, and proves `gi_native_TU_RS_derives_RS`
(`gb_RS G`), `gi_native_TU_RS_witness_pure` (`gb_pure gb_unary (gb_RS_plus G)`) and
`gi_native_TU_RS_witness_specification` (`gb_rigid_specification_on_chart G [] (gb_RS_plus G)`),
each under `sg_rich G` in `gb_signature` with no translation parameter. The
stock correspondence is `gi_TU_RS_literal_stock_inclusion` (literal for the
PP core, ∃fun′ and TU) together with `gi_TU_RS_axiom_from_native` (zeroary
Exhaustion by the existing provable equivalence). The uniform witness
specification uses α-transport of the translated formula. The catalog is
`native-tu-rs-witness-audit.txt` (17 entries). No weaker-scope theorem is
claimed and no existing result or stock was changed.

### 2. State and prove arbitrary finite PC at every type

The notes, p.3, assert finite instances of pure comprehension. Begin with
the particular finite constructions in
[Goodman_T8_Transfer.thy](theories/t8/Goodman_T8_Transfer.thy), including
`gi_T8c_operator_purity`, and the native logical-purity/application schemas in
[Goodman_Book_Axiom_Packages.thy](theories/axiom_extension/Goodman_Book_Axiom_Packages.thy).
Those ingredients do not already constitute an arbitrary-finite, all-type
native theorem.

Choose a finite list of pure terms of one type σ. Define its predicate by
finite disjunctions of Leibniz identities, with constant falsity for the
empty list. Prove the predicate pure and prove its membership formula,
retaining the typing and freshness conditions. Completion means an explicit
finite-list induction, an empty-case theorem, the general typed endpoint,
and an audit entry. This is finite PC, not classification of every external
subset of a pure stock.

**Status (20 September 2026): completed and accepted after Codex's independent
proof review and checker/export run.** Two prose corrections distinguish
finite comprehension from arbitrary external PC and record the existing
relative-consistency consequence for this weaker stock. No proof or axiom
package was changed.
[Goodman_Native_Finite_PC.thy](theories/native_extras/Goodman_Native_Finite_PC.thy)
represents the n parameters as context variables of type σ, defines the selector
λx.(x = aₙ ∨ … ∨ x = a₁ ∨ ¬⊤₀) (n = 0: λx.¬⊤₀), and proves by explicit induction
on n (`gi_PC_selector_pure_from`, via the fixed closed logical builder
λa.λQ.λx.(x = a ∨ Q x), two application-closure steps and three β-steps) the
closed constructor sentence `gi_CEV_finite_PC`. The native endpoint
`gi_native_finite_PC` is `sg_rich G ⟹ goodman_book_proves gb_signature G (gb_finite_PC_axioms G) (gb_finite_PC G σ n)`
with `gb_finite_PC_axioms G = gb_purity_schema G ∪ gb_application_schema G`,
plus the n = 0 instance and `gi_native_empty_selector_pure`. The native family is
written on an explicit chart and agrees literally with the translation
(`gi_finite_PC_native_translation`). Freshness is carried by `named_chart_fresh`
on the chart; typing is the explicit `lookup Γ i = Some σ` parameter condition.
Catalog `native-finite-pc-audit.txt` (42 entries). The membership clause is a
material biconditional, not proposition identity.

### 3. Export one native subsidiary algebra lemma

For the notes' p.2 biconditional operators, begin with
`CEV_axiom_biconditional_self_inverse` and
`CEV_axiom_biconditional_group_member_from` in
[Bacon_PP_Goodman_T6_WI_Master.thy](theories/preserved-additions/wi-master/Bacon_PP_Goodman_T6_WI_Master.thy).
They are existing source helpers used by transferred proofs. Native builders
already occur in
[Goodman_Native_T6_Extras.thy](theories/native_extras/Goodman_Native_T6_Extras.thy).

Choose one result, such as self-inverseness of the operator p ↦ (p ↔ a)
under its stated assumptions. Supply the named statement and its source
correspondence, with purity of a and the exact axiom stock explicit where
needed. Completion means a separately audited native theorem, not merely
another use of the old helper in a larger transferred proof. For group or
kind algebra, first compare the existing exact-root results in
[Goodman_T9_Root_Algebra.thy](theories/t9/Goodman_T9_Root_Algebra.thy);
do not present an already proved exact-root lemma as missing.

**Status (20 September 2026): completed and accepted after Codex's independent
proof review and checker/export run.** The companion purity/group results
are proved here over a package containing PP; necessity of PP is not
established. The general composition law remains a separate possible
contribution, not a gap in this chosen task.
[Goodman_Native_Biconditional_Algebra.thy](theories/wi_master/Goodman_Native_Biconditional_Algebra.thy)
packages, for B_a = λp.(p ↔ a), the closed sentences `gi_bic_self_inverse`
(∀a.((B_a ∘ B_a) = id)), `gi_bic_operator_pure` (∀a.(Pure(a) → Pure(B_a))) and
`gi_bic_group_member` (∀a.(Pure(a) → B_a ∈ G)) from the preserved helpers, and
transfers them: `gi_native_bic_self_inverse` holds over every added stock `U`
(it is a C⁺ theorem, `gi_native_bic_self_inverse_empty_stock` for `U = {}`);
`gi_native_bic_operator_pure` and `gi_native_bic_group_member` hold over
`gb_T6_core G` (logical purity, application closure, PP at t→t). The
group-membership sentence is the uniform native formula reached by
α-transport of the literal translation (`gi_bic_group_member_alpha`). The
exact-root T9 algebra is semantic and untouched. Catalog
`native-biconditional-algebra-audit.txt` (26 entries).

### 4. Integrate the frozen enumeration and frame-representation results

The two formerly unselected snapshots are now selected and checked:

- [Bacon_PP_ZF_Exact_Enumeration.thy](theories/preserved-additions/exact-enumeration/Bacon_PP_ZF_Exact_Enumeration.thy):
  `pp_e_consistent_sentence_enum_range` and
  `pp_e_enumerated_sentence_true_at_branch`.
- [Bacon_PP_ZF_Exact_Completeness.thy](theories/preserved-additions/exact-completeness/Bacon_PP_ZF_Exact_Completeness.thy):
  `pp_e_Bacon_consistency_representation` and `pp_e_Bacon_exact_completeness`.

These are old exact-carrier results, not conjectures. The completed task
established their import closure without altering their preserved proof
bodies, then transferred the sentence-level representation and companion
necessity results through the named denotation correspondence. Both have
selected builds, audited native endpoints, and updated coverage/provenance.
The fixed string alphabet and t-generated fragment remain explicit.
Here consistency means satisfiability under some typed interpretation on
the fixed frame, and the common theory ranges over interpretations on that
frame. It does not mean syntactic H consistency or H completeness.

**Status (20 September 2026): completed and accepted after Codex's independent
review of both representation and companion necessity, and a checker/export
run.** The result characterizes frame satisfiability/validity; it is not an
effective decision procedure. Both snapshots are selected under their recorded replay session
names `Goodman_Exact_Enumeration` (parent `Goodman_Exact_Legacy_07`) and
`Goodman_Exact_Frame_Completeness`, bodies unchanged (hashes in
`verification/provenance/frozen.json`; `extraction.json` now records them as
selected later). [Goodman_Exact_Frame_Representation.thy](theories/exact_frame/Goodman_Exact_Frame_Representation.thy)
(session `Goodman_Integration_Exact_Frame`) defines the named signature
predicate `gi_exact_named_in_signature` with its decode lemma, the named
sentence predicate `gi_exact_named_sentence S G M` (language, closedness,
t-generated fragment, constants in S) and frame satisfiability
`gi_exact_named_frame_satisfiable G g M` (truth at the root of some typed
interpretation on the frame), and transfers `pp_e_Bacon_consistency_representation`
through `gi_exact_decode`: `gi_exact_named_frame_representation_branch`
(satisfiable ⟷ true at some substitution of `pp_e_complete_constants S`),
`gi_exact_named_frame_representation_diamond` (⟷ native ¬□¬M true at the
root, under `sg_rich G` and a typed assignment), and
`gi_exact_named_frame_satisfiable_at_branch`. The companion necessity
theorem is also transferred: `gi_exact_named_frame_valid G g M` (truth at the
root of every typed interpretation on the frame) equals membership of the
decoding in the frame theory, truth at every substitution of the complete
model (`gi_exact_named_frame_completeness_branch`), and the native □M at
the root (`gi_exact_named_frame_completeness_box`); validity is
unsatisfiability of the negation (`…_valid_iff_negation_unsatisfiable`).
Catalog `exact-frame-representation-audit.txt` (21 entries, including the
five principal snapshot theorems now in the selected closure). No syntactic
H consistency or H completeness claim is made.

## Larger mathematical and source-scope obligations

### 5. Make exact Theorem 10.1 parametric in constant names

Start with Bacon's Logical Combinatorialism, appendix Theorem 10.1, and
`gi_exact_Bacon_10_1_named` in
[Goodman_Exact_10_1_Transfer.thy](theories/exact_qln/Goodman_Exact_10_1_Transfer.thy).
The checked theorem handles string names, every closed named term in its
t-generated fragment, and a countable family of interpretations. It does
not handle an arbitrary cardinality of constant names.

A bounded first deliverable is an evaluator/action correspondence lemma
for a polymorphic name type, retaining the alphabet-independent branch
gluing construction in
[Bacon_PP_ZF_Exact_10_1.thy](theories/preserved-additions/exact-first/stage06/Bacon_PP_ZF_Exact_10_1.thy).
The full item is complete only with a parametric gluing theorem and audited
named-term endpoint, without an injection of all names into strings. Keep
the t-generated restriction and countable branch family. An open-term
extension also needs the related-environment hypothesis; finite support of
one term does not prove countability of the declared signature.

**Status (20 September 2026): completed and accepted after Codex's independent
proof review and checker/export run.** The accepted scope is the closed-term
arbitrary-name gluing theorem, not open-term transport or arbitrary-name
sentence-enumeration completeness.
[Goodman_Exact_10_1_Parametric.thy](theories/exact_qln/Goodman_Exact_10_1_Parametric.thy)
defines the polymorphic evaluator `gi_exact_poly_denote C G g M` for named
terms over any name type 'c by coding the finitely many constants of M
injectively into strings (`gi_exact_name_code M`, per term) and evaluating
the renamed term with the correspondingly renamed interpretation; it
coincides with `gi_exact_named_denote` at 'c = string
(`gi_exact_poly_denote_string`). The gluing `gi_exact_poly_glued A c σ` is
literally the pointwise branch gluing of the preserved construction. The
endpoints `gi_exact_Bacon_10_1_parametric_action`,
`gi_exact_Bacon_10_1_parametric_truth_branch` and the packaging theorem
`gi_exact_Bacon_10_1_parametric` state, for every 'c, every nat-indexed family
typed at t-generated types, and every closed named term of the polymorphic
t-generated fragment `gi_exact_poly_propositional_term`, that the glued
interpretation realizes the family on the branches. No injection of all
names into strings is used and no countability of the signature is asserted;
the open-term/related-environment extension is not included. Catalog
`exact-10-1-parametric-audit.txt` (28 entries).

### 6. Resolve the unconditional next-type M1 nonmembership claim

**Open contributor project.** Branden has left tasks 6–9 for contributors;
the report does not represent them as completed or as active automated tasks.

Goodman's M1 claim is stronger than the current criterion in
[Goodman_Exact_QLN_Model.thy](theories/exact_qln/Goodman_Exact_QLN_Model.thy):
`gi_exact_generic_native_PP_global_iff` equates PP validity in the specified
generic interpretation with membership of the actual purity classifier in
the next native logical stock. Neither membership nor nonmembership is
thereby established.

The bounded first deliverable is a precise nonmembership statement for
that classifier and that complete stock, with a proposed invariant or
separation lemma. Closing the source claim requires a checked proof in
its intended scope, or a checked counterexample and explicit correction.
Do not count an iff, a conditional obstruction, or an unsuccessful search
as completion. The general footnote-59 endpoint
`gi_book_fn59_from_native_extension_soundness` in
[Goodman_General_M1_Native_Semantics.thy](theories/general_m1/Goodman_General_M1_Native_Semantics.thy)
is already proved with its purity and soundness conditions; deleting those
conditions is not an expository simplification.

### 7. Extend T9 beyond the exact-carrier interpretation

Read the notes' T9/Attack 3 and the existing
`gi_T9_native_formula_counting_chain` and
`gi_T9_native_formula_cardinal_dichotomy` in
[Goodman_T9_Native_Conclusion.thy](theories/t9/Goodman_T9_Native_Conclusion.thy),
with [Goodman_T9_Infinitude.thy](theories/t9/Goodman_T9_Infinitude.thy).
The abstract argument and its exact-carrier instantiation are completed.
The remaining source-general task concerns arbitrary appropriate native
models, not another proof of those endpoints.

Start by proving one representative-independence lemma for pure values,
invertibles, or kinds on a model's Leibniz-equivalence quotient. The larger
deliverable must supply the quotient group/action, the correctly typed
lowered PC selector, representation, and fibre coding, then instantiate
the existing counting/infinitude argument. Completion requires explicit
model and C+[T] soundness assumptions and full external PC on the quotient.
An internal or definable-subset comprehension scheme is not silently
full external PC. No part of this task establishes PC or L2 from PP.

### 8. Identify the particular glued proposition, if that is the intended r

The generic-seed M7 instance is complete: see
`gi_exact_M7_generic_invariant_unreachable` and
`gi_exact_M7_fun_prime_orbit_collision` in
[Goodman_Exact_M7_Transfer.thy](theories/m_claims/Goodman_Exact_M7_Transfer.thy).
The remaining choice-sensitive question is whether a specified coordinate
of `pp_e_complete_constants` is the intended free/fun′ proposition.

First state that coordinate and the chosen gluing components precisely.
Completion for that choice means proving its typing and fun′ property
(or the required identification), then applying the existing M7 theorem.
Do not identify an arbitrary Theorem 10.1 interpretation with the generic
seed, or conclude that every typed r has a noninjective orbit.

### 9. Clarify T7b and the multiple-fundamental M4 proposal

Compare the source passages with `gi_T7a_closed` in
[Goodman_T7_Transfer.thy](theories/numbered/Goodman_T7_Transfer.thy) and the
completed single-fundamental repair in
[Goodman_Exact_M4_Repair.thy](theories/m_claims/Goodman_Exact_M4_Repair.thy).
T7a and repaired M4 are not open merely because the source also sketches
larger proposals.

The bounded deliverable is a source clarification: for T7b, specify the
term, binders, and fixed/shifted kind relations; for the wider M4 proposal,
specify the multiple-fundamental stock and its intended semantic claim.
Completion of this clarification means an agreed precise statement with
all choices labeled. It is not a theorem, and a contributor's new formula
must not be attributed to Goodman without that distinction.

### 10. Finish the claim-by-claim source audit and corrected report

**Agreed reporting checkpoint completed, 20 September 2026.** Read the
[new report](reports/GOODMAN_VERIFICATION_REPORT_2026-09-20.pdf) and
[reconciliation ledger](docs/RECONCILIATION_2026-09-20.md). They incorporate
the independently accepted tasks 1–5 and leave tasks 6–9 explicit and open,
as Branden directed. This is not a claim that every source obligation or
an exhaustive file-by-file fidelity audit is complete. The original broader
completion criterion below remains a standard for later contributor work,
not something achieved merely by publishing qualifications.

Use [SOURCE_CORRESPONDENCE.md](docs/SOURCE_CORRESPONDENCE.md) as the current
index, alongside the historical
[object-language audit](docs/FINAL_OBJECT_CLAIM_AUDIT.md) and
[model audit](docs/FINAL_MODEL_CLAIM_AUDIT.md). Those audits retain their
dated baselines; their M5 follow-ups supersede the older open-repair rows.

Choose one numbered source claim and compare the original notes, the
historical report identified in the source guide, its definitions, the
actual endpoint, and its exported premises. Record proved content,
corrections, conditional content, missing bridges, and underspecification
separately. Completion of the whole item requires a reconciled ledger and
a corrected report covering every promised source claim, with no stale
M5, arbitrary-signature, M1, or general-model T9 assertions. A passing
build is necessary for formal repairs but does not establish source fidelity.
Source PDFs and the historical report are reference inputs, not permission
to redistribute private research material.

## Verification and working rules

1. Use Isabelle2025-2 and the enclosing Bacon–Dorr core with its pinned source hashes.
   Follow [the verification guide](docs/VERIFICATION.md); do not silently
   refresh a dependency pin to make a check pass.
2. Keep builds, exports, and native dependency extraction serial. The
   per-session limit is 60 seconds. Run the repository's complete checker
   before submitting a formal change; retain failed logs as well as successes.
3. No admitted steps, new axioms, or oracle-based proofs. Preserve explicit
   typing, freshness, signature, carrier, and locale assumptions.
4. Add each new theory to ROOT or the selected import closure and add its
   substantive endpoints to an audit catalog. A file existing on disk is
   not evidence that the build checked it.
5. Keep preserved proof bodies unchanged. Place repairs or stronger results
   in new integration theories and retain the provenance mapping.
6. Explain whether a claim is a theorem, a local implication, a root-truth
   fact, global validity, or a conditional model result. Keep the full F
   language distinct from R and HOL–ZF distinct from the ZF object logic.
7. Use the authors' notation in prose, including □, ◇, fun′, and ≠. A
   translated endpoint must be labeled as translated; identical meaning is
   not necessarily identical represented syntax.
8. Include source correspondence, verification results, and audit coverage
   in the pull request. Credit collaborators and disclose substantive
   automated assistance. Private model-search material and stream journals
   are not contribution artifacts.

The open items above are an invitation to agreed, bounded contributions,
not instructions to resume all paused research or to claim the full PP
problem has been solved.
