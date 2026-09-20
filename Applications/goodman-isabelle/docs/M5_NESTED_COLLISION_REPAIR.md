# M5: the repaired object-language collision

Standalone copy: theory links below follow the new layout. Historical
build names/timings identify the integration checkpoint; the new repository's
own verification record is in [verification/README.md](../verification/README.md).

20 September 2026. This completes the nested-input collision repair only.
The remaining Goodman integration and model-search work stays paused.

## Statement and correction

Put NC(p) = □p ∨ □¬p and F(p) = (p ↔ NC(p)), where p has proposition
type and F has type t→t. Keep the operator F from the M5 discussion, but
replace the proposed first input NC(r) by

    q = NC(□r) = □□r ∨ □¬□r.

In CEV+ with logical-purity and application-closure schemas, we prove

    fun′(r) → (q ≠ ⊤ ∧ Fq = F⊤),
    fun′(r) → ¬Reversible(F).

These are genuine object-language implications. The assumption fun′(r)
is local and discharged; it is not added to the global axiom stock.
The output identity Fq = F⊤ is proved separately in CEV+ with **no added
axioms**. The stock used for the input inequality is exactly
`pp_T2_min_axioms = pp_purity_schema ∪ pp_application_closure_schema`.
No PP, Purity of Fun, QLN, Recombination, Exhaustion, or existence axiom
is added to prove these conditional statements.

The old input pair NC(r), ⊤ is not rehabilitated. Its claimed local
collision has a checked exact-model counterexample. The old proof with
a fixed fun′(r) axiom is also retained as historical evidence, but that
axiom stock is already inconsistent. Neither is used to prove this repair.

## Proof in source notation

**Proof.** Fix a proposition r and abbreviate NC(□r) by q.

1. S4 proves q → □q. Each disjunct of q is already boxed; axiom 4
   and normality therefore make each disjunct imply □q.
2. S4 also proves ¬□¬q. Indeed, axiom 4 gives □r → □□r, hence
   ¬q → ¬□r. Normality gives □¬q → □¬□r. The latter consequent
   is a disjunct of q, whereas axiom T gives □¬q → ¬q. Thus □¬q
   implies both q and ¬q.
3. By T, □q → q. Together with steps 1–2 this yields
   q ↔ (□q ∨ □¬q), that is, q ↔ NC(q). Consequently Fq is a
   theorem. The proposition F⊤ is also a theorem, because □⊤ is.
   Their material equivalence is therefore a theorem, and theorem-level
   zeroary Equivalence gives the identity Fq = F⊤. No temporary
   hypothesis has been introduced at this stage.
4. Now assume fun′(r) locally. Nontriviality gives r ≠ ⊤, or ¬□r.
   Attainment at the pure proposition ⊤ gives ◇(r = ⊤), or ◇□r.
   Thus □□r is false by T, and □¬□r is false by the definition of
   possibility. Hence ¬q, and T gives ¬□q. Since □q abbreviates
   q = ⊤, the inputs are unequal.
5. Combine the input inequality with the already established output
   identity and discharge fun′(r). Reversibility implies injectivity,
   so the same collision gives the second implication. ▪

In particular, step 4 never necessitates a conclusion drawn under fun′(r)
and never applies Equivalence under it. The temporary-assumption calculus
has only Assumption, Theorem and MP constructors.

## Isabelle endpoints and native transfer

Implementation: [Goodman_M5_Nested_Collision.thy](../theories/m5_object/Goodman_M5_Nested_Collision.thy).

| Endpoint | Exact role |
|---|---|
| `gi_M5_nested_stable` | q → □q |
| `gi_M5_nested_dense` | ¬□¬q |
| `gi_M5_nested_NC_equivalent` | q ↔ NC(q) |
| `gi_M5_nested_outputs_equal` | Fq = F⊤ over the empty added stock |
| `gi_M5_nested_local_collision` | Discharged fun′-conditional collision |
| `gi_M5_nested_local_nonreversibility` | Discharged fun′-conditional nonreversibility |
| `gi_M5_nested_native_collision_translated` | Collision implication in the new named calculus |
| `gi_M5_nested_native_nonreversibility_translated` | Nonreversibility implication in the new named calculus |

The native endpoints use `gb_T2_min_axioms G` and retain rich-variable-stock,
name-map, typed-chart, distinctness and conclusion-admission premises.
Their conclusions are translated formulas, not independently defined
unguarded native formulas. The equality in the collision is proposition
identity, not just agreement in truth value at the actual world.

## Verification and independent review

The 21-endpoint audit checks oracle dependencies, residual kernel
hypotheses and unresolved unification pairs. Explicit theorem premises
remain visible in the exported statements. A new proof-node traversal
also rejects dependence on the old axiom-stock collision and fixed-fun′
collapse endpoints; importing their theory is not treated as using them.

An independent read-only agent reviewed the proof and its import/definition
scopes on 20 September. It found no flaw or missing mathematical endpoint
for this conditional repair. It specifically checked the empty-stock
identity, MP-only temporary reasoning, and native admission guards.
That review is source-level evidence, not a substitute for the build.

The serial build `verification/build-2026-09-20T07-01-14-790980.log`
passed (exit 0, 48 seconds total; M5 object session 6 seconds). The audit
traversed **45,189 proof nodes** without reaching a prohibited endpoint.
The [verification record](../verification/README.md)
contained 1,574 integration endpoints in 82 catalogs at that checkpoint,
including these 21 (the later task-1, task-2 and task-3 catalogs are separate).
The nine separately counted historical replay endpoints remain separate.
All 82 preserved proof bodies and upstream theory/ROOT hashes still match.
The older semantic collision at punctured truth remains a separate result
in [Goodman_M5_Collision_Repair.thy](../theories/m5/Goodman_M5_Collision_Repair.thy).

## What this completes

The M5 noninjectivity/nonreversibility argument now has a corrected input
that supports an actual conditional object-language derivation, in addition
to the previously checked semantic calculation. This closes the nested-input
obligation identified by the final-readiness audits.

It does not construct a model of PP, prove PP inconsistent, or establish
the remaining unrelated report claims. Both upstream repositories and
their reports remain untouched; the final corrected report is still pending.
