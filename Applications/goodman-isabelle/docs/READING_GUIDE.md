# Reading the Goodman formalization

Start with a source claim, not the file order. The
[source correspondence guide](SOURCE_CORRESPONDENCE.md) records the current
scope; [STATUS.md](../STATUS.md) separates checked results from remaining
work. The [notation guide](NOTATION.md) translates the principal constructors.
No familiarity with the historical development is assumed here.

## Three levels to keep apart

The repository contains an older constructor presentation, the independent
named language of Bacon's book, and bridges between them. The source files
under `theories/preserved/` and `theories/preserved-additions/` retain the old
proof bodies. The remaining directories contain the integration. The
Bacon–Dorr core is the enclosing repository's independently checked core,
not a second copy inside this application. Its exact source hashes remain
pinned while application and documentation commits may change repository HEAD.

At each level, distinguish a formula from a proof assertion and from a
semantic claim about its interpretation. In particular, proving a theorem
conditional on fun′(r) does not construct a proposition satisfying fun′.
Nor does adding fun′(r) to a global axiom stock model a temporary assumption
that happens to hold at one world.

## One checked proof: the repaired M5 collision

Open [Goodman_M5_Nested_Collision.thy](../theories/m5_object/Goodman_M5_Nested_Collision.thy).
This is completed work, not a proposed proof. Goodman's notes, pp.5–6,
consider the proposition operator

    NC(p) = □p ∨ □¬p,          F(p) = (p ↔ NC(p)).

Here p and r have proposition type t, and F has type t→t. The repaired
first input is q = NC(□r), literally □□r ∨ □¬□r. The other input is ⊤.
We retain F but replace the source's unsuccessful input NC(r).

The principal theorem `gi_M5_nested_local_collision` proves

    fun′(r) → (q ≠ ⊤ ∧ Fq = F⊤).

Its added stock need contain only logical purity and application closure.
The companion `gi_M5_nested_local_nonreversibility` proves
fun′(r) → ¬Reversible(F). Neither conditional adds PP, Purity of Fun, QLN,
Exhaustion, or an existence axiom.

Proof. We first work with no added axioms and no temporary fun′ assumption.
Since each disjunct of q is boxed, S4's axiom 4 and normality give q → □q.
Also, ¬q implies ¬□r: if □r held, axiom 4 would give the first disjunct □□r
of q. Normality therefore gives □¬q → □¬□r. Its consequent is a disjunct
of q, while axiom T gives □¬q → ¬q. Thus ¬□¬q is a theorem.

Together with □q → q, these facts establish q ↔ NC(q). Hence Fq is a
theorem. The proposition F⊤ is also a theorem, since □⊤ holds. Their
material equivalence is therefore a theorem, and theorem-level zeroary
Equivalence yields the proposition identity Fq = F⊤. This is the separate
empty-added-stock endpoint `gi_M5_nested_outputs_equal`.

Now assume fun′(r) temporarily. The existing nontriviality theorem gives
r ≠ ⊤, equivalently ¬□r. Attainment at the pure proposition ⊤ gives
◇(r = ⊤), equivalently ◇□r. By T, the first fact rules out □□r; the second
rules out □¬□r. Hence ¬q. A further use of T gives ¬□q, which says q ≠ ⊤.
Combine this with the previously proved output identity, then discharge
fun′(r). Reversibility would make F injective, so the same collision gives
the conditional nonreversibility result. ▪

The key distinction is visible in the declarations:

| Endpoint or expression | What it establishes |
|---|---|
| `gi_M5_nested_input r` | The represented formula NC(□r) |
| `gi_M5_nested_NC_equivalent` | Theoremhood of q ↔ NC(q), a material biconditional |
| `gi_M5_nested_outputs_equal` | Theoremhood of Fq = F⊤ over the empty added stock |
| `gi_M5_nested_input_false_locally` | ¬q under a temporary fun′(r) assumption |
| `gi_M5_nested_local_collision` | The implication after the temporary assumption is discharged |
| host `A = B` | Equality of Isabelle representations or values, not automatically an object-language identity assertion |

The temporary calculus has only Assumption, Theorem, and MP constructors.
The proof does not necessitate a statement obtained under fun′(r), and it
does not apply theorem-level Equivalence to a merely local biconditional.
These restrictions matter: the old fixed-fun′ axiom stock is inconsistent,
whereas the old NC(r), ⊤ local collision is refuted by an exact model.
The new proof uses neither route.

Finally inspect `gi_M5_nested_native_collision_translated`. Its conclusion
is in the named calculus, but is explicitly a translated formula. Its
premises retain a rich variable stock, the Pure/Fun name map, a distinct
typed chart, and admission of conclusion constants into the signature.
The [repair record](M5_NESTED_COLLISION_REPAIR.md) describes its 21-endpoint
audit and the proof-dependency exclusion of the historical collision and
fixed-fun′ collapse endpoints. That evidence supports this repair, not a
claim that every source theorem is fully formalized.

## A route through the proof-theoretic integration

1. [Goodman_Book_Axiom_Extension.thy](../theories/axiom_extension/Goodman_Book_Axiom_Extension.thy)
   defines `goodman_book_proves`, written C+[T] ⊢ A. Its PE rule may use
   theorems depending on added axioms. This differs from ordinary consequence
   with temporary premises.
2. [Goodman_Book_Vocabulary.thy](../theories/axiom_extension/Goodman_Book_Vocabulary.thy)
   declares Pure and Fun as object-language constants and defines the basic
   formulas. It does not assign them semantic extensions.
3. [Goodman_CEV_Axiom_Preservation.thy](../theories/replay/Goodman_CEV_Axiom_Preservation.thy)
   supplies forward whole-proof preservation. The closed source-axiom
   stock, typing, name chart, and signature conditions remain part of the
   theorem. Forward preservation is not two-way proof equivalence.
4. [Goodman_Native_T6_Extras.thy](../theories/native_extras/Goodman_Native_T6_Extras.thy)
   independently defines L2, strong L2, Inv, TU, WI, and RS. Read its native
   routes next. Their refutations retain the stated classification/L2
   assumptions and do not establish a PP-alone contradiction.

## A route through the exact models

First read the native soundness interface in
[Goodman_Exact_Goodman_Soundness.thy](../theories/semantics/Goodman_Exact_Goodman_Soundness.thy).
Global validity ranges over every world and every typed assignment; truth
at the distinguished root is a different claim. The construction uses
HOL–ZF exact carriers and Bacon's constrained function domains, not arbitrary
full host function spaces.

Then read [Goodman_Exact_QLN_Model.thy](../theories/exact_qln/Goodman_Exact_QLN_Model.thy).
The generic interpretation satisfies the explicit no-PP zeroary/unary QLN
background. Its PP theorem is a classifier-membership iff. It does not
prove that membership, and therefore does not solve PP consistency.

The [M7 transfer](../theories/m_claims/Goodman_Exact_M7_Transfer.thy) distinguishes
the complete logical stock from all invariant operators. Its actual
generic-seed result must not be relabeled as a claim about every gluing
choice. For T9, read the locale assumptions before the
[native conclusion](../theories/t9/Goodman_T9_Native_Conclusion.thy): full
external PC and exact-carrier interpretation are genuine conditions.

The M5 enlarged models in `theories/m5/` have actual exact-carrier rebuilds.
Older secondary comparison models should still be described as secondary;
their retention does not make them exact Bacon-model instantiations.

## Checking what has actually been checked

Read `fixes`, `assumes`, `shows`, and the enclosing `locale` or `context`.
An assumed model or membership is not a constructed one. Follow the audit
entry to the exported statement and selected session. All 293 supplied
theory files are now selected: the frozen exact-enumeration and
exact-completeness files were wired in by task 4 (submitted for review),
with their transferred endpoints audited in the new exact-frame session. The
ten task-1 to task-5 theories added on 20 September 2026 are selected and audited.

Use the [verification guide](VERIFICATION.md) for the checker and dependency
requirements, and the native Isabelle dependency exports for navigation.
Do not run another build or export alongside the checker. The
[contributor guide](../CONTRIBUTING.md) gives bounded remaining tasks;
historical milestone prose may describe an earlier frontier.
