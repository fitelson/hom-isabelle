# Verification status

## Core compatibility update — 26 September 2026 (third pin refresh)

The core completed a comprehensive repository audit and its fixes, and added
the relevant-language (λI) development (independently defined λI calculus,
internal-conversion models, soundness, original-signature model existence
and global strong completeness) with a regression session. The dependency
pin was refreshed to that checkpoint (1,473 entries: 77 added core files,
70 changed, none removed; base revision unchanged; full core check exit 0).
Goodman's 303 theories, 87 catalogs and mathematical conclusions are
unchanged; the full serial build/export against the refreshed pin
**passed** (exit 0, 4 minutes 9 seconds, 60 sessions), all 87 catalogs
matching the retained certificates entry for entry, with the same two
provenance summary lines changing only in proof-node counts. See
[verification](verification/README.md).

## Core compatibility update — 26 September 2026 (earlier)

The core now proves generic full-C modal soundness and completeness for
countably declared signatures on arbitrary name carriers and for ZF-small
whole name carriers, in the nontrivial book model class, with rich stock
and the minimal primitive language. The dependency pin was reviewed and
refreshed twice the same day: first for the eight soundness/completeness
theories, then for the ZF-small-carrier development (six added core
theories, 70 changed files, 1,396 entries; independently reviewed; full
core check exit 0). See
[the review](docs/CORE_UPDATE_2026-09-26.md).

Goodman's 303 theories, 87 catalogs and mathematical conclusions are
unchanged. The PP question and tasks 6–9 remain open. Ordinary root
consequence is not the added-axiom extension: the new theorem applies
through the existing full-deductive-closure bridge, not by silently
replacing the extension with root assumptions. The full serial
build/export against the refreshed pin **passed** (exit 0, 3 minutes 51
seconds, 60 sessions): all 87 catalogs and statement files match the
retained certificates entry for entry, with 1,708 integration entries and
nine replay entries; two provenance summary lines changed only in their
proof-node counts because core proof terms changed. See
[verification](verification/README.md).

Location: ordinary folder `Applications/goodman-isabelle/` in the
Bacon–Dorr repository, with the same visibility. The core and application
session graphs and checks remain separate. Relocation did not change any
of the 303 theory files or the mathematical status below.

20 September 2026. **Tasks 1–5 are completed and independently accepted.**
The agreed report/reconciliation checkpoint (task 10) is complete:
[report](reports/GOODMAN_VERIFICATION_REPORT_2026-09-20.pdf) and
[claim ledger](docs/RECONCILIATION_2026-09-20.md).
At Branden's direction, tasks 6–9 remain open contributor projects.
This does not complete every original source claim, establish exhaustive
file-by-file audit coverage, or settle Goodman's consistency question.
No model search is running or automatically authorized to resume.

## Checked results and their limits

| Area | Checked scope |
|---|---|
| Proof transfer | Whole-proof forward preservation for H, Classicism and CEV+ extensions, with explicit typing, closed added axioms and signature conditions. Not an unqualified two-way calculus identification. |
| Goodman T-results | Principal T1–T8 results and T6 routes, with corrected T3 statements, explicit T2f/T5 hypotheses and underspecified T7b excluded. T6 retains its extra L2/classification assumptions. |
| TU⇒RS (accepted) | Native derivability of `gb_RS G`, of purity of the named witness R₊ = λp.(p ∧ fun′ p), and of its uniform rigid specification, from `gb_TU_RS_axioms G` = PP core ∪ {zeroary Exhaustion, ∃fun′, TU} in `gb_signature`. Exhaustion and ∃fun′ are retained; the weaker-scope claim without Exhaustion is not asserted. Derivability is established independently of whether this stock is consistent; its consistency remains unknown. |
| Finite PC (accepted) | For every type σ and every n, `gb_finite_PC G σ n`, i.e. ∀aₙ…∀a₁.((Pure(a₁) ∧ … ∧ Pure(aₙ)) → (Pure(λx.(x = aₙ ∨ … ∨ x = a₁ ∨ ¬⊤₀)) ∧ ∀x.((λx.…) x ↔ (x = aₙ ∨ … ∨ x = a₁ ∨ ¬⊤₀)))), is derivable from `gb_finite_PC_axioms G` = logical-purity ∪ application-closure schemas in `gb_signature`, by explicit induction on n; n = 0 is the empty selector. Finite comprehension only: not comprehension for arbitrary, potentially infinite external subsets and not T9's external full PC. |
| Biconditional operators (accepted) | For B_a = λp.(p ↔ a): `gb_bic_self_inverse G` (∀a.((λp.B_a(B_a p)) = λp.p)) is a C⁺ theorem over every added stock, including the empty one; `gb_bic_operator_pure G` (∀a.(Pure(a) → Pure(B_a))) and `gb_bic_group_member G` (∀a.(Pure(a) → B_a ∈ G)) are proved here over the native T6 PP core in `gb_signature`. This does not establish that PP is necessary. These are the notes' biconditional-operator examples, not WI, Inv, or a classification of G. |
| Frame representation (accepted) | The preserved enumeration and frame-completeness snapshots are now selected (sessions `Goodman_Exact_Enumeration`, `Goodman_Exact_Frame_Completeness`, bodies unchanged). `gi_exact_named_frame_representation_branch`: a closed named string sentence of the t-generated fragment over signature S is true at the root of some typed interpretation on Bacon's fixed frame iff it is true at some substitution of the single glued model `pp_e_complete_constants S`; `…_diamond` states the native ◇ = ¬□¬ form at the root, and `…_at_branch` realizes it at a branch [n]. Companion `gi_exact_named_frame_completeness_branch`/`_box`: truth at the root of every typed interpretation iff truth at every substitution of the complete model iff native □ at its root. Consistency here is frame satisfiability, not syntactic H consistency or H completeness. These are semantic characterizations, not an effective decision procedure. |
| Parametric Theorem 10.1 (accepted) | For an arbitrary type 'c of constant names: polymorphic exact evaluator `gi_exact_poly_denote` (equal to `gi_exact_named_denote` at 'c = string) and alphabet-independent gluing `gi_exact_poly_glued`; `gi_exact_Bacon_10_1_parametric_action` and `gi_exact_Bacon_10_1_parametric`: one glued interpretation realizes a countable (nat-indexed) family typed at t-generated types on the branches [n], for every closed named term of the t-generated fragment. Name coding is per term on its finitely many constants; no injection of all names into strings and no countability of the signature is used or asserted. Type e remains excluded. |
| Exact semantics | Bacon's represented exact appendix carriers, native interpretation and global extension soundness, full closed-logical denotation/stock correspondence, and concrete zeroary/unary QLN background. |
| L2 | Counterexample for the complete closed-logical stock in the specified no-PP interpretation. Not a countermodel to PP⇒L2. |
| M1–M3 | Bottom-type PP, qualified diagonal obstruction, invariant-carrier obstruction, and exact M3 algebra/freeness/meagerness. Unconditional higher-type classifier nonmembership remains open. |
| M4/M6 | Actual exact-stock constructions, replacing the old impossible all-view premise; not arbitrary enlarged-stock theorems. |
| M5 | Actual exact-carrier rebuilt model for the explicit no-PP background; Inv/TU root failures and WI nonderivability with its theorem-level scope; repaired NC(□r) conditional collision. |
| M7 | Exact-stock diagonal and failure of reachability for the verified generic seed and the stated fun′ class; not an identification with every arbitrary gluing. |
| T9 / Attack 3 | Abstract conditional counting results and exact-carrier instantiation with full external PC. Arbitrary-Henkin quotient/model bridge is unfinished. |
| Further consequences | J/S control, granularity, direct WI equations and proof-theoretic finite support, each with its exported hypotheses. Not a semantic compactness construction. |

See [source correspondence](docs/SOURCE_CORRESPONDENCE.md) for entry points.

The finite-PC axiom stock is a subset of the already verified no-PP QLN
background. Its consistency therefore follows, relative to HOL–ZF, from
`gi_exact_generic_QLN_background_consistent` and monotonicity of derivability.
This is a consequence of existing results, not a new separately cataloged
consistency theorem from task 2. It says nothing about consistency after
adding PP or the task-1 TU assumptions.

## Evidence

- **293 supplied `.thy` files**, byte-identical to the integration extraction,
  plus **ten new live theories** (`Goodman_Native_TU_RS_Witness`,
  `Goodman_Native_Finite_PC`, `Goodman_Native_Biconditional_Algebra`,
  `Goodman_Exact_Frame_Representation`, `Goodman_Exact_10_1_Parametric` and
  their audits), giving **303 supplied files** after tasks 1–5.
- **303 selected theory files** (all 293 extracted files, the two former
  enumeration/completeness snapshots now being wired into the session graph
  by task 4, plus the ten new ones).
- **1,708 integration catalog entries / 87 catalogs**, plus nine separately
  counted historical replay entries. All cataloged objects have zero oracle
  dependencies, residual kernel hypotheses and unresolved unification pairs.
  Explicit theorem premises are not removed by that check.
- **82 preserved files** have immutable provenance hashes. This includes
  the two formerly unselected snapshots; preservation is not new verification,
  and their selection by task 4 did not alter their bytes.
- The 21 M5-repair endpoints include a proof-node check excluding the
  historical collision and fixed-fun′ collapse endpoints. The integration
  checkpoint traversed 45,189 nodes. No conclusion about nonvacuity is
  inferred merely from a theorem's import list.

Standalone build evidence is recorded in [verification/README.md](verification/README.md).
The preserved [object-claim audit](docs/FINAL_OBJECT_CLAIM_AUDIT.md) and
[model-claim audit](docs/FINAL_MODEL_CLAIM_AUDIT.md) are source-level reviews
from the integration project. They are not a file-by-file comprehensive
audit of all 303 current theories or all of the core dependency.

## Remaining work

Contributor tasks **1–5 are completed and independently accepted**:
native TU⇒RS, all-type finite PC, the chosen biconditional-operator algebra
result, exact frame representation with its companion necessity theorem,
and arbitrary-name closed-term Theorem 10.1. Open-term transport is a
separate extension. The following tasks, matching CONTRIBUTING.md, are
deliberately left to contributors rather than assigned to an ongoing run:

6. **Unconditional M1 classifier nonmembership:** resolve the actual
   membership question, rather than repeating the existing conditional iff.
7. **General-model T9:** supply the Leibniz-quotient, selector, representation
   and group-action bridges, with full external PC explicitly distinguished
   from internally expressible comprehension.
8. **The particular glued fundamental proposition:** specify the intended
   gluing and prove the required freeness/fun′ condition for the M3/M7 instance.
9. **Source clarification:** obtain precise T7b and multiple-fundamental M4
   statements. The conflicting TU/RS prose also remains unresolved: the
   accepted Exhaustion-conditional result does not establish Goodman's
   intended scope or settle the weaker no-Exhaustion question.

**Task 10: completed in the agreed reporting/reconciliation scope.** The
new report and ledger preserve the unresolved obligations above. This is
not a declaration that the original unrestricted verification objective
or a comprehensive file-by-file source audit has been completed.

Further algebra, such as a separately packaged general biconditional
composition law, is an optional extension beyond task 3's selected result,
not a reason to mark that completed task unfinished.

The [contributor guide](CONTRIBUTING.md) supplies bounded deliverables and
completion criteria. M5's nested collision is **completed**, not a TODO.
Goodman's original PP consistency question remains an additional open
research question, not an implied deliverable of a passing repository build.

## Formerly included but not selected

- [Exact enumeration](theories/preserved-additions/exact-enumeration/Bacon_PP_ZF_Exact_Enumeration.thy)
- [Exact frame representation](theories/preserved-additions/exact-completeness/Bacon_PP_ZF_Exact_Completeness.thy)

These older snapshots were supplied as starting points, with checksums.
Contributor task 4 (completed and independently accepted, 20 September 2026)
wired them into the build under their recorded session names, with proof
bodies unchanged, and audited the transferred representation endpoints in
[Goodman_Exact_Frame_Representation.thy](theories/exact_frame/Goodman_Exact_Frame_Representation.thy).
Their five principal snapshot theorems are listed in that audit as preserved
results now inside the selected closure; the snapshot files themselves
carry no audit theory of their own.
