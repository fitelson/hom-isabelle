# Final-readiness audit: exact semantic claims

**Standalone provenance note:** this is a retained review of the integration
workspace, not a new review of every file in this repository. Old relative
paths and export names below identify that workspace's historical evidence.
Use [SOURCE_CORRESPONDENCE.md](SOURCE_CORRESPONDENCE.md) for current paths,
[STATUS.md](../STATUS.md) for current coverage, and `verification/audits/`
for the standalone release's exported certificates. The old report and
source PDFs are not distributed here.

**20 September follow-up:** the separately required NC(□r) object-language
repair is now verified and consolidated, not merely a semantic candidate.
See [the completed repair](M5_NESTED_COLLISION_REPAIR.md).
The old NC(r) local collision remains refuted; the model constructions and
other scope qualifications below are unchanged. The original audit is
preserved as a record of its 19 September baseline.

19 September 2026. Independent read-only audit of the model-sensitive portion
of the integration goal, against all seven pages of Goodman's original notes,
the historical report, current theory statements and exported theorem objects.
This is a scope and source-correspondence audit, not a new Isabelle build.
The checked baseline is the 20:21 serial check and 1,553-object checkpoint.
Later work must update the findings below before declaring completion.

## Verdict

The integration genuinely repairs the earlier M4/M6 instantiation gap and
constructs an actual M5 enlargement on Bacon's exact carriers. The main
remaining mathematical/interface gaps found in this audit are:

1. **Arbitrary-alphabet Theorem 10.1 is not yet proved.** Both the preserved
   theorem and its new named transfer fix string constants. An arbitrary
   subset of string constants is not an arbitrary cardinality of constants.
2. **The preserved enumeration/frame-theory representation results need
   integration.** They are actual old exact-carrier proofs, not conjectures,
   but are outside the current frozen/native adapter closure.
3. **The old M5 local collision assertion is false.** A new checked exact
   counterexample refutes the indicated pair. The corrected semantic
   collision is proved; the nonexplosive object-language nested-input
   repair was still in progress at the audit baseline.

These are not reasons to discard the completed results. They prevent a
blanket claim that every advertised report assertion has already been
faithfully transferred.

## Sources and evidence actually inspected

- Original: Higher_Order_Metaphysics/sources/pdfs/Goodman_PP_Project_Notes.pdf,
  all seven printed pages. In particular M1–M2 at p.4, M3–M5 at p.5,
  M5–M7 and suggested attacks at p.6, and the audit warnings at p.7.
- Bacon, Logical Combinatorialism, appendix Definitions 7.1, 7.2 and 8.1,
  Proposition 8, and Theorem 10.1. The function-space condition is
  i·x=i·y ⇒ i·f(x)=i·f(y), not an arbitrary full function space and not a
  PER replacement.
- Historical report:
  GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.tex, especially
  lines 190–250, 589–701, 828–891, 1041–1128, and 1471–1491.
- Export catalogs: exact-stock; l2-10-1-t7-final; m123467-t8-final;
  residual-results. Specific inspected statement catalogs include
  exact-stock, exact-l2-object, exact-m1-bottom, exact-m2, exact-m3-algebra,
  exact-m3-topology, exact-m4-repair, exact-m6-repair, exact-m7,
  general-M1-native, m5-classifications and m5-fixed-pair.
- Current proofs/interfaces: Exact_QLN_Model, Exact_Goodman_Soundness,
  Exact_Classicist_Soundness, General_M1_Native_Semantics,
  Exact_Expanded_Stock, Exact_M5_Rebuilt_Model, T9_Native_Purity,
  T9_Native_Conclusion and T9_Infinitude.
- Preserved upstream Exact_10_1, Exact_Enumeration and Exact_Completeness
  were inspected directly. Their old status prose was not taken as a
  substitute for their definitions and theorem types.

## Exact foundations and the report's four appendix tasks

### Carriers and Proposition 8: faithful in the represented specialization

Frozen exact-first/stage02/Bacon_PP_ZF_Full_MSet defines the arrow domain by
Bacon's actual function-space condition and defines its action by applying
the output action to evaluation at a canonical preimage. The all-type
closure, action laws and surjectivity are proved, culminating in
bacon_surjective_mset_at_every_type_exact_hol_zf and the function-space
surjectivity endpoint.

The proposition domain codes P(N<ω) in HOL–ZF; Ind is the chosen singleton
surjective M-set. This is a faithful **instance** of Bacon's general
construction. It is not a theorem that every abstract monoid and arbitrary
surjective individual M-set has this particular coding. No PER-domain
replacement appears in this construction. Prefix presentation and Bacon's
division action are connected using word reversal; those coordinate changes
must remain explicit when comparing formulas involving a nontrivial word.

### Task 1: real arbitrary-name gap

At exact-first/stage06/Bacon_PP_ZF_Exact_10_1.thy, the definition
pp_e_Bacon_glued_constants explicitly has type

    (nat → string → otype → ZF) → string → otype → ZF.

pp_e_Bacon_10_1 and its term-action lemma use the old oterm evaluator.
The new gi_exact_Bacon_10_1_named likewise uses string book_named_term.
They cover all allowed occurrence types in the t-generated fragment and
arbitrary interpretations of those string names; they do not cover an
arbitrary name type. The unrelated parametric H/Classicism completeness
theorems are not exact-frame gluing theorems and cannot fill this gap.

Bacon's theorem is stated for a signature Σ without a cardinal restriction.
His explanatory phrase “arbitrary signatures” particularly contrasts
higher-type with merely propositional constants, but the formal statement
does not impose countability. The old report advertises the unqualified
arbitrary-signature result. The correction required by the present goal is
a genuine parametric theorem, not a silent change of that claim to strings.

A bounded implementation route is available: retain the unchanged
alphabet-independent pp_e_branch_glue at each type, define a polymorphic
constant interpretation and evaluator, prove the action-related evaluator
induction, then glue each constant coordinate. Every term has finite
support, but there must be no global injection of arbitrary names into
strings. Keep the t-generated restriction and countable branch sequence.
Open terms additionally need a correctly related environment; do not erase
the assignment condition from “arbitrary terms.”

### Task 2: soundness is substantively covered

Frozen stage07 proves exact old H/C/CE/CEV soundness, including individual
existence and arbitrary finite vectors. The new native development proves
full minimal-model fields, βη/environment preservation, actual all-type
Modalized Functionality and theorem-level PE, and inducts over the actual
native C+[T] proof predicate.

pp_e_constants.gi_exact_goodman_extension_global_sound assumes that each
added axiom is globally valid. The interpretation is typed; G is rich.
Global validity quantifies every world and every typed assignment.
This assumption is necessary, not a missing soundness proof. Root truth
of a fixed fundamental instance cannot replace global validity.

### Tasks 3–4: preserved proofs exist but integration remains

Upstream canonical/Bacon_PP_ZF_Exact_Enumeration.thy contains:

- pp_e_consistent_sentence_enum_range;
- pp_e_enumerated_sentence_true_at_branch;
- the typed pp_e_complete_constants interpretation and component action.

Upstream canonical/Bacon_PP_ZF_Exact_Completeness.thy contains:

- pp_e_Bacon_consistency_representation;
- pp_e_Bacon_exact_completeness;
- pp_e_Bacon_exact_theory_characterization.

These results use the fixed string signature and t-generated sentences.
Their “consistent” predicate is **semantic frame consistency**:
a sentence has some typed exact-carrier constant interpretation.
Their “complete theory” is the theory common to all interpretations on the
fixed frame. It is not syntactic H consistency or H completeness. The old
report expressly preserves this distinction and is correct on that point.

The current integration tree lacked these two frozen theories and a named
sentence-level transfer at inspection time. Freezing/building them and
transporting their statements through the proved decoder is a genuine,
manageable completion task. It does not require identifying their glued
constants with the generic-seed Pure/Fun interpretation.

## Complete logical stock and L2

gi_exact_logical_denotation_sets_equal proves equality of the entire native
closed-logical denotation set with the old closed typed logical-term set.
gi_exact_native_stock_iff_original adds the worldwise saturation bridge.
Both directions of coverage are present; the result is not limited to the
translated image or to finitely enumerated operators.

The L2 object export contains gi_exact_generic_L2_false_at_root, its actual
native denotation bridge, failure of global validity, and
gi_exact_QLN_background_not_proves_L2. The typed root equality bridges
connect the raw operator counterexample to the actual quantified formula.
This supports failure of L2 for the complete fixed logical stock and its
specified no-PP QLN interpretation. It does not establish failure for every
possible enlarged pure stock, every world, or every PP interpretation.

## M1: what is and is not completed

Bottom-type PP is genuinely instantiated:
gi_M1_NC_denotes_exact_classifier gives equality of the native closed
noncontingency operator and the actual proposition-purity classifier;
gi_M1_exact_bottom_PP_gvalid follows. The proof is not
invariance ⇒ logical definability.

The exact footnote-59 result retains PP, Purity of Fun, QSS and unique
proposition-level fundamentality. Its typed diagonal and native formulas
are evaluated rather than postulated.

The general native theorem now works in the independent
book_full_minimal_model interface with arbitrary value carrier and actual
Leibniz identity. gi_book_native_fn59_contradiction assumes local Pure(D),
QSS and unique fundamentality. gi_book_fn59_from_native_extension_soundness
uses the separately proved native purity derivation and explicitly requires
truth preservation of C+[T] over that purity stock.

**This matches the old report's carefully qualified general-Henkin scope:**
the old theorem expressly assumed compositional clauses, type closure,
identity congruence and soundness of the CEV/vector-equivalence machinery.
A bare H minimal model was never enough. Thus the explicit soundness
premise is not itself a newly discovered missing mathematical proof.
However, a claim about every independently defined varying-domain modal
model requires a per-world minimal-model adapter and its own C+[T]
soundness theorem. The current theorem must not be advertised as supplying
those adapters automatically.

Existence/unique fundamentality and Purity of Fun must be stated or clearly
in force. The bare slogan “QLN + PP + PureFun is inconsistent” without a
fundamental witness is too broad.

The classifier at the next type exists in the exact function carrier and
has exactly the closed-logical-stock extension (the general classifier
lemmas supply this). The current PP result remains an iff with its
membership in the next pure stock. No unconditional nonmembership has been
proved. The old report already states this qualification, so it is not an
unfinished proof that can honestly be filled in by rewording a conditional.
Goodman's original unconditional M1 assertion is not verified by these
results. Nor should the classifier-extension theorem be relabeled as a
formal proof of arbitrary complete-Boolean-lattice structure if no such
supremum theorem is cited.

## M2 and M3

M2 is instantiated on actual exact values. The classifier map is a bijection
onto all invariant unary values, Cantor comparison is transferred to the
actual proposition carrier, and every typed R has an explicit invariant
collision. These facts refute the invariance reading of purity, not logical
purity itself.

M3's zero/difference closure is witnessed by actual closed logical terms;
gi_exact_M3_fun_prime_iff_free has no leftover conditional stock locale.
Necessity and necessity-of-negation yield the two extreme views. The
meagerness result is stated using the explicit finite-cylinder definition
gi_M3_product_meager, not a silently imported library topology. Its
definition and the finite-cylinder argument implement the intended product
topology claim. The actual pp_e_generic_raw_seed is proved free.

This does not identify an arbitrary Theorem10.1 interpretation with that
generic seed, nor prove that every choice of glued components has a
fundamental/free root. Those are materially different quantifiers.

## M4 and M6: old impossible premise removed, not assumed

The old fixed-r premise “every view of r is fun′” is rigorously impossible
for the complete exact stock: root fun′ implies an empty view, while the
empty proposition is not fun′. This is not the correctly guarded boxed QSS
formula.

New M4 proves, for **every exact-stock fun′ r**, existence of a suitably
chosen branch lift p that remains fun′ but from which no pure operator
recovers r. Consequently p is outside r's reversible orbit. The branch is
chosen from r's nonconstant proper view; the theorem does not promise that
a predetermined branch works. The actual generic-seed instance is proved.

New M6 proves:

- every pair of distinct substitutions is separated by some fun′ proposition;
- every proposition has an unreachable arbitrary target;
- an explicit strict-inclusion fun′ pair lies in different reversible
  orbits and remains inclusion-related under every substitution;
- a specified joint assignment is therefore impossible.

The exported statements contain neither the false all-view-QSS premise nor
an uninstantiated arbitrary-stock condition. The arbitrary missing target
is not claimed to be fun′. The multiple-fundamental “wide Fun” proposal in
the notes remains underspecified and separate.

## M5: actual rebuilding, and a newly corrected collision

The expanded stock is denotations of **all** closed typed terms over k at
t→t, including lambda and higher-order quantification. It is not just an
application grammar. Its countability, invariance, typing and application
closure are proved; constant abstraction proves equality with the least
application hull. Native closed-term coverage is proved in both directions.

The actual rebuilt interpreter has k=K and the intended Pure/Fun coordinates.
It preserves the expanded-language denotations. Both the uniform repaired
exotic and the source's fixed pair {[5]}, {[5],[]} instantiate its locale.
The fixed-pair export certifies QLN, QSS, purity, actual denotation,
involution and nonuniformity. Thus the old report's “secondary comparison
model only” status is outdated: the exact-carrier construction is real.

The certified stock is the explicit no-PP background: logical purity,
application closure, unique proposition-level fundamentality/no other
fundamentals, and zeroary/unary QLN. QSS is separately proved globally.
No PP or PureFun is smuggled in; a separate Persistence schema is not part
of the advertised certificate. Countability concerns the basis/root stock,
not every world's saturated extension.

TU and Inv have actual root failures and native nonderivability.
WI nonderivability/failure of global validity follows via its theorem-level
implication to TU; this must not be reported as a proved root implication.

The fixed-constant 10.1 theorem preserves K literally and is useful
independent metatheory. The actual rebuilt generic model does not claim to
be the specific interpretation returned by that gluing function. This is
an alternative exact-carrier construction of the required independence
model, not a replacement of Bacon's carriers.

The historical M5 pair NC(r),⊤ is false under a merely local fun′ premise,
as the new actual-model counterexample proves. Old axiom-stock collision
proofs are valid but the fixed-fun′ stock is already inconsistent through
necessitation and possible purity. They cannot certify a nonexplosive
local theorem. The semantic repair using UNIV−{[]} proves actual
noninjectivity of the displayed operator; the proposed NC(□r) local
object-language repair must be checked separately.

## M7: quantifiers and the chosen seed

The complete-stock diagonal works for **every typed R** and gives an exact
proposition that is neither pure nor a pure unary image of R.
This establishes zeroary/unary Fundamental Completeness failure in the
single-fundamental setting, not merely a secondary-tree result.

The invariant reachability iff is proved for every typed R. More strongly,
every exact-stock fun′ r has two equal views at distinct words and thus a
singleton outside every invariant-operator image. The actual generic
fundamental seed satisfies the premise. This is an explicit orbit
collision, not an invalid inference from a stabilizer.

No theorem says every arbitrary R has a noninjective orbit, or that every
arbitrary 10.1 gluing is fun′. If “Bacon's chosen glued r” denotes a
particular pp_e_complete_constants coordinate, its freeness still needs
identification; the existing result applies immediately once that premise
is proved. The original report left that choice-sensitive instance open.
The new generic-model instance should be reported as newly settled without
equating the two constructions.

## Typed/external-PC boundary

The new T9 results use actual root-pure exact values, their pure inverse
group and actual kinds. The native core is globally valid; L2 and ∃fun′ are
actual root formulas; all applications carry the correct type premises.
Full external unary PC ranges over every external subset of the pure
unary stock. It is stronger than availability only for internally
represented or definable subsets.

The pure selector has the corrected unary type and is constructed from
the higher-order PC witness, not identified with that witness. The
infinitude/exponential bound is a conditional semantic theorem. It does
not show that PC or L2 follows from PP, construct a model of those
assumptions, or automatically generalize to every Henkin quotient model.

## Recommended completion order

1. Complete genuine arbitrary-alphabet exact gluing; preserve fragment and
   assignment guards.
2. Freeze and transfer exact enumeration/frame-theory representation.
3. Finish/refute the nonexplosive M5 nested-input derivation and report the
   checked counterexample to the old pair.
4. Reconcile the corrected report against this claim map, keeping M1's
   classifier nonmembership open, general-model soundness explicit,
   M7's generic/glued distinction, and T9's exact/external-PC scope.
5. Perform the final serial build and re-export the new actual statements.
