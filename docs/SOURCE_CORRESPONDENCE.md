# Source statements, verified results, and remaining scope

**H soundness and completeness are proved in the scopes below.** For
**Bacon's full-type Classicism C**, generic modal soundness is proved
for the explicit nontrivial class without a cardinality restriction.
Original-signature model existence and the root-consequence and
consistency equivalences are proved for every signature whose
declared-name union admits an injective code into the elements of a ZF
set, on an arbitrary name carrier; countably declared signatures and
ZF-small whole carriers are special cases (26 September 2026). The
remaining language, carrier, foundation and source qualifications are
stated below.

The paper's numbering refers to the **1 July 2022 draft** of Bacon–Dorr's
*Classicism*. This is a curated source map, not a claim that every statement
in the book or paper has been formalized. “Proved” refers to the maintained,
checked development; ongoing unverified work is not counted.

The [partial source audit](PARTIAL_SOURCE_AUDIT_2026-09-10.md) covers 120
of 1,380 theory files, not this whole table. It distinguishes the source
language from the constructor-based intermediate calculus and records
remaining raw/guarded βη and sentence-premise closure obligations. These
are source-correspondence qualifications, not failed kernel derivations.
In particular, model existence for an encoded interface must not silently
be promoted to an unrestricted source-model claim while an interface
equivalence used for that promotion remains unproved.

## At a glance

| Development | Soundness | Model existence and completeness | Main boundary |
|---|---|---|---|
| H: Bacon–Dorr's named full-F language | Proved, including local soundness for open premises | Sentence-set model existence and closed strong completeness proved | Completeness requires closed premises and conclusion, a rich variable stock, and an explicit carrier |
| H: Bacon's full-F minimal language | Proved for the printed-guard calculus | Original-signature model existence, countermodels, and global strong completeness proved | Open formulas and arbitrary premise sets allowed; full minimal language, rich stock, and the specified general-model class |
| C: Bacon–Dorr's relational-type language R | Proved for the stated category and action semantics | Category representation/completeness and single-formula action completeness proved | R-language scope; explicit carriers; action-model representation uses HOL–ZF |
| C: Bacon's full-type minimal language | Generic soundness for every independent nontrivial modal model and admissible interpretation, with a rich stock and no cardinality restriction | Original-signature model existence, derivability iff root consequence, and consistency iff satisfiability for signatures whose declared-name union is bounded by a ZF set, on arbitrary carriers including ZF; countably declared and ZF-small-carrier scopes retained as special cases | HOL–ZF; full minimal language; rich stock; inhabited domains and a false proposition at every world; root consequence; declared unions with no bounded injection are outside the construction |

Here **F** is the full simple-type grammar; **R** is the paper's relational-type
restriction. For the book's H, “global” truth means truth under every typed
assignment, including when a formula has free variables. It must not be
confused with truth at every world of a modal model.

## H: Bacon–Dorr's named full-F language

These are pure Isabelle/HOL results. Soundness is carrier-polymorphic;
the completeness statements quantify all independent models on an explicitly
specified sufficiently large carrier, not only the constructed canonical model.

| Result | Source | Formal endpoint and scope |
|---|---|---|
| Independent H calculus — **defined** | Figure 2, p.8 | [`paper_named_H`](../theories/base/source_vocabulary/Bacon_Source_Named_H.thy): ten-constructor named presentation, not a definition by semantic validity |
| H theorem soundness — **proved** | Figure 2, p.8, and Theorem 3.2, pp.44–45 | [`paper_named_H_soundness`](../theories/base/source_models/Bacon_Source_Named_H_Soundness.thy): every H theorem is valid in every independent named BBK model, with that model's rich variable stock |
| H local soundness — **proved** | Project-defined local consequence associated with Figure 2 H | [`paper_named_local_soundness`](../theories/base/source_models/Bacon_Source_Named_H_Soundness.thy): local derivability preserves truth at a typed partial assignment adequate for the premises and conclusion, every premise being a type-t formula of L(Σ) (hypothesis `premise_languages`); open formulas and infinite premise sets allowed |
| H model existence — **proved** | Theorem 3.2, sentence-set form | [`paper_named_BBK_model_existence`](../theories/base/source_models/Bacon_Source_Named_Model_Existence.thy): constructs a model for a consistent sentence set in a rich stock, with the stated carrier |
| H closed strong completeness — **proved** | Theorem 3.2, sentence-consequence form | [`paper_named_closed_strong_completeness`](../theories/base/source_models/Bacon_Source_Named_Closed_Strong_Completeness.thy): derivability from a sentence set iff semantic consequence; arbitrary signatures and sentence sets, but closed premises and conclusion |
| Countable-domain refinement — **proved** | Refinement of the Theorem 3.2 construction | [`paper_named_BBK_countable_signature_model_existence`](../theories/base/source_models/Bacon_Source_Named_Countable_Model_Existence.thy) and [`paper_named_nat_closed_strong_completeness`](../theories/base/source_models/Bacon_Source_Named_Nat_Strong_Completeness.thy): countably declared signatures admit the stated natural-number-domain version; the entire constant-name type need not be countable |

Open-premise **soundness** in this section does not assert open-premise
**completeness** for the project's local consequence relation for paper H. The book result
below uses its separately defined global consequence relation.

### What Figure 2 and Theorem 3.2 say

**Figure 2 specifies H's proof rules.** It includes propositional reasoning,
universal instantiation, existential generalization, reflexivity, Leibniz's
law, beta and eta conversion, modus ponens, and the two quantifier rules.
It does not define theoremhood by truth in models. This matters because
soundness and completeness must connect independently defined syntax and
semantics.

**Theorem 3.2 says that BBK models characterize H.** On the soundness side,
every H theorem holds in every BBK model. On the model-existence side, every
H-consistent set of sentences holds in some BBK model. Consequently, for
sentences, derivability from a set of premises agrees with truth in every
model of those premises. The theorem also gives a countable version: when
the signature is countable, the domains can be taken inside a fixed
countable set such as the natural numbers. The Isabelle endpoints above
make the carrier and variable-stock requirements explicit, and refine
countability to the declared constants rather than the ambient name type.

## H: Bacon's full-F minimal language

These are also pure Isabelle/HOL results. They concern Bacon's general models
and the full minimal logical basis, not his later modal models for Classicism.
The printed free-for proviso is connected to the implementation's other
calculus by a proved correspondence, not by identifying their definitions.

| Result | Source | Formal endpoint and scope |
|---|---|---|
| General-model environment condition — **defined and characterized** | Definition 14.13 | `book_environment_conditions` and its equivalence lemmas: agreement on the intersection of free-variable sets |
| Leibniz quotient — **proved** | Proposition 15.5, p.322 | `book_proposition_15_5_full_minimal`: actual quotient for the full minimal profile, with explicit definedness assumptions |
| H soundness for the printed calculus — **proved** | Chapter 5 calculus; Chapters 14–15 general-model semantics | [`book_printed_theory_soundness`](../theories/base/book_models/Bacon_Book_Printed_Completeness.thy): derivability preserves global truth in every independent full minimal model; rich variable stock and truth of all premises are explicit |
| H original-signature model existence — **proved** | Theorem 15.3, pp.320–321 | [`book_printed_canonical_model_existence`](../theories/base/book_models/Bacon_Book_Printed_Completeness.thy): constructs a full minimal model satisfying a consistent typed premise set in its original signature |
| H global strong completeness — **proved** | Corollary 15.2, p.321 | [`book_printed_canonical_strong_completeness`](../theories/base/book_models/Bacon_Book_Printed_Completeness.thy): derivability from S iff global semantic consequence over every independent full minimal model on the explicit carrier |
| H countermodel with a falsifying assignment — **proved** | Countermodel direction of the same completeness result | [`book_printed_canonical_countermodel`](../theories/base/book_models/Bacon_Book_Printed_Completeness.thy): if A is not derivable from S, constructs a model making every premise globally true and an assignment falsifying A |

The last three results allow **open formulas, infinite premise sets, and
uncountable signatures**. They retain the full-F minimal language, rich
variable stock, the specified model class with its witnessed closed-value
condition, and explicit carrier scope. They do not cover every general
λ-sublanguage or richer primitive basis in the book. The documented
universal-closure repair of the countermodel argument also remains relevant.

### What the numbered book results say

**Definition 14.13 specifies the environment model condition.** An
interpretation assigns an appropriately typed value to a term under an
assignment. Variables receive their assigned values, and application is
interpreted by the applicative structure's application operation. In
addition, beta–eta-equivalent terms receive the same value when their
assignments agree on the intersection of their free-variable sets. This
condition accommodates nonfunctional structures: it does not simply
identify every higher-order object with a set-theoretic function. The
formalization preserves the intersection condition and the language guards.

**Theorem 15.3 is the general-model existence theorem for H.** Every
consistent theory has a general model making its sentences true. The
construction adds witnesses, completes the theory, and constructs suitable
domains from terms. The verified full-minimal instance supplies
an actual model of the original signature, not merely a model in an enlarged
witness language. Its original premises may be open and form an infinite set.

**Corollary 15.2 turns model existence into completeness.** If a formula is
true in every model of a theory, it is provable from that theory. Together
with soundness, this gives the equivalence between provability and semantic
consequence. For open formulas, the checked countermodel argument uses the
negation of the conclusion's universal closure: the countermodel satisfies
all premises under every typed assignment but falsifies the conclusion at
some assignment. It does not incorrectly require the open conclusion's
negation to be true under every assignment.

**Proposition 15.5 constructs a truth-preserving Leibnizian quotient.** Two
objects are Leibniz equivalent when every predicate available in the model
gives them the same truth value. The proposition identifies such objects
and shows that the quotient remains a model, makes the same sentences true,
and is Leibnizian: distinct objects can be distinguished by a predicate.
The Isabelle proof constructs the quotient, proves that application and
interpretation are well defined, and verifies truth preservation. Its
checked scope is the full minimal model class with a rich variable stock,
not every general sublanguage or richer primitive profile considered in
the book.

## H over Bacon's relevant (λI) language

These are pure Isabelle/HOL results in session `Bacon_Book_Lambda_I_Development`
(`theories/base/book_lambda_I/`). They concern the sublanguage of Definition
9.2 in which every abstraction binds a variable occurring free in its body,
and an independently defined theory calculus for it. They do not identify
that calculus with the restriction of H to λI formulas.

| Result | Source | Formal endpoint and scope |
|---|---|---|
| λI is a general λ-language — **proved** | Definitions 9.1–9.2 | [`book_lambda_I_general_lambda_language`](../theories/base/book_lambda_I/Bacon_Book_Lambda_I_Syntax.thy): closure under substitution of λI terms, directed βη-reduction with α, relettering and logical-symbol substitution; the vacuous abstraction is excluded |
| λI theory calculus — **defined, embedded one way** | Definition 9.8 restricted to λI formulas | [`book_lambda_I_derivable`](../theories/base/book_lambda_I/Bacon_Book_Lambda_I_Calculus.thy): PC1–PC3, UI over λI terms, exact-capture β/η, MP, binder Gen with the occurrence guard; `book_lambda_I_derivable_embeds` into full H; `book_lambda_I_presentations_iff` for the constant-form Gen |
| Internal conversion and α — **proved as partial infrastructure toward Proposition 9.1** | Proposition 9.1 (raw-conversion internalization itself is not proved) | [`book_lambda_I_alpha_conv`](../theories/base/book_lambda_I/Bacon_Book_Lambda_I_Conversion.thy), `book_lambda_I_conv_derivable_iff`: α-variants of λI terms are joined by β/η steps through λI terms, and internal conversion transports derivability |
| λI models — **defined**, soundness **proved** | Definition 14.13 read through Proposition 9.1; Theorem 15.1 | [`book_lambda_I_model`](../theories/base/book_lambda_I/Bacon_Book_Lambda_I_Models.thy): denotation invariant under internal conversion, minimal-basis truth clauses, a false proposition, and an actual typed assignment required (the witnessed-assignment convention); `book_lambda_I_model.book_lambda_I_soundness` under a rich stock; `book_full_minimal_model_lambda_I` restricts every full minimal model; an actual model with an assignment satisfying ⊥ → ⊥ is the regression session `Bacon_Book_Lambda_I_Regressions` |
| λI original-signature model existence — **proved** | Theorem 15.3, λI instance | [`book_lambda_I_canonical_model_existence`](../theories/base/book_lambda_I/Bacon_Book_Lambda_I_Canonical_Model_Existence.thy): a λI model of the original signature satisfying a consistent, possibly open and infinite λI premise set; term model on internal conversion classes of closed λI terms |
| λI global strong completeness — **proved** | Corollary 15.2, λI instance | [`book_lambda_I_canonical_strong_completeness`](../theories/base/book_lambda_I/Bacon_Book_Lambda_I_Canonical_Completeness.thy): derivability from S iff consequence over every λI model on the canonical carrier; countermodel with a falsifying assignment `book_lambda_I_canonical_countermodel_with_assignment` |

Boundaries that remain visible, each a distinct open question: (i)
identification of the independently defined λI calculus with HJ, the least
relevant-language logic of Definitions 9.9–9.10, whose substitution
closure is not proved; (ii) conservativity of full H over the λI calculus,
that is identification with H restricted to λI formulas, of which only the
one-way embedding is proved; (iii) the λI printed/exact β correspondence,
the calculus using exact-capture β only; and (iv) the internalization of
raw βη-conversion between λI endpoints (a typed Church–Rosser argument not
available here), so the model class is the internal-clause class and
completeness for the raw-invariant subclass is open.

## Classicism C: Bacon–Dorr's relational-type language R

This is distinct from the full-F H development above. The category results
are in HOL; the explicit set-valued action-model representation uses HOL–ZF.

| Result | Source | Formal endpoint and scope |
|---|---|---|
| Native C/Equivalence presentations — **correspondence proved** | Appendix A.2–A.3; p.12/p.14 presentations | [`paper_R_classicism_equivalence_iff`](../theories/classicism/action_models/Bacon_Source_Relational_Classicism_Equivalence_Iff.thy): `paper_R_classicism_proves` and `paper_R_equivalence_proves` coincide under an R-rich stock (`paper_R_rich G`, needed for the Equivalence-to-C direction through A.3); not an automatic claim about every finite presentation |
| Truth identity under abstraction — **proved** | Proposition A.2 | [`paper_R_classicism_A2`](../theories/classicism/action_models/Bacon_Source_Relational_Classicism_A2.thy): a proved formula, abstracted over a typed variable vector, is identical to the corresponding constant-truth abstraction |
| Closure under Equivalence — **proved** | Proposition A.3 | [`paper_R_classicism_A3`](../theories/classicism/action_models/Bacon_Source_Relational_Classicism_A3.thy): proved equivalence of formulas yields identity of their corresponding abstractions |
| C category soundness and completeness — **proved** | Theorem 3.12 | [`paper_R_arbitrary_signature_classicism_selected_category_iff`](../theories/classicism/action_models/Bacon_Source_Relational_Arbitrary_Signature_Classicism_Completeness.thy): derivability iff membership in the common theory of every independent intensional selected BBK category on the displayed sufficiently large carrier |
| C action-model soundness — **proved** | Definition 3.20 and Theorem 3.23 | [`paper_ZF_classicism_valid_on`](../theories/classicism/action_models/hol_zf/Bacon_Source_ZF_Action_Validity_On.thy): soundness on every world-label type, with typed adequate assignments and the independent action-model conditions |
| C action-model completeness — **proved** | Theorem 3.23 | [`paper_ZF_arbitrary_signature_action_iff`](../theories/classicism/action_models/hol_zf/Bacon_Source_ZF_Arbitrary_Signature_Action_Completeness.thy): single-formula derivability iff validity at arbitrary signatures; R-richness, R-language guards, and an explicit world-label carrier remain |

The single-formula action theorem is **not** an arbitrary-infinite-theory
compression or strong-completeness theorem. None of these R-language results
by itself completes the book's full-type modal semantics.

### What the numbered paper results say

**Proposition A.2 lifts theoremhood to identity with truth under abstraction.**
If P is a theorem, abstracting P over a vector of variables yields the same
operator as abstracting constant truth over that vector. This is an identity
of higher-order objects, not just agreement in truth value on one assignment.
The native R proof retains the typed-vector and rich-stock assumptions.

**Proposition A.3 establishes closure under Equivalence.** If A and B are
provably equivalent, their abstractions over the same variable vector are
provably identical. The empty vector gives propositional identity itself.
This connects the identity-axiom approach to Classicism with its
Equivalence-rule presentation. The verified native p.12/p.14 correspondence
is kept distinct from the additional correspondence required for the paper's
finite Figures 3–4 axiomatization.

**Theorem 3.12 characterizes Classicism using intensional categories of BBK
models.** The relevant models are considered together with homomorphisms
between them. Intensionality requires those maps and the available arguments
to distinguish distinct higher-order objects by their resulting truth values.
The formulas true throughout every such category are exactly the Classicist
theorems. The Isabelle result quantifies independent selected categories on
an explicitly sufficient carrier and works at arbitrary signatures in the
paper's R language. It does not assume that an arbitrarily small, previously
chosen carrier can accommodate every signature.

**Definition 3.20 states when an action premodel is a model.** Every
well-typed term must receive a value in the correct domain at every relevant
object and arrow, under every adequate assignment. This includes abstraction
closure, not merely closure under application. Propositions are represented
by sets of arrows; a proposition holds at an object when its denotation
contains that object's identity arrow. Model validity evaluates at the base
object and quantifies the appropriate assignments. These independent
modelhood and truth conditions are what the action soundness/completeness
results concern.

**Theorem 3.23 gives soundness and completeness for action models.** Every
Classicist theorem is valid in every action model; conversely, a formula
valid in every action model is a Classicist theorem. The construction connects
the category characterization to concrete domains of propositions and
higher-order operations with actions along arrows. In Isabelle, soundness
is independent of the world-label carrier, while completeness specifies a
sufficient carrier. The arbitrary-signature result is for a single formula,
not an unrestricted strong-completeness theorem for arbitrary premise sets.

## Classicism C: Bacon's full-type minimal language

The independent proof calculus includes all-type Modalized Functionality.
It is not the older Equivalence-rule base merely renamed. The modal
construction uses the separate HOL–ZF foundation.

| Result | Source | Formal endpoint and scope |
|---|---|---|
| Full-type C calculus — **defined, with presentation bridges proved** | p.160 and p.178 endnote 5 | `book_full_C_proves`: H+MF+PE, distinct from the older Equivalence-rule base |
| Structural modal-model conditions — **defined** | Displayed Definition 18.1 | `book_ZF_modal_model`, retained with the documented future-restricted implication convention; admits all-true models |
| Nontrivial modal-model refinement — **defined and instantiated** | Explicit source clarification, using Definition 15.1 (pp.314–315) and the p.392 general-model claim | `book_ZF_nontrivial_modal_model`: inhabited domains and a false proposition at every world; not an additional clause claimed to be printed in Definition 18.1 |
| Canonical modal model — **proved** | Proposition 18.5 | `book_full_C_coded_frame.full_ZF_canonical_modal_model`: every field of the independent model predicate is constructed from a rich stock, an eligible canonical root, and a total bounded term code injective on the terms admitted by the ambient signature; countable coding is a special case |
| Canonical interpretation — **proved** | Definition 17.13 | `full_ZF_canonical_interpretation`: the constructed model satisfies every independent interpretation clause |
| Generic interpretation existence — **proved** | Definition 17.13; Theorem 17.1, interpretation-existence component | [`generic_interpretation_exists`](../theories/classicism/book/modal_semantics/interpretation/Bacon_Book_ZF_Generic_Interpretation_Existence.thy): every independent full-minimal modal model has an admissible interpretation; no countability, richness, supplied interpreter or extra nonemptiness premise |
| Generic interpretation naturality — **proved** | Lemma 17.1 | [`generic_interpretation_natural`](../theories/classicism/book/modal_semantics/interpretation/Bacon_Book_ZF_Generic_Interpretation_Existence.thy): moving a term's value by a counterpart map agrees with evaluating it at the future world under the moved assignment; term and assignment typing guards retained |
| Original-theory truth — **proved** | Proposition 18.6, truth step | `full_ZF_original_theory_satisfied`: satisfaction of the original theory when the root contains its universal closures |
| Fixed-ambient model existence — **proved** | Theorem 18.4, generalized existence construction | `book_coded_ambient_signature.book_full_C_ambient_modal_model_exists` and `book_full_C_ambient_nontrivial_modal_model_exists`: inclusion in a fixed ambient signature, infinite reserves dominating the entire declared union, and a total bounded term code injective on admitted terms suffice; the countable ambient locale supplies a retained instance |
| Original-signature model existence — **proved** | Theorem 18.4, countably declared signature instance | [`book_full_C_countable_modal_model_exists`](../theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Countable_Model_Existence.thy): actual model and admissible interpretation satisfying the entire consistent theory; open formulas and infinite premise sets allowed; arbitrary name carrier, countably many declared constants per type, no original spare-name requirement |
| Semantic signature pullback — **proved** | Auxiliary transport for the existence construction | `signature_pullback_model`, `signature_pullback_interpretation`: no injectivity or countability assumption on the constant map |
| Nontrivial original-signature model existence — **proved** | Strengthened forward instance of Theorem 18.4, retaining countably declared signatures | [`book_full_C_countable_nontrivial_modal_model_exists`](../theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Countable_Nontrivial_Existence.thy): same four input premises, but the constructed model also has inhabited domains and a false proposition at every world |
| All-true structural model and its exclusion — **proved** | Audit regression for the omitted nontriviality condition | [`probe_inconsistent_theory_has_model`, `probe_not_nontrivial`](../theories/classicism/book/modal_semantics/regressions/Bacon_Book_ZF_Singleton_Regression.thy): the structural predicate does not imply consistency; the strengthened class excludes this example |
| Truth clauses and naturality — **proved** | Definitions 17.13, 18.1–18.2; Lemma 17.1 | [`truth_imp`, `truth_all`, `truth_bottom`](../theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Modal_Truth_Clauses.thy), [`truth_iff`, `truth_all_predicate`](../theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Modal_Identity_Clauses.thy), [`denote_natural`, `denote_coincidence`](../theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Modal_Naturality.thy): implication uses the documented future-restricted complement; quantification ranges over the current domain |
| Leibniz identity and box clauses — **proved** | Definition 18.1(3.5) equality operation; the p.392 `□⊤` presentation; Exercise 18.1 | [`truth_leibniz`, `truth_box`](../theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Modal_Identity_Clauses.thy): `A =σ B` is true at w iff the values are equal, the model's own equality operation separating them; the literal `λp.(p =ₜ ⊤)` is true iff the operand holds at every accessible world under the moved assignment; no false-proposition premise |
| βη-step invariance — **proved** | Definitions 17.9–17.11 | [`denote_subst`, `denote_beta_step`, `denote_eta_step`](../theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Modal_Conversion.thy): value-preserving at every type, world and typed assignment, in every context, under the calculus's free-for guard |
| H worldwise soundness — **proved** | Chapter 5 calculus over Chapter 17–18 models | [`H_valid_at`, `theory_derivable_valid_at`](../theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Modal_H_Soundness.thy): every H theorem is valid at every world; theory derivations preserve validity at a fixed world |
| Generic full-C soundness — **proved** | Theorem 18.4, soundness direction; Chapter 8 endnote 5 | [`full_C_valid_everywhere`, `full_C_theory_valid_at_root`, `satisfiable_theory_consistent`](../theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Full_C_Soundness.thy): every full-C theorem is valid at every world of every nontrivial model under every admissible interpretation; theory derivations are valid at the root when the premises are satisfied there |
| Full-C modal completeness — **proved** | Theorem 18.4, p.398; cardinal generalization of its displayed countable construction | [`book_full_C_theory_derivable_iff_consequence`, `book_full_C_theory_consistent_iff_satisfiable`](../theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Full_C_Completeness.thy) retain countably declared signatures on arbitrary carriers; [`book_full_C_theory_derivable_iff_consequence_small_carrier`, `book_full_C_theory_consistent_iff_satisfiable_small_carrier`](../theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Full_C_Small_Carrier_Completeness.thy) allow every name of a ZF-small carrier to be declared, including `nat set`; [`book_full_C_theory_derivable_iff_consequence_small_declared`, `book_full_C_theory_consistent_iff_satisfiable_small_declared`, `…_ZF_carrier`](../theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Full_C_Declared_Names_Completeness.thy) need only a ZF-bounded declared-name union on an arbitrary carrier and subsume both. All concern rich stock, full simple types, the minimal language, open formulas and arbitrary premise sets, root consequence and the explicit nontrivial model class. The cardinal reserve invariant, the smallness premises and the bounded term code are formalization additions, not printed source clauses |
| Cardinal name reserves — **proved** | Generalisation of the unused-name reserve preceding Definition 18.8 (pp.398–400) | [`book_ambient_signature.book_ambient_henkin_signature_ambient`](../theories/classicism/book/Bacon_Book_Ambient_Signature.thy): reserves that are infinite and at least as large as the declared signature reproduce themselves along the Henkin extension; the cardinal invariant is ours, the book's displayed construction is countable |
| Nontrivial original-signature model existence for small carriers — **proved** | Cardinal generalization of the construction for Theorem 18.4, pp.398–401 | [`book_full_C_small_carrier_nontrivial_modal_model_exists`](../theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Small_Carrier_Existence.thy): rich stock, well-formed full-minimal premises, full-C consistency, and a total name-carrier injection into the elements of an actual ZF set; all constants may be declared; open formulas and arbitrary premise sets allowed; countable types, `nat set` and powersets of ZF-small types are proved ZF-small; includes a `nat set` corollary |
| Nontrivial original-signature model existence for small declared names — **proved** | Cardinal generalization of the construction for Theorem 18.4, pp.398–401, on an arbitrary carrier | [`book_full_C_small_declared_nontrivial_modal_model_exists`](../theories/classicism/book/representation/hol_zf/Bacon_Book_ZF_Declared_Names_Existence.thy): rich stock, well-formed full-minimal premises, full-C consistency, and an injective code of the declared-name union into the elements of an actual ZF set; the carrier is arbitrary; `book_full_C_ZF_carrier_nontrivial_modal_model_exists` covers the type ZF with a set-bounded declared union; the countable and small-carrier theorems follow as `…_from_small_declared` corollaries |

The [nontriviality clarification](MODAL_NONTRIVIALITY.md) remains
essential. For the broad structural class, the reverse consistency
implication of Theorem 18.4 is false, not merely unproved. The nontrivial
class supports generic soundness and the declared-name-smallness
completeness and consistency characterizations above, with the earlier
scopes retained as special cases. The additional premise set is
required true at the root under every typed assignment; it is not
required true at every future world.

### What remains open for full-type C

| Obligation | Current boundary |
|---|---|
| Declared unions with no ZF-bounded injection | Signatures whose declared-name union admits no injection bounded by a ZF set are outside the construction and the general endpoint. This is a limitation of the injective syntax-coding method, not a claim that every theory in such a signature lacks a set-valued model; a broader existence/completeness theorem or a sharp impossibility result is not established |
| Separate structural-class soundness statement | H, identity, box and conversion clauses already hold under their structural interpretation guards; no separate general full-C soundness endpoint for the broad structural class is asserted here. A consistency characterization for that class is refuted by the singleton regression |
| General λ-sublanguages and richer primitive profiles | The modal endpoints concern the full minimal language; these broader source formulations are not covered |
| Remaining source correspondence | The explicit nontrivial refinement, future-restricted implication, literal identity-with-top box, and deferred source-fidelity obligations remain visible |

The completed H and paper-R results retain their separately stated scopes.
These modal results do not certify the deferred source-fidelity corpus.

### What the numbered modal-model results say

**The full-type convention on p.160 and in p.178 endnote 5 distinguishes this
C from the older base.** Its principles include Modalized Functionality at
every function type, as well as Propositional Equivalence. The former relates
identity of operators to their necessary agreement on arguments; the latter
licenses propositional identity from proved propositional equivalence. The
independent `book_full_C_proves` presentation includes these requirements
explicitly. Merely reusing the earlier full-F syntax does not add them.

**Definition 17.13 specifies interpretation in a concrete modalized
applicative structure.** At a world w, variables receive their assigned
values and constants receive the counterparts of their root denotations.
Application uses the function's value at the current world and argument.
An abstraction denotes a function on all accessible future world–argument
pairs: move the assignment to the future world, assign the argument to the
bound variable, and evaluate the body. The important existence obligation
is that this entire function belongs to the chosen domain. Both the canonical
case and generic existence for the independent full-minimal modal-model class
are now verified.

**Theorem 17.1 guarantees that interpreting terms does not leave the
structure.** Bacon states both totality on well-typed terms and closure for
the associated iterated future-abstraction operations. Our generic result
establishes its interpretation-existence component in full-minimal modal
models: K/S abstraction elimination supplies a typed value and proves that
it is exactly the required future function graph. The checked construction
does not assume a canonical model or replace restricted domains by full
function spaces. This entry does not claim the theorem's entire broader
general-signature formulation.

**Lemma 17.1 states naturality of interpretation.** Interpreting a term and
then moving its value to an accessible world gives the same result as first
moving the assignment and interpreting the term there. The generic
construction proves this equality with explicit world, language and typed
assignment conditions. Counterpart maps need not be injective.

**Definition 18.1 specifies a modal model for Classicism.** It comprises a
pointed frame, a domain at every type and world, counterpart maps, and
interpretations of the nonlogical constants. Propositions are subsets of
the relevant future cone. Higher-order objects are suitably natural
functions on future world–argument pairs; their domains may be proper
subsets of the corresponding function spaces. The domains must contain the
prescribed combinators, implication, quantifiers, and identity operations.
This is an independent model definition, not a predicate saying that the
model validates C. The implementation explicitly documents its
future-restricted reading of the printed implication clause.

**Proposition 18.5 certifies the canonical construction as a modal model.**
Constructing domains and counterpart maps is not enough: the prescribed
logical and combinatory operations must actually belong to those domains.
The proof identifies them with the represented values of the appropriate
closed terms and verifies their complete future behavior. The Isabelle
endpoint discharges every field of the independent model predicate; it
does not assume the very modelhood claim it is meant to establish.

**Proposition 18.6 is the truth step for the original theory.** The canonical
model makes the formulas of the starting theory true. For closed sentences,
the argument connects membership in a canonical world with membership of
that world in the sentence's represented proposition. The checked
original-theory result also handles open premises by using their universal
closures at the root and then recovering truth under every typed assignment.
The separate existence theorem constructs the required root rather than
silently dropping this containment premise.

**Theorem 18.4 is the book's modal soundness and completeness claim.**
It is stated without a signature-cardinality qualification on p.398; its
displayed canonical proof starts with a countable signature. This
formalization extends that construction to signatures whose declared-name
union admits an injective code into the elements of an actual ZF set, on
an otherwise arbitrary HOL name carrier. The declared-name smallness
premise and the internal cardinal reserve and bounded-code interfaces are
formalization additions, not printed hypotheses of the theorem.
Original-signature nontrivial model existence, derivability iff root
consequence, and consistency iff satisfiability are established in this
scope. The countably declared and whole-carrier-smallness results remain
available as special cases. Generic soundness has no signature-cardinality
restriction. The full minimal language, rich stock, HOL–ZF foundation,
explicit nontrivial class, root satisfaction under every typed assignment,
future-restricted implication and literal box convention remain as
documented; the broader language/profile variants are not covered.

## Reading the entries correctly

The theorem names above are searchable short names; model-local theorems also
carry their surrounding locale's assumptions. Follow the linked theory, then
inspect its `fixes`, `assumes`, `shows`, and enclosing `context`.
The [reading guide](READING_GUIDE.md), [notation guide](NOTATION.md), and
[native graph](KNOWLEDGE_GRAPH.md) provide further orientation.

Do not discard signature restrictions, richness, closedness, carrier bounds,
adequacy, or model premises when presenting a result. Kernel verification
establishes the encoded theorem, not historical source fidelity by itself.

The book modal development's implication is explicitly future-restricted:
`(W↑v ∖ p) ∪ q`. This and the universal-closure treatment of open premises are
documented source-review points, not claims that every printed clause has
been transcribed literally.
