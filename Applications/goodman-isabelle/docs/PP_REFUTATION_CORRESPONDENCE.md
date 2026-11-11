# Purity of Pure and Recombination: note ↔ Isabelle correspondence

**Hand proof.** `reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex` (typeset:
`reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.pdf`), "Purity of Pure and
Recombination", 11 November 2026.
SHA-256 of the `.tex`:
`feae0c1547ce942343cc63791bcc39b829c20d2336f805b16f87b495f6d433fe`.
The Isabelle development was aligned with exactly this text.

**Isabelle development.** `theories/pp_refutation/`, five sessions in the note's order:

| Session | Directory | Theories |
|---|---|---|
| `Goodman_Integration_PP_Refutation_Kit` | `theories/pp_refutation/kit` | `Goodman_PP_Refutation_Kit` (technical) |
| `Goodman_Integration_PP_Refutation_Logic` | `theories/pp_refutation/logic` | `Goodman_PP_Refutation_Objects_Logic` (technical), `Goodman_PP_Refutation_Lemma1`, `…_Lemma2`, `…_Lemma3` |
| `Goodman_Integration_PP_Refutation_Stages` | `theories/pp_refutation/stages` | `Goodman_PP_Refutation_Objects_Stage`, `…_Objects_Induction` (technical), `…_Lemma4`, `…_Objects_Lemma5` (technical), `…_Lemma5`, `…_Lemma6` |
| `Goodman_Integration_PP_Refutation_Theorem1` | `theories/pp_refutation/theorem1` | `Goodman_PP_Refutation_Objects_Theorem1` (technical), `Goodman_PP_Refutation_Theorem1` |
| `Goodman_Integration_PP_Refutation_Packaging` | `theories/pp_refutation/packaging` | `Goodman_PP_Refutation_Packaging` (beyond the note), `Goodman_PP_Refutation_Audit` |

In the tables below theory names are abbreviated by dropping the prefix
`Goodman_PP_Refutation_`.

**Coverage.** Definitions (1)–(3), (12), (13), (R); Lemmas 1–6 with every numbered
formula (4)–(11), (14)–(16); Theorem 1 with its two consequences. The repository
packaging is listed separately at the end; it is not part of the note.

**What the build certifies.** The audit theory fails the build unless all 78 listed
endpoints (66 of the note, 12 packaging) are free of oracles, residual hypotheses and
flex-flex pairs. Retained certificate and exact printed statements:
`verification/audits/Goodman_Integration_PP_Refutation_Packaging.Goodman_PP_Refutation_Audit/`
(`pp-refutation-audit.txt`, `pp-refutation-statements.txt`). The first check was made
with Isabelle2025-2 (see `verification/README.md`). The build certifies the Isabelle
statements; that they render the note's statements is what this document records, and
passing the build is not by itself a source-fidelity audit.

## How to read a statement

Every theorem has the form `Γ ; T ⊢CEV⁺ A` for an arbitrary typing context `Γ`, with the
note's free variables as arbitrary well-typed terms (`Γ ⊢ Y : gr_u`, `Γ ⊢ p : Prop`, …).
The stock column says which added axioms the proof may use:

| Stock | Hypothesis in Isabelle | Note |
|---|---|---|
| none | no hypothesis on `T` (holds for `T = {}`) | "logical theorem", "logic alone" |
| T₀ | `gr_T0 ⊆ T` | Purity schema and Application closure |
| 𝒯 | `gr_Th ⊆ T` | T₀ + (PP_u) |

`gr_T0 = pp_purity_schema ∪ pp_application_closure_schema`,
`gr_Th = gr_T0 ∪ {pp_target_PP}` (theory `Objects_Stage`, where the correspondence with
the note's 𝒯 is stated once). Classicism is the base calculus. `gr_Th` is equal to the
application's `pp_T6_core_PP_axioms` (`gr_Th_eq_T6_core`).

## Objects

| Note | Isabelle | Theory |
|---|---|---|
| u = t→t; type u→t of properties | `gr_u`; `gr_cls` | `Kit` |
| □A = (A = ⊤); V ⊆ W | `ObjBox A` (core); `gr_sub V W` | `Objects_Logic` |
| (1) Σ | `gr_Sigma`; (ΣY)p is `App (App gr_Sigma Y) p`; β-body `gr_sg Y p` (`gr_Sigma_app`) | `Objects_Logic` |
| (2) Pre(W) = □(ΣW ⊆ W) | `gr_Pre W` | `Objects_Logic` |
| (3) L | `gr_L` (β: `gr_L_app`; instantiation: `gr_Lbody_E`) | `Objects_Logic` |
| g = λp.(p & Lp); q = g r | `gr_g`; `gr_q r` (= r & Lr) | `Objects_Logic` |
| "expands to a closed logical term" | `gr_Sigma_logical`, `gr_L_logical`, `gr_g_logical`, `gr_M_logical`, `gr_Dplus_logical`, `gr_Dminus_logical` | objects theories |
| T₀, 𝒯, (PP_u) | `gr_T0`, `gr_Th`; `gr_T0_purity`, `gr_T0_application`, `gr_Th_PP` | `Objects_Stage` |
| K⊥ | `gr_Kbot` (`gr_Kbot_app`: K⊥p ↔ ⊥) | `Objects_Stage` |
| closure conditions 1, 2, 3; Cl(𝒵) | `gr_Cl1 Z`, `gr_Cl2 c Z`, `gr_Cl3 c Z`; `gr_Cl gr_Pure Z` | `Objects_Stage` |
| Cl_c (proof of Lemma 6) | `gr_Cl c` | `Objects_Stage` |
| (12) Stage(Y) | `gr_Stage gr_Pure Y`; the property Stage: `gr_StageP gr_Pure` | `Objects_Stage` |
| (13) P | `gr_P` (β: `gr_P_app`) | `Objects_Stage` |
| M | `gr_M` | `Objects_Stage` |
| conditions 1–3 on Ψ; 𝒲 | `gr_Ind1 Ψ`, `gr_Ind2 gr_Pure Ψ`, `gr_Ind3 gr_Pure Ψ`; `gr_W gr_Pure Ψ` | `Objects_Induction` |
| λY.∀p(Y(¬p) ↔ Yp); Ψ of (15) | `gr_Sym`; `gr_PredProp gr_Pure p` | `Objects_Lemma5` |
| (R) | `gr_R gr_Pure r` (instantiation: `gr_R_E`); ∀p Xp is `gr_AllP X` | `Objects_Theorem1` |
| D₊, D₋ | `gr_Dplus`, `gr_Dminus` | `Objects_Theorem1` |
| X₊, X₋ | `gr_Xplus Y0`, `gr_Xminus Y0` (D₊Y₀ = X₊: `gr_Dplus_app_eq`; β: `gr_Xplus_app`) | `Objects_Theorem1` |
| K⊤ | `gr_Ktop` | `Objects_Theorem1` |
| fun′(r); ∃r fun′(r) | existing `pp_fun_prime r`; existing `pp_exists_fun_prime` | `Bacon_PP_T6_Encoding` |
| Fun(r); unary Recombination | existing `pp_fun Prop r`; existing `pp_unary_recombination` | `Bacon_PP_Question` |

## Numbered results

| Item | Formula | Isabelle theorem | Theory | Stock |
|---|---|---|---|---|
| L1 (4) | (ΣY)(¬p) ↔ (ΣY)p | `gr_Lemma1_4` | `Lemma1` | none |
| L1 (5) | (ΣY)p → □((ΣY)p) | `gr_Lemma1_5` | `Lemma1` | none |
| L1 (6) | □(V ⊆ W) → □(ΣV ⊆ ΣW) | `gr_Lemma1_6` | `Lemma1` | none |
| L1 (7) | □(V ⊆ W) → (ΣV ⊆ ΣW) | `gr_Lemma1_7` (closure: `gr_Lemma1_7_closure`) | `Lemma1` | none |
| L2 (8) | Lp ↔ (ΣL)p | `gr_Lemma2_8` | `Lemma2` | none |
| L2 (9) | Lp → □(Lp) | `gr_Lemma2_9` | `Lemma2` | none |
| L2 (10) | L(¬p) ↔ Lp | `gr_Lemma2_10` | `Lemma2` | none |
| L2 (11) | Pre(W) → □(L ⊆ W) | `gr_Lemma2_11` | `Lemma2` | none |
| L2 | Pre(W) → L ⊆ W | `gr_Lemma2_inst` | `Lemma2` | none |
| L2 | ΣL ⊆ L; Pre(L) | `gr_Lemma2_SigmaL_sub_L`; `gr_Lemma2_Pre_L` | `Lemma2` | none |
| L2 | Pre(ΣL); L ⊆ ΣL | `gr_Lemma2_Pre_SigmaL`; `gr_Lemma2_L_sub_SigmaL` | `Lemma2` | none |
| L3 | ∀r((r & Lr) → L(r & Lr)) | `gr_Lemma3_closure` | `Lemma3` | none |
| L3 | Lq | `gr_Lemma3_Lq` | `Lemma3` | none |
| L3 | L(¬q); L(¬q) = ⊤ | `gr_Lemma3_Lnq`; `gr_Lemma3_Lnq_top` | `Lemma3` | none |
| L3 | g(¬q) = ¬q | `gr_Lemma3_g_neg_q` | `Lemma3` | none |
| L3 | g r = q | `gr_Lemma3_g_r` | `Lemma3` | none |
| L4 | K⊥ is a stage | `gr_Lemma4_Stage_Kbot` | `Lemma4` | T₀ |
| L4 | Stage(Y) → Stage(ΣY) | `gr_Lemma4_Stage_Sigma` | `Lemma4` | T₀ |
| L4 | union condition for Stage | `gr_Lemma4_Stage_union` | `Lemma4` | none |
| L4 | Stage is closed | `gr_Lemma4_Stage_closed` | `Lemma4` | T₀ |
| L4 | conditions 1–3 give Cl(𝒲) | `gr_Lemma4_Cl_W` | `Lemma4` | T₀ |
| L4 | induction: conditions 1–3 → (Stage(Y) → Ψ(Y)) | `gr_Lemma4_induction`; ∀Y form `gr_Lemma4_induction_forall` | `Lemma4` | T₀ |
| L5 (14) | Stage(Y) → ∀p(Y(¬p) ↔ Yp) | `gr_Lemma5_14` (instance: `gr_Lemma5_14_at`) | `Lemma5` | T₀ |
| L5 (15) | Stage(Y) → (Yp → ∃Y₀(Stage(Y₀) & ¬Y₀p & (ΣY₀)p)) | `gr_Lemma5_15` | `Lemma5` | T₀ |
| L6 | M(Pure_u) = P | `gr_Lemma6_M_Pure_eq_P` | `Lemma6` | none |
| L6 | Pure(M) | `gr_Lemma6_Pure_M` | `Lemma6` | 𝒯 (T₀ suffices) |
| L6 | Pure(P) | `gr_Lemma6_Pure_P` | `Lemma6` | 𝒯 |
| L6 | Y ⊆ P for every stage Y | `gr_Lemma6_Stage_sub_P` | `Lemma6` | none |
| L6 | Stage(P); Stage(ΣP) | `gr_Lemma6_Stage_P`; `gr_Lemma6_Stage_SigmaP` | `Lemma6` | 𝒯 |
| L6 (16) | ΣP ⊆ P | `gr_Lemma6_16` | `Lemma6` | 𝒯 |
| L6 | □(ΣP ⊆ P); Pre(P) | `gr_Lemma6_box_16`; `gr_Lemma6_Pre_P` | `Lemma6` | 𝒯 |
| L6 | L ⊆ P | `gr_Lemma6_L_sub_P` (instance: `gr_Lemma6_L_in_P`) | `Lemma6` | 𝒯 |
| Thm 1 | Pure(X₊), Pure(X₋) for pure Y₀ | `gr_Theorem1_Pure_Xplus`, `gr_Theorem1_Pure_Xminus` | `Theorem1` | T₀ |
| Thm 1 | Case 1; Case 2 (from (R), stage Y₀, ¬Y₀q and the boxed disjunct: ⊥) | `gr_Theorem1_case1`; `gr_Theorem1_case2`; both: `gr_Theorem1_cases` | `Theorem1` | T₀ |
| Thm 1 | 𝒯 ⊢ no r satisfies (R), i.e. ¬∃r.(R) | `gr_Theorem1_R` (open form `gr_Theorem1_R_at`) | `Theorem1` | 𝒯 |
| Thm 1 | fun′(r) → (R) | `gr_Theorem1_funp_R` | `Theorem1` | T₀ |
| Thm 1 | 𝒯 ⊢ ¬∃r fun′(r) | `gr_Theorem1_funp` (open form `gr_Theorem1_funp_at`) | `Theorem1` | 𝒯 |
| Thm 1 | Fun(r) → (R) | `gr_Theorem1_Fun_R` | `Theorem1` | `pp_unary_recombination ∈ T` |
| Thm 1 | 𝒯 + unary Recombination ⊢ ¬∃r Fun(r) | `gr_Theorem1_Fun` (open form `gr_Theorem1_Fun_at`) | `Theorem1` | 𝒯 and `pp_unary_recombination ∈ T` |

## Proof routes

Each theorem is preceded by the sentence of the note it formalizes, and its proof follows
that sentence. In particular: (6) is obtained by necessitating the universal closure of
(7), instantiating inside the box, then 4 and K; L ⊆ ΣL comes from (6) at V = ΣL, W = L
(giving Pre(ΣL)) and instantiation of (3); (9) from the necessitated biconditional (8),
(5) and K; Lemma 3 from q → Lq (by Lr = ⊤, q = r & ⊤ = r, substitution), necessitation of
its universal closure, boxed instantiation and weakening inside the box, then
g(¬q) = ¬q & L(¬q) = ¬q & ⊤ = ¬q; Lemma 4 through 𝒲 and instantiation of (12);
(14) with the converse by ¬s and double negation; (15) by induction on the property with
parameter p; Lemma 6 through M(Pure_u) = P, the union condition applied to P, successor
closure and Necessitation of (16); Theorem 1 through the predecessor Y₀ of q, the two
cases with X₊ and X₋, (R) instantiated at X± and then at ¬q, the identities g r = q and
g(¬q) = ¬q, double negation, and symmetry (14) for ¬Y₀(¬q); the fun′ consequence through
X = K⊤ from Xr = ⊤ = K⊤r, then Xp = ⊤, hence Xp; the Fun consequence through unary
Recombination. (R) is only ever the antecedent of an implication: boxes are obtained from
hypothesis-free equivalences (`gr_Theorem1_Xplus_r`, `gr_Theorem1_Xminus_r`) by
`grk_box_iff`, and nothing depending on (R) is necessitated.

## Unavoidable differences

1. **de Bruijn syntax.** Bound variables are indices; a free variable of the note is an
   arbitrary well-typed term in an arbitrary context, so "for every Y, p" is schematic.
   "Generalizing" is the calculus rule `Gen` applied in the extended context; "bound
   variables are chosen fresh" is `shift`.
2. **Primitive connectives.** ¬, &, ∨, → are primitive; A ↔ B is (A → B) & (B → A);
   ⊤ is `ObjTrue` (∀p(p → p)), ⊥ is `ObjFalse`; iterated & and ∨ associate to the right.
3. **Pre, Cl, Stage are meta-level abbreviations** (Isabelle functions from terms to
   formulas), as the note's "abbreviation". As a term of type u→t, Stage is
   `gr_StageP gr_Pure` = λY.Stage(Y), used for "Stage is closed".
4. **Class variables and properties** (𝒵, Ψ, 𝒲) are terms of type u→t; 𝒵(Y) is `App Z Y`.
5. **q is r & Lr**, the β-normal form of g r (the note writes q = r & Lr = gr); the
   identity g r = q is `gr_Lemma3_g_r`.
6. **Closure condition 2** is curried, Pure(Y) → (𝒵(Y) → 𝒵(ΣY)); condition 3 has the
   conjunctive antecedent of the displayed formula.
7. **Lemma 4's hypotheses** are object-language formulas (`gr_Ind1..3`) and its conclusion
   is stated for an arbitrary Y (and also with ∀Y).
8. **(15)** packages ∃Y₀(Stage(Y₀) & ¬Y₀p & (ΣY₀)p) as `gr_PredEx gr_Pure p`.
9. **P is defined by (13)**, exactly as in the note; M(Pure_u) = P is a proved identity
   (one β-step), and Pure(P) is transported along it by Leibniz's law.
10. **Necessitation** is `CEV_axiom_necessitation`, derived from the Rule of Equivalence
    as in the note. The calculus allows it for theorems with parameters in context; the
    note's detours through universal closures are followed all the same.
11. **Technical lemmas** (typing, shifting, substitution, β, tautology checking, quantifier
    monotonicity) live in `Kit` and the `Objects_*` theories, not in the lemma theories.
12. **fun′, Fun, unary Recombination** are the application's existing constants. Their
    shapes agree with the note's displayed formulas: `pp_fun_prime r` is
    ∀X∀Y((Pure(X) & Pure(Y)) → (Xr = Yr → X = Y)); `pp_unary_recombination` is
    ∀X∀r((Pure(X) & Fun(r)) → (□(Xr) → ∀p Xp)). No equivalence proof was needed.
    ¬∃r Fun(r) is `Neg (Exists Prop (pp_fun Prop (Var 0)))`.
13. **X₊, X₋ are λ-terms** as in the note; D₊Y₀ = X₊ and D₋Y₀ = X₋ are proved identities
    (one β-step) along which purity is transported, as for M(Pure_u) = P.
14. **"Suppose r satisfies (R)", "choose a stage"** are rendered as implications and as the
    calculus rule `Inst` (∃-elimination) in an extended context; "Xp = ⊤" is `□(Xp)`.

## Packaging (beyond the note)

Theory `Goodman_PP_Refutation_Packaging`. Not part of the hand proof.

| Statement | Isabelle theorem | Hypotheses |
|---|---|---|
| 𝒯 is the application's T6 PP core | `gr_Th_eq_T6_core`: `gr_Th = pp_T6_core_PP_axioms` | none |
| 𝒯 ⊆ the Recombination-with-PP stock | `gr_Th_sub_recombination` | none |
| `[] ; pp_T6_core_PP_axioms ⊢CEV⁺ Neg pp_exists_fun_prime` | `gr_T6_core_no_fun_prime` | none |
| `[] ; pp_recombination_PP_axioms ⊢CEV⁺ ObjFalse` | `gr_recombination_PP_refutation` | none |
| `[] ; pp_full_QLN_PP_axioms ⊢CEV⁺ ObjFalse` | `gr_full_QLN_PP_refutation` | none |
| the two consistency questions are false | `gr_recombination_question_negative`, `gr_full_QLN_question_negative` | none |
| `goodman_book_proves gb_signature G (gb_recombination_PP_axioms G) (book_bottom G)` | `gr_native_recombination_PP_refutation` | `sg_rich G` |
| `¬ goodman_book_consistent gb_signature G (gb_recombination_PP_axioms G)` | `gr_native_recombination_PP_inconsistent` | `sg_rich G` |
| the same two for `gb_zeroary_unary_QLN_PP_axioms G` | `gr_native_QLN_PP_refutation`, `gr_native_QLN_PP_inconsistent` | `sg_rich G` |
| `goodman_book_proves gb_signature G (gb_T6_core G) (book_not G (gb_exists_fun_prime G))` | `gr_native_T6_core_no_fun_prime` | `sg_rich G` |

The refutation of `pp_recombination_PP_axioms` uses Theorem 1 (third assertion) and only
the existence part of `pp_unique_fundamental Prop`. The native stock is literally
`gb_recombination_PP_axioms G`; the name map is chosen by `gi_goodman_names_satisfiable`
and does not occur in the statements.

## Provenance and stock-use checks

The audit theory also fails the build unless:

- no endpoint of the note depends on a theorem that refutes a stock outright (a theorem
  whose conclusion derives `ObjFalse` or `book_bottom` and none of whose premises is a
  derivation judgement, which is the shape of the T6 and M5 refutations of auxiliary
  stocks), and the packaging endpoints depend on no such theorem other than the
  packaging refutations themselves;
- the endpoints of Lemmas 1–3 do not depend on the rule `CEV_axiom_proves.Axiom`;
- the endpoints of Lemmas 4–5 do not depend on `gr_Th_PP`;
- `gr_Theorem1_R` and `gr_Theorem1_funp` depend on `gr_Th_PP` and on
  `CEV_axiom_necessitation` and not on unary Recombination.

The certificate lists the imported application-level theorems that the note endpoints
use.
