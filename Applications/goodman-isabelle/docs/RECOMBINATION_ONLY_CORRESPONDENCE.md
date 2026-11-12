# Recombination without Exhaustion: hand proof and Isabelle correspondence

Shortly after Jacob Lettie found his refutation of Purity of Pure at type u = t→t
([his result](LETTIE_PP_CORRESPONDENCE.md)), a strengthening was found that drops
Exhaustion. Logical Purity, Application and PPᵤ, as ordinary premises over H + PE, refute
the existence of a universal proposition outright. Since a fundamental proposition is
universal by unary Recombination, PPᵤ is refuted by Logical Purity, Application, unary
Recombination and a fundamental proposition: the Recombination-only reading of Goodman's
question. No Exhaustion, Persistence or Purity of Fun is used.

Status: checked in Isabelle (Isabelle2026, no oracles).

**Hand proof.** [`reports/RECOMBINATION_WITHOUT_EXHAUSTION_HAND_PROOF_2026-11-11.pdf`](../reports/RECOMBINATION_WITHOUT_EXHAUSTION_HAND_PROOF_2026-11-11.pdf)
(self-contained TeX alongside). It is written as an ordinary theorem-proof note and does
not mention the formalization. Its lemmas follow the Isabelle proof one for one, with the
same routes and the same premise instances (L1–L10, A1–A10 in §5 of the note). The tables
below map each one to its theorem.

**Isabelle.** Session `Goodman_Integration_Recombination_Only` in
[`theories/recombination_only/`](../theories/recombination_only/), on top of Lettie's
kernel `PoP_Main` (his files unchanged): `Goodman_RecOnly_Closure`,
`Goodman_RecOnly_Relative`, `Goodman_RecOnly_Final` and the audit theory
`Goodman_RecOnly_Audit`. The audit checks 31 endpoints for oracles, residual hypotheses
and flex-flex pairs and exports their statements to
`verification/audits/Goodman_Integration_Recombination_Only.Goodman_RecOnly_Audit/`.
Build: `./check_isabelle.sh --export` (serial, 60 seconds per session).

## Consequence relation

- Lettie's `U_proves` (H, the Rule of Equivalence at type t, MP, Gen, Inst) has no premise
  or assumption rule. Every added principle is an antecedent of an implication, so
  Equivalence, hence Necessitation, applies only to theorems of the base logic. No proof
  uses `CEV_axiom_proves` or `goodman_book_proves`.
- The set statements use the repository's `CEV_set_derivable` over C (Assumption, Theorem,
  Derive_MP only): ordinary premises.
- Necessitations in the proof: `ro_boxed` (□(a → Θa), Lemma 2), `ro_cor` (□¬P_b(Q_b x), Lemma 7),
  and K/4 steps on base theorems (`u_rc_K`, `U_modal_4`). All are of premise-free theorems.

## Main statements

| Note | Isabelle | Statement |
|---|---|---|
| Theorem 1, over H + PE | `ro_thm1_U` | `[] ⊢U Imp roLA (Imp (Pure_{u→t} π) (Neg ExUni))` |
| Theorem 1, over C, ordinary premises | `ro_thm1_CEVs` | `[] ; {PP_u} ∪ LP schema ∪ App schema ⊢CEV_s ¬ExUni` |
| Corollary (fundamental proposition exists) | `ro_cor_EF_U` | `[] ⊢U Imp roLA (Imp EF (Imp rcH5 ¬PP_u))` |
| Corollary, unique fundamental | `ro_cor_U` | same with `pp_unique_fundamental Prop` |
| Corollary, repository package | `ro_recombination_refutes_PP` | `[] ; pp_recombination_background_axioms ⊢CEV_s ¬PP_u` |
| (same) | `ro_recombination_PP_inconsistent` | `[] ; pp_recombination_PP_axioms ⊢CEV_s ⊥` |

`roLA` is 20 instances: Logical Purity at ⊤, ∧, m, Ŵ, Φ̂, P̂, P̂′, Q̂, Z := λaλYλx.(a ∧ Yx)
and composition; Application at (t,t→t), (t,t), (u,t), (u→t,u→u), (u,u), (u→t,u),
(u→t,t→u), (t,u), (t,u→u), (u,u→u). `rcH5` (Lettie's) is Logical Purity at the negator,
Application at (u,u) and unary Recombination. `ExUni` is Lettie's `rcExUni`,
∃r ∀y ∀Y (π(Y) → (Yy → ◇Yr)). `pp_recombination_background_axioms` is the repository's
stock package for the question (Logical Purity, Application, unique fundamental
proposition, no fundamentals at other types, zeroary and unary Recombination; no Exhaustion, no
Persistence, no Purity of Fun). Of these, the proof uses Logical Purity, Application,
unique fundamentality (for the existence of a fundamental proposition) and unary
Recombination.

## Item by item

| Note | Isabelle (theory) |
|---|---|
| §1 R, Uni, ∃r Uni(r); Rec₁; neg | `rcR`, `rcUni`, `rcExUni`; `pp_unary_recombination`; `k_C` |
| §1 Proposition (Lettie: fundamental propositions are universal) | `u_fun_step`, `u_uni_ctx`, `u_fun_ExUni` (Lettie's kernel, imported) |
| §2 base-logic laws: Necessitation, K-rule, T, 4, □(A↔B) → A=B | `U_nec`, `u_rc_K`, `U_modal_T`, `U_modal_4`, `u_rc_box_iff_eq` |
| §3 m, and, Cl (Cl1)–(Cl5), W, a; Ĉl, Ŵ | `ro_m`, `ro_and`, `roCl` (`roCl1`–`roCl5`), `roW`, `roa`; `ro_Cl`, `ro_W` (Goodman_RecOnly_Closure) |
| §3 elimination and introduction for W | `ro_W_elim`, `ro_W_intro` |
| Lemma 1 (W satisfies the closure conditions), condition by condition | `ro_ClW_1`–`ro_ClW_5`, `ro_ClW` |
| Lemma 2 (a → Θ(a) is a base theorem) | `ro_base`, `ro_boxed` |
| §4 R_b, C_b, F_b, Q_b, P_b, P′_b, κ, Φ | `roR`, `roC`, `roF`, `roQf`/`roQ`, `roP`, `roPp`, `rok`, `roPhi` (Goodman_RecOnly_Relative) |
| §4 R̂, F̂, Q̂, P̂, P̂′, Φ̂; elimination and introduction for R_b | `ro_R`, `ro_F`, `ro_Q`, `ro_P`, `ro_Pp`, `ro_Phi`; `roR_elim`, `roR_intro` |
| Lemma 3 (firmness persists) | `ro_lemA` |
| Lemma 4 (Q_b fixes firm propositions) | `ro_lemB` |
| Lemma 5 (symmetry) | `ro_lemC` (biconditional), `ro_ident` |
| Lemma 6 (¬Q_b(x) → F_b(Q_b(x))) | `ro_lemD` |
| Lemma 7 (the first test necessarily fails) | `ro_cor` |
| Lemma 8 (the guarded step) | `ro_guarded` |
| Lemma 9 (necessary purity under the guard suffices) | `ro_relative` |
| §5 Z, comp; L1–L10, A1–A10; LA | `ro_Z`, `ro_comp` (Goodman_RecOnly_Final); `roHC0`, `roHF`; `roLA` |
| §6 G, Pres | `ro_G`, `roPres` |
| Lemma 10 (the guard is pure and true): Cl(G) condition by condition; m(W); π(W); Pure_t(a) | `ro_ClG_1`–`ro_ClG_5`, `ro_ClG`; `ro_mW`; `ro_piW`; `ro_pure_a`; `ro_closure_true` (premises `roHC`, hypothesis `roH`) |
| Lemma 11 (Φ is pure and preserves pure truths) | `ro_Phi_pure`, `ro_Phi_pres` |
| Lemma 12 (properties of the guard) (a), (b), (c) | `ro_actual`, `ro_certificate`, `ro_Fa` |
| Lemma 13 (universality relative to the guard) | `ro_step1`, `ro_uni_rel` |
| Proof of Theorem 1: R_a(e, ¬e); contradiction; ¬∃r Uni(r) | `ro_step2`, `ro_Rae`; `ro_contra`; `ro_thm1` (premises `roPrem`) |
| Theorem 1 | `ro_thm1_U`; over C, `ro_thm1_CEVs` (via `ro_LA_derivable`, `U_sub_CEV`) |
| Corollary: EF, H5; a unique fundamental proposition gives EF | `k_EF`, `rcH5`; `lo_EF_of_UF` |
| Corollary | `ro_cor_EF_U`, `ro_cor_U`, `ro_cor_set`, `ro_recombination_refutes_PP`, `ro_recombination_PP_inconsistent` |

## Notes on the formalization

1. Lemmas 1, 2 and 10 are proved for an arbitrary closed term Θ (typed, invariant under
   substitution and renaming), with π the constant `Pure_u`. Lemma 2's a → Θ(a) is a
   premise-free theorem, so Necessitation applies to it directly.
2. The symmetry F_b(¬x) ↔ F_b(x) is proved as a biconditional (Lemma 5), as in Lettie's
   development; the identity P′_b(z) = P_b(¬z) then follows by Propositional Equivalence.
3. Theorem 1's premises over H + PE are 20 named instances rather than the schemas; the
   set version over C uses the full schemas (`ro_LA_derivable`). A1 (App at (t,t→t)) and A8
   (App at (t,u)) are the same formula, since u = t→t; it occurs once in `roHC0` and once in
   `roHF`, so there are nineteen distinct instances.
4. Condition (Cl1) is not needed for Lemma 2; it is the condition that accounts for premise
   L1 (in Lemma 10).
5. The theories state the closure and relativized lemmas for an arbitrary closed term T and
   arbitrary proposition terms b, x, z, as the note does in words.
