# Recombination without Exhaustion: hand proof and Isabelle correspondence

Shortly after Jacob Lettie found his refutation of Purity of Pure at type u = t→t
([his result](LETTIE_PP_CORRESPONDENCE.md)), a strengthening was found that drops
Exhaustion. Logical Purity, Application and PPᵤ, as ordinary premises over H + PE, refute
the existence of a universal proposition outright. Since a fundamental proposition is
universal by unary Recombination, PPᵤ is refuted by Logical Purity, Application, unary
Recombination and a fundamental proposition: the Recombination-only reading of Goodman's
question. No Exhaustion, Persistence or Purity of Fun is used.

Status: Isabelle-checked (Isabelle2026, no oracles), pending independent human review.

**Hand proof.** [`reports/RECOMBINATION_WITHOUT_EXHAUSTION_HAND_PROOF_2026-11-11.pdf`](../reports/RECOMBINATION_WITHOUT_EXHAUSTION_HAND_PROOF_2026-11-11.pdf)
(self-contained TeX alongside). Every numbered step names its Isabelle theorem, and every
use of Logical Purity or Application names its instance (Table 1 of the note).

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
- Necessitations in the proof: `ro_boxed` (□(a → Θa), Lemma 1), `ro_cor` (□¬P_b(Q_b x)),
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
proposition, no other fundamentals, zeroary and unary Recombination; no Exhaustion, no
Persistence, no Purity of Fun). Of these, the proof uses Logical Purity, Application,
unique fundamentality (for the existence of a fundamental proposition) and unary
Recombination.

## Item by item

| Note | Isabelle (theory) |
|---|---|
| §3 m, Ĉl, Cl, Ŵ, W, a, G, Pres | `ro_m`, `ro_Cl`, `roCl`, `ro_W`, `roW`, `roa`, `ro_G`, `roPres` (Goodman_RecOnly_Closure) |
| Lemma 1(a), clause by clause | `ro_ClW_1`–`ro_ClW_5`, `ro_ClW` |
| Lemma 1(b), (c) | `ro_base`, `ro_boxed` |
| Lemma 1(d1), clause by clause | `ro_ClG_1`–`ro_ClG_5`, `ro_ClG` |
| Lemma 1(d2)–(d4), (d) | `ro_mW`, `ro_piW`, `ro_pure_a`, `ro_closure_true` |
| §4 R̂, F̂, Q̂, P̂, P̂′, Φ̂ | `ro_R`, `ro_F`, `ro_Q`, `ro_P`, `ro_Pp`, `ro_Phi` (Goodman_RecOnly_Relative) |
| R_b, F_b, Q_b, Q_b(z), P_b, P′_b, C_b, κ, Φ | `roR`, `roF`, `roQf`, `roQ`, `roP`, `roPp`, `roC`, `rok`, `roPhi` |
| (2.1)–(2.7) | `ro_lemA`, `ro_lemB`, `ro_lemC`, `ro_ident`, `ro_lemD`, `ro_cor`, `ro_guarded` |
| Lemma 2 | `ro_relative` |
| §5 premises L5–L10, A6–A10; Prem | `roHF`; `roPrem` (Goodman_RecOnly_Final) |
| (5.1)–(5.5) | `ro_Phi_pure`, `ro_Phi_pres`, `ro_actual`, `ro_certificate`, `ro_Fa` |
| §6 Z, comp | `ro_Z`, `ro_comp` |
| (6.1)–(6.4) | `ro_step1`, `ro_uni_rel`, `ro_step2`, `ro_Rae`, `ro_contra`, `ro_thm1` |
| Theorem 1 | `ro_thm1_U`, `ro_thm1_CEVs` |
| §7 Proposition (Lettie: a fundamental proposition is universal) | `u_fun_step`, `u_uni_ctx`, `u_fun_ExUni` (Lettie's kernel, imported) |
| Corollary | `ro_cor_EF_U`, `ro_cor_U`, `ro_cor_set`, `ro_recombination_refutes_PP`, `ro_recombination_PP_inconsistent` |

## Notes on the formalization

1. Lemma 1 is proved for an arbitrary closed term Θ (typed, invariant under substitution
   and renaming), with π the constant `Pure_u`. Part (b) is a premise-free theorem, so
   Necessitation applies to it directly.
2. The symmetry F_b(¬x) = F_b(x) is proved as a biconditional (2.3), as in Lettie's
   development; the identity (2.4) then follows by Propositional Equivalence.
3. Theorem 1's premises over H + PE are 20 named instances rather than the schemas; the
   set version over C uses the full schemas (`ro_LA_derivable`).
4. Clause (Cl1) of the closure condition is not needed for a → Θa; it is the clause that
   accounts for premise L1.

## Not done

No independent human review yet.
