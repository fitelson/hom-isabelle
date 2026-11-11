# Lettie's refutation of Purity of Pure: hand proof and Isabelle correspondence

**The result.** Over H + PE, ten ordinary premises refute Purity of Pure at type
u = t→t: W ⊢ ¬PPᵤ. The theorem and its proof are due to Jacob Lettie, working with the
Purity of Pure team, a group of Claude Opus 5.5 sessions (*If a Proposition Is
Fundamental, Purity Is Not Pure* and *Weaker Theories That Still Refute Purity of Pure*,
9 November 2026). They are included here with Lettie's permission. His notes and his
Metamath file are not included in this repository.

**Hand proof.** [`reports/LETTIE_PP_REFUTATION_HAND_PROOF_2026-11-11.pdf`](../reports/LETTIE_PP_REFUTATION_HAND_PROOF_2026-11-11.pdf)
(LaTeX source beside it): a self-contained proof written for this repository in
Goodman's notation, following Lettie's proof of No Universal Proposition. The
explanatory revision starts with the reduction from fundamentality to universality,
motivates the operators, and separates the base-logical argument from the use of
the purity premises. Its appendix maps Lemmas A–G to their Isabelle theorems.
The original TeX and PDF are preserved in
[`reports/archive/2026-11-11_pre_explanatory_revision/`](../reports/archive/2026-11-11_pre_explanatory_revision/README.md).
The definitions, finite premises and formalization are unchanged.

**Isabelle.** [`theories/lettie_pp/`](../theories/lettie_pp/): Lettie's theories,
byte-identical to his distributed files, in their own sessions `PoP_Main`, `PoP_W`,
`PoP_NUP`, `PoP_SYN`, `PoP_K6`, `PoP_PSI` and `PoP_PPT`. The audit session
`Goodman_Integration_Lettie_Audit` exports their principal statements and fails the
build if any depends on an oracle; see [verification](../verification/README.md).

## The consequence relation

`w_not_pp` is a closed theorem of `U_proves` (defined in
`theories/lettie_pp/t/PoP_G100_Kernel.thy`): H, the Rule of Equivalence at type t,
modus ponens, Generalization and Instantiation. `U_proves` has no rule for added
premises. The ten premises are antecedents of the theorem, so no step can necessitate a
premise or apply Equivalence to a consequence of one. This is the reading of the added
principles as ordinary premises over the base logic, as in Bacon's formulation of the
question. `w_not_pp_C` is the same statement in the application's `⊢CEV`.

## Definitions

| Hand proof | Isabelle (`PoP_G100_Kernel`) |
|---|---|
| π = Pureᵤ | `rc_p` = `pp_Pure rc_u`, with `rc_u` = Prop → Prop |
| R(x,y), Uni(x) | `rcR`, `rcUni`; ∃x Uni(x) is `rcExUni` |
| F(z) = □(¬R(z,¬z) ∧ ¬R(¬z,z)) | `rcF` (conjunctive form, as in the hand proof) |
| Q, P, P′ | `rcQ`, `rcP`, `rcPp` |
| M, M′, M″ | `rc_P`, `rc_Pp`, `rc_W` (closed logical terms abstracting π) |
| App(σ,τ) | `pp_application_closure` (from the application's `Bacon_PP_Question`) |
| Pure_σ(t) | `pp_pure` |
| Exhaustion₀ at a | `zI a` = Pure_t(a) → (a → □a) |
| PPᵤ | `pp_pure (rc_u →ₒ Prop) rc_p` |

## Results

| Hand proof | Statement | Isabelle theorem | Theory |
|---|---|---|---|
| Lemma A | F(x) → □F(x) | `nup_lemA` | `PoP_G100_NUP` |
| Lemma B | F(x) → Q(x) = x | `nup_lemB` | `PoP_G100_NUP` |
| Lemma C | F(¬x) = F(x) | `nup_lemC` | `PoP_G100_NUP` |
| Lemma C, second part | P′(z) = P(¬z) | `nup_ident` | `PoP_G100_NUP` |
| Lemma D | ¬Q(x) → F(Q(x)) | `nup_lemD` | `PoP_G100_NUP` |
| Lemma E | □¬P(Q(x)) | `nup_cor` | `PoP_G100_NUP` |
| Lemma F | □π(P) ∧ □π(P′) → F(Q(x)) | `nup_step2` | `PoP_G100_NUP` |
| Lemma G | PPᵤ and W1–W9 give □π(P), □π(P′), ∀x F(Q(x)) and ∀Y(π(Y) → π(Y∘Q)) | `nup_step3` | `PoP_G100_NUP` |
| Final argument, Section 6 | ∀x F(Q(x)) and ∀Y(π(Y) → π(Y∘Q)) give ¬∃x Uni(x) | `nup_step4` | `PoP_G100_NUP` |
| No Universal Proposition | PPᵤ and W1–W9 give ¬∃x Uni(x) | `nup_NUP_U`, `u_S` | `PoP_G100_NUP`, `PoP_G100_Kernel` |
| **Theorem** | W ⊢ ¬PPᵤ | **`w_not_pp`** (in `⊢CEV`: `w_not_pp_C`) | `PoP_G100_W_Not_PP` |
| Proposition, Section 1; its existential consequence W10 | Logical Purity of λW.λz.¬W(z), App(u,u) and unary Recombination give Fun(r) → Uni(r); with ∃r Fun(r), they give ∃x Uni(x) | `u_uni_ctx`, `u_fun_ExUni` | `PoP_G100_Kernel` |

Lettie's further theorems, not restated in the hand proof:

| Statement | Isabelle theorem |
|---|---|
| Bacon's theory with a fundamental proposition (C with Logical Purity, Application, ∃r Fun(r), Recombination and Exhaustion, as ordinary premises) proves ¬PPᵤ | `cfp2` (and the finite form `cfp2_thm`) |
| That theory is consistent, as ordinary premises and as an axiom extension | `k6`, `k6_plus` |
| It refutes PP at every type built from t alone other than t | `k7_HT1` |
| It proves zeroary Exhaustion from a finite list | `cfp6` |
| Its extension by PP at type t is consistent | `ppt_k6` |
| The variants of §5 and §7 of *Weaker Theories* | `syn_S`, `syn_Psi` |

## Differences between the texts

- Lettie's main note and his Metamath certificate write F(z) as □¬(R(z,¬z) ∨ R(¬z,z)).
  The Isabelle theories, and the hand proof, use □(¬R(z,¬z) ∧ ¬R(¬z,z)). The two
  propositions are identical by PE; the operators F, and so M, M′ and M″, are different
  terms, and the premises W1–W3 mention those terms.
- The Isabelle lemmas are stated for a typed proposition x in an arbitrary context, in de
  Bruijn syntax; the hand proof's free x corresponds to that parameter.
- Lemma G is stated in Isabelle as one implication from the conjunction `rcS` (PPᵤ and
  the nine purity premises) to the conjunction of its four conclusions.

## Scope

- This settles Goodman's question in its full-QLN reading, with the added principles as
  ordinary premises: they are inconsistent with PPᵤ and a fundamental proposition.
- Exhaustion is used only through W8–W9. Whether PPᵤ is refuted with unary Recombination
  and a fundamental proposition but no Exhaustion (and no Persistence), as ordinary
  premises, is **open**.
- Purity of Fun, Modalized Functionality, uniqueness of the fundamental proposition and
  higher-arity QLN are not used.
