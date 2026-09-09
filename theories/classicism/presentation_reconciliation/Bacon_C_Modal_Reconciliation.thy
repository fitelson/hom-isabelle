theory Bacon_C_Modal_Reconciliation
  imports Bacon_C_Vector_Presentation "Bacon_Classicism.Bacon_S4"
begin

section \<open>Preserving the checked positive S4 derivations in C\<close>

text \<open>
  With □A := A =ₜ ⊤₀, the earlier modal development proves
  □(A → B) → (□A → □B), □A → A, and □A → □□A, and the rule
  from ⊢ A to ⊢ □A.  The established CEV-to-C presentation theorem
  now transfers those checked derivations into axiom-based C.

  Isabelle representation.  ObjBox, modal_K, modal_T, and modal_4 retain
  their existing definitions.  C_public_necessitation translates the C
  premise to CEV, applies CEV_necessitation, and translates back; the
  three axiom instances use CEV_proves_to_C directly.

  Status.  This preserves the positive S4 package with its exact typing
  premises.  It does not show that C's modal fragment is exactly S4, rule
  out stronger modal principles, or establish soundness/completeness for
  any model class.  The C-only Appendix A reconstruction is already complete
  before this adapter reuses the earlier CEV modal proofs.
\<close>

theorem C_public_necessitation:
  assumes derivation: "\<Gamma> \<turnstile>\<^sub>C A"
  shows "\<Gamma> \<turnstile>\<^sub>C \<box>\<^sub>o A"
  by (rule CEV_proves_to_C[OF CEV_necessitation[OF C_proves_to_CEV[OF derivation]]])

theorem C_public_modal_T:
  assumes A: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C modal_T A"
  by (rule CEV_proves_to_C[OF CEV_modal_T[OF A]])

theorem C_public_modal_K:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C modal_K A B"
  by (rule CEV_proves_to_C[OF CEV_modal_K[OF A B]])

theorem C_public_modal_4:
  assumes A: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C modal_4 A"
  by (rule CEV_proves_to_C[OF CEV_modal_4[OF A]])

end
