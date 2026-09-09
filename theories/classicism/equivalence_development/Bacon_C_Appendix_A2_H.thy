theory Bacon_C_Appendix_A2_H
  imports Bacon_C_Appendix_A2_Existence Bacon_C_Appendix_A2_Gen Bacon_C_Appendix_A2_Inst
begin

section \<open>Appendix A.2 for every theorem of the represented H calculus\<close>

text \<open>
  If H proves A in the context of v̄ together with Γ, then
  ⊢C (λv̄.A) = (λv̄.⊤₀).
  Source: the H axiom and rule cases of Bacon--Dorr Proposition A.2,
  pp.65–67.  The target H_proves presentation additionally exposes the
  IndividualExistence constructor, treated by the preceding leaf.

  Isabelle representation.  The auxiliary induction keeps the equation
  Ω = Δ @ Γ explicit.  At Gen and Inst, its recursive call uses
  σ # Ω = (σ # Δ) @ Γ, so the induction hypothesis abstracts the fresh
  quantified variable as well as the original prefix.
  Status.  All H_proves constructors are covered.  This is not yet the
  theorem for arbitrary C derivations: the additional C identity-axiom
  cases still have to be included in that separate induction.
\<close>

lemma C_A2_H_vector_truth_aux:
  assumes derivation: "\<Omega> \<turnstile>\<^sub>H A"
  shows "\<Omega> = \<Delta> @ \<Gamma> \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
      (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> ObjTrue)"
  using derivation
proof (induction arbitrary: \<Delta> \<Gamma> rule: H_proves.induct)
  case (PC \<Omega> A)
  have tautology: "prop_tautology (\<Delta> @ \<Gamma>) A" using PC.hyps by (simp only: PC.prems)
  show ?case by (rule C_PC_vector_abstraction[OF tautology])
next
  case (IndividualExistence \<Omega>)
  show ?case by (rule C_A2_individual_existence_vector_truth)
next
  case (UI \<sigma> \<Omega> A T)
  have A: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> A : Prop" using UI.hyps(1) by (simp only: UI.prems)
  have T: "\<Delta> @ \<Gamma> \<turnstile> T : \<sigma>" using UI.hyps(2) by (simp only: UI.prems)
  show ?case by (rule C_A2_UI_vector_truth[OF A T])
next
  case (EG \<sigma> \<Omega> A T)
  have A: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> A : Prop" using EG.hyps(1) by (simp only: EG.prems)
  have T: "\<Delta> @ \<Gamma> \<turnstile> T : \<sigma>" using EG.hyps(2) by (simp only: EG.prems)
  show ?case by (rule C_A2_EG_vector_truth[OF A T])
next
  case (Ref \<Omega> M \<sigma>)
  have M: "\<Delta> @ \<Gamma> \<turnstile> M : \<sigma>" using Ref.hyps by (simp only: Ref.prems)
  show ?case by (rule C_A2_Ref_vector_truth[OF M])
next
  case (LL \<Omega> A \<sigma> B F)
  have A: "\<Delta> @ \<Gamma> \<turnstile> A : \<sigma>" using LL.hyps(1) by (simp only: LL.prems)
  have B: "\<Delta> @ \<Gamma> \<turnstile> B : \<sigma>" using LL.hyps(2) by (simp only: LL.prems)
  have F: "\<Delta> @ \<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop" using LL.hyps(3) by (simp only: LL.prems)
  show ?case by (rule C_A2_LL_vector_truth[OF A B F])
next
  case (Beta \<Omega> A B)
  have A: "\<Delta> @ \<Gamma> \<turnstile> A : Prop" using Beta.hyps(1) by (simp only: Beta.prems)
  have B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop" using Beta.hyps(2) by (simp only: Beta.prems)
  show ?case by (rule C_A2_beta_axiom_vector_truth[OF A B Beta.hyps(3)])
next
  case (Eta \<Omega> A B)
  have A: "\<Delta> @ \<Gamma> \<turnstile> A : Prop" using Eta.hyps(1) by (simp only: Eta.prems)
  have B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop" using Eta.hyps(2) by (simp only: Eta.prems)
  show ?case by (rule C_A2_eta_axiom_vector_truth[OF A B Eta.hyps(3)])
next
  case (MP \<Omega> A B)
  have A_truth: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> ObjTrue)"
    by (rule MP.IH(1)[OF MP.prems])
  have implication_truth: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp A B)) (C_abstract_prefix \<Delta> ObjTrue)"
    by (rule MP.IH(2)[OF MP.prems])
  show ?case by (rule C_A2_MP_vector[OF A_truth implication_truth])
next
  case (Gen \<Omega> P \<sigma> Q)
  have extended: "\<sigma> # \<Omega> = (\<sigma> # \<Delta>) @ \<Gamma>" using Gen.prems by simp
  have premise_identity: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev (\<sigma> # \<Delta>)) Prop)
    (C_abstract_prefix (\<sigma> # \<Delta>) (Imp (shift P) Q))
    (C_abstract_prefix (\<sigma> # \<Delta>) ObjTrue)"
    by (rule Gen.IH[OF extended])
  show ?case by (rule C_A2_Gen_vector[OF premise_identity])
next
  case (Inst \<sigma> \<Omega> P Q)
  have P: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> P : Prop" using Inst.hyps(1) by (simp only: Inst.prems)
  have Q: "\<Delta> @ \<Gamma> \<turnstile> Q : Prop" using Inst.hyps(2) by (simp only: Inst.prems)
  have extended: "\<sigma> # \<Omega> = (\<sigma> # \<Delta>) @ \<Gamma>" using Inst.prems by simp
  have premise_identity: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev (\<sigma> # \<Delta>)) Prop)
    (C_abstract_prefix (\<sigma> # \<Delta>) (Imp P (shift Q)))
    (C_abstract_prefix (\<sigma> # \<Delta>) ObjTrue)"
    by (rule Inst.IH[OF extended])
  show ?case by (rule C_A2_Inst_vector[OF P Q premise_identity])
qed

theorem C_A2_H_vector_truth:
  assumes derivation: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>H A"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> ObjTrue)"
  by (rule C_A2_H_vector_truth_aux[OF derivation]) (rule refl)

corollary C_A2_H_zeroary_truth:
  assumes derivation: "\<Gamma> \<turnstile>\<^sub>H A"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop A ObjTrue"
proof -
  have premise: "[] @ \<Gamma> \<turnstile>\<^sub>H A" using derivation by simp
  show ?thesis using C_A2_H_vector_truth[OF premise] by simp
qed

end
