theory Bacon_C_Appendix_A2
  imports Bacon_C_Appendix_A2_H Bacon_C_Appendix_A2_Closed_Axioms
begin

section \<open>Appendix A.2 for the represented axiom-based calculus C\<close>

text \<open>
  If ⊢C A in the context of v̄ together with Γ, then
  ⊢C (λv̄.A) = (λv̄.⊤₀) in Γ.
  Source: Bacon–Dorr Proposition A.2, pp.65–67, combining the H
  constructor cases, closed Boolean and Classicist identity axioms,
  and preservation by MP, Gen, and Inst.

  Isabelle representation.  C_abstract_prefix Δ reverses the de Bruijn
  prefix before forming λv̄.  The auxiliary proof retains Ω = Δ @ Γ
  explicitly, and extends Δ to σ # Δ in both quantifier-rule cases.
  Thus the induction never assumes an abstraction rule for arbitrary open
  equations: each rule uses its separately established vector-identity
  preservation theorem.  Every C_proves constructor is covered.

  Scope.  This theorem is for the represented full F type grammar and
  string-named, unrestricted constant stock.  The datatype has primitive
  Imp and dedicated logical constructors; its Boolean axiom list includes
  the material-implication operation bridge, and the imported H presentation
  explicitly includes IndividualExistence.  These representation bridges
  remain qualifications on source correspondence, not additional assumptions
  of the theorem below.  No CE/CEV or semantic completeness premise is used.
  Appendix A.3 and equivalence of the represented calculi are separate
  corollaries to be assembled from this result.
\<close>

lemma C_A2_C_vector_truth_aux:
  assumes derivation: "\<Omega> \<turnstile>\<^sub>C A"
  shows "\<Omega> = \<Delta> @ \<Gamma> \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
      (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> ObjTrue)"
  using derivation
proof (induction arbitrary: \<Delta> \<Gamma> rule: C_proves.induct)
  case (H \<Omega> A)
  have theorem_H: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>H A" using H.hyps by (simp only: H.prems)
  show ?case by (rule C_A2_H_vector_truth[OF theorem_H])
next
  case (BooleanIdentity A \<Omega>)
  show ?case by (rule C_A2_BooleanIdentity_vector_truth[OF BooleanIdentity.hyps])
next
  case (IdentityIdentity \<Omega> \<sigma>)
  show ?case by (rule C_A2_IdentityIdentity_vector_truth)
next
  case (AbsorbDisjForall \<Omega> \<sigma>)
  show ?case by (rule C_A2_AbsorbDisjForall_vector_truth)
next
  case (DistDisjForall \<Omega> \<sigma>)
  show ?case by (rule C_A2_DistDisjForall_vector_truth)
next
  case (AbsorbConjExists \<Omega> \<sigma>)
  show ?case by (rule C_A2_AbsorbConjExists_vector_truth)
next
  case (DistConjExists \<Omega> \<sigma>)
  show ?case by (rule C_A2_DistConjExists_vector_truth)
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
    by (rule Gen.IH[where \<Delta>="\<sigma> # \<Delta>" and \<Gamma>=\<Gamma>, OF extended])
  show ?case by (rule C_A2_Gen_vector[OF premise_identity])
next
  case (Inst \<sigma> \<Omega> P Q)
  have P: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> P : Prop" using Inst.hyps(1) by (simp only: Inst.prems)
  have Q: "\<Delta> @ \<Gamma> \<turnstile> Q : Prop" using Inst.hyps(2) by (simp only: Inst.prems)
  have extended: "\<sigma> # \<Omega> = (\<sigma> # \<Delta>) @ \<Gamma>" using Inst.prems by simp
  have premise_identity: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev (\<sigma> # \<Delta>)) Prop)
    (C_abstract_prefix (\<sigma> # \<Delta>) (Imp P (shift Q)))
    (C_abstract_prefix (\<sigma> # \<Delta>) ObjTrue)"
    by (rule Inst.IH[where \<Delta>="\<sigma> # \<Delta>" and \<Gamma>=\<Gamma>, OF extended])
  show ?case by (rule C_A2_Inst_vector[OF P Q premise_identity])
qed

theorem C_Appendix_A2:
  assumes derivation: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>C A"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> ObjTrue)"
  by (rule C_A2_C_vector_truth_aux[OF derivation]) (rule refl)

lemmas C_A2_C_vector_truth = C_Appendix_A2

corollary C_Appendix_A2_zeroary:
  assumes derivation: "\<Gamma> \<turnstile>\<^sub>C A"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop A ObjTrue"
proof -
  have premise: "[] @ \<Gamma> \<turnstile>\<^sub>C A" using derivation by simp
  show ?thesis using C_Appendix_A2[OF premise] by simp
qed

end
