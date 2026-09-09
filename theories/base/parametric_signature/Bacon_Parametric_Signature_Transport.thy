theory Bacon_Parametric_Signature_Transport
  imports Bacon_Parametric_Proof_Substitution
begin

section \<open>Deleting a declaration by typed constant replacement\<close>

text \<open>
  Replacing c:σ by N:σ can move a proof from Σ to Ω when N ∈ ℒ(Ω)
  and Ω retains every other declared typed constant.  This strengthens the
  same-signature substitution theorem: the removed constant need not remain
  available in Ω.  It is the one-declaration step used in signature
  conservativity, not a semantic completeness argument.

  Isabelle representation: pH_proves_pconst_into replays every constructor
  with its target-signature guard.  Local and set consequences use the same
  map on their premises.  No old closed replacement term is assumed.
  Status: cross-signature proof transport only.
\<close>

lemma pconst_subst_signature_into:
  assumes source: "pterm_in_signature \<Sigma> M"
    and replacement: "pterm_in_signature \<Omega> N"
    and names: "\<And>d \<tau>. d \<in> \<Sigma> \<tau> \<Longrightarrow> d \<noteq> c \<or> \<tau> \<noteq> \<sigma> \<Longrightarrow> d \<in> \<Omega> \<tau>"
  shows "pterm_in_signature \<Omega> (pconst_subst c \<sigma> N M)"
  using source replacement
  by (induction M arbitrary: N) (auto simp: pshift_def intro: names split: if_splits)

lemma pH_proves_pconst_into:
  assumes d: "pH_proves \<Sigma> \<Gamma> A" and typed: "has_ptype \<Gamma> N \<sigma>"
    and sigN: "pterm_in_signature \<Omega> N"
    and names: "\<And>d \<tau>. d \<in> \<Sigma> \<tau> \<Longrightarrow> d \<noteq> c \<or> \<tau> \<noteq> \<sigma> \<Longrightarrow> d \<in> \<Omega> \<tau>"
  shows "pH_proves \<Omega> \<Gamma> (pconst_subst c \<sigma> N A)"
  using d typed sigN
proof (induction arbitrary: N rule: pH_proves.induct)
  case (PC \<Gamma> A)
  show ?case by (rule pH_proves.PC[OF pproof_taut_pconst[OF PC.hyps(1) PC.prems(1)] pconst_subst_signature_into[OF PC.hyps(2) PC.prems(2) names]])
next
  case (IndividualExistence \<Gamma>)
  show ?case by simp (rule pH_proves.IndividualExistence)
next
  case (UI \<rho> \<Gamma> A T)
  have nt: "has_ptype (\<rho> # \<Gamma>) (pshift N) \<sigma>" by (rule pshift_preserves_typing[OF UI.prems(1)])
  have ns: "pterm_in_signature \<Omega> (pshift N)" using UI.prems(2) by (simp add: pshift_def)
  show ?case by (simp only: pconst_subst.simps pproof_pconst_psubst0)
    (rule pH_proves.UI[OF pconst_subst_type[OF UI.hyps(1) nt] pconst_subst_type[OF UI.hyps(2) UI.prems(1)]
      pconst_subst_signature_into[OF UI.hyps(3) ns names] pconst_subst_signature_into[OF UI.hyps(4) UI.prems(2) names]])
next
  case (EG \<rho> \<Gamma> A T)
  have nt: "has_ptype (\<rho> # \<Gamma>) (pshift N) \<sigma>" by (rule pshift_preserves_typing[OF EG.prems(1)])
  have ns: "pterm_in_signature \<Omega> (pshift N)" using EG.prems(2) by (simp add: pshift_def)
  show ?case by (simp only: pconst_subst.simps pproof_pconst_psubst0)
    (rule pH_proves.EG[OF pconst_subst_type[OF EG.hyps(1) nt] pconst_subst_type[OF EG.hyps(2) EG.prems(1)]
      pconst_subst_signature_into[OF EG.hyps(3) ns names] pconst_subst_signature_into[OF EG.hyps(4) EG.prems(2) names]])
next
  case (Ref \<Gamma> M \<rho>)
  show ?case by simp (rule pH_proves.Ref[OF pconst_subst_type[OF Ref.hyps(1) Ref.prems(1)] pconst_subst_signature_into[OF Ref.hyps(2) Ref.prems(2) names]])
next
  case (LL \<Gamma> A \<rho> B F)
  show ?case by simp (rule pH_proves.LL[OF pconst_subst_type[OF LL.hyps(1) LL.prems(1)]
    pconst_subst_type[OF LL.hyps(2) LL.prems(1)] pconst_subst_type[OF LL.hyps(3) LL.prems(1)]
    pconst_subst_signature_into[OF LL.hyps(4) LL.prems(2) names] pconst_subst_signature_into[OF LL.hyps(5) LL.prems(2) names] pconst_subst_signature_into[OF LL.hyps(6) LL.prems(2) names]])
next
  case (Beta \<Gamma> A B)
  have step: "pcompatible_step pbeta_contract (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B)"
    by (rule pproof_compatible_pconst[OF Beta.hyps(3)]) (rule pproof_beta_pconst)
  show ?case by simp (rule pH_proves.Beta[OF pconst_subst_type[OF Beta.hyps(1) Beta.prems(1)]
    pconst_subst_type[OF Beta.hyps(2) Beta.prems(1)] step pconst_subst_signature_into[OF Beta.hyps(4) Beta.prems(2) names] pconst_subst_signature_into[OF Beta.hyps(5) Beta.prems(2) names]])
next
  case (Eta \<Gamma> A B)
  have step: "pcompatible_step peta_contract (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B)"
    by (rule pproof_compatible_pconst[OF Eta.hyps(3)]) (rule pproof_eta_pconst)
  show ?case by simp (rule pH_proves.Eta[OF pconst_subst_type[OF Eta.hyps(1) Eta.prems(1)]
    pconst_subst_type[OF Eta.hyps(2) Eta.prems(1)] step pconst_subst_signature_into[OF Eta.hyps(4) Eta.prems(2) names] pconst_subst_signature_into[OF Eta.hyps(5) Eta.prems(2) names]])
next
  case (MP \<Gamma> A B)
  have left: "pH_proves \<Omega> \<Gamma> (pconst_subst c \<sigma> N A)" by (rule MP.IH(1)[where N=N, OF MP.prems])
  have right: "pH_proves \<Omega> \<Gamma> (PImp (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B))"
    using MP.IH(2)[where N=N, OF MP.prems] by simp
  show ?case by (rule pH_proves.MP[OF left right pconst_subst_signature_into[OF MP.hyps(3) MP.prems(2) names] pconst_subst_signature_into[OF MP.hyps(4) MP.prems(2) names]])
next
  case (Gen \<Gamma> P \<rho> Q)
  have nt: "has_ptype (\<rho> # \<Gamma>) (pshift N) \<sigma>" by (rule pshift_preserves_typing[OF Gen.prems(1)])
  have ns: "pterm_in_signature \<Omega> (pshift N)" using Gen.prems(2) by (simp add: pshift_def)
  have premise: "pH_proves \<Omega> (\<rho> # \<Gamma>) (PImp (pshift (pconst_subst c \<sigma> N P)) (pconst_subst c \<sigma> (pshift N) Q))"
    using Gen.IH[where N="pshift N", OF nt ns] by (simp add: pproof_pconst_shift)
  show ?case by simp (rule pH_proves.Gen[OF pconst_subst_type[OF Gen.hyps(1) Gen.prems(1)] pconst_subst_type[OF Gen.hyps(2) nt]
    pconst_subst_signature_into[OF Gen.hyps(3) Gen.prems(2) names] pconst_subst_signature_into[OF Gen.hyps(4) ns names] premise])
next
  case (Inst \<rho> \<Gamma> P Q)
  have nt: "has_ptype (\<rho> # \<Gamma>) (pshift N) \<sigma>" by (rule pshift_preserves_typing[OF Inst.prems(1)])
  have ns: "pterm_in_signature \<Omega> (pshift N)" using Inst.prems(2) by (simp add: pshift_def)
  have premise: "pH_proves \<Omega> (\<rho> # \<Gamma>) (PImp (pconst_subst c \<sigma> (pshift N) P) (pshift (pconst_subst c \<sigma> N Q)))"
    using Inst.IH[where N="pshift N", OF nt ns] by (simp add: pproof_pconst_shift)
  show ?case by simp (rule pH_proves.Inst[OF pconst_subst_type[OF Inst.hyps(1) nt] pconst_subst_type[OF Inst.hyps(2) Inst.prems(1)]
    pconst_subst_signature_into[OF Inst.hyps(3) ns names] pconst_subst_signature_into[OF Inst.hyps(4) Inst.prems(2) names] premise])
qed

lemma pH_derivable_pconst_into:
  fixes \<Sigma> \<Omega> :: "'a psignature" and N :: "'a pterm" and c :: 'a
  assumes d: "pH_derivable \<Sigma> \<Gamma> L A" and typed: "has_ptype \<Gamma> N \<sigma>"
    and sigN: "pterm_in_signature \<Omega> N"
    and names: "\<And>d \<tau>. d \<in> \<Sigma> \<tau> \<Longrightarrow> d \<noteq> c \<or> \<tau> \<noteq> \<sigma> \<Longrightarrow> d \<in> \<Omega> \<tau>"
  shows "pH_derivable \<Omega> \<Gamma> (map (pconst_subst c \<sigma> N) L) (pconst_subst c \<sigma> N A)"
proof (rule pproof_local_transport[OF d])
  fix B :: "'a pterm" assume proof_B: "pH_proves \<Sigma> \<Gamma> B"
  show "pH_proves \<Omega> \<Gamma> (pconst_subst c \<sigma> N B)"
    by (rule pH_proves_pconst_into[OF proof_B typed sigN names])
next
  fix B :: "'a pterm" assume B: "has_ptype \<Gamma> B Prop"
  show "has_ptype \<Gamma> (pconst_subst c \<sigma> N B) Prop"
    by (rule pconst_subst_type[OF B typed])
next
  fix B :: "'a pterm" assume B: "pterm_in_signature \<Sigma> B"
  show "pterm_in_signature \<Omega> (pconst_subst c \<sigma> N B)"
    by (rule pconst_subst_signature_into[OF B sigN names])
next
  fix B C :: "'a pterm"
  show "pconst_subst c \<sigma> N (PImp B C) =
    PImp (pconst_subst c \<sigma> N B) (pconst_subst c \<sigma> N C)" by simp
qed

lemma pH_set_pconst_into:
  fixes \<Sigma> \<Omega> :: "'a psignature" and N :: "'a pterm" and c :: 'a
  assumes d: "pH_set_derivable \<Sigma> \<Gamma> S A" and typed: "has_ptype \<Gamma> N \<sigma>"
    and sigN: "pterm_in_signature \<Omega> N"
    and names: "\<And>d \<tau>. d \<in> \<Sigma> \<tau> \<Longrightarrow> d \<noteq> c \<or> \<tau> \<noteq> \<sigma> \<Longrightarrow> d \<in> \<Omega> \<tau>"
  shows "pH_set_derivable \<Omega> \<Gamma>
    (image (pconst_subst c \<sigma> N) S) (pconst_subst c \<sigma> N A)"
proof (rule pproof_set_transport[OF d])
  fix L :: "'a pterm list" and B :: "'a pterm"
  assume local_B: "pH_derivable \<Sigma> \<Gamma> L B"
  show "pH_derivable \<Omega> \<Gamma> (map (pconst_subst c \<sigma> N) L) (pconst_subst c \<sigma> N B)"
    by (rule pH_derivable_pconst_into[OF local_B typed sigN names])
qed

subsection \<open>Monotonicity in the declared signature\<close>

lemma phenkin_map_id[simp]: "phenkin_map id A = A"
  by (induction A) simp_all

lemma pH_signature_mono:
  assumes d: "pH_proves \<Sigma> \<Gamma> A" and inclusion: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> \<Omega> \<tau>"
  shows "pH_proves \<Omega> \<Gamma> A"
proof -
  have names: "id c \<in> \<Omega> \<tau>" if declared: "c \<in> \<Sigma> \<tau>" for c \<tau>
    using subsetD[OF inclusion declared] by simp
  have mapped: "pH_proves \<Omega> \<Gamma> (phenkin_map id A)"
    by (rule phenkin_map_proves[OF d names])
  show ?thesis using mapped by simp
qed

lemma pH_local_signature_mono:
  assumes d: "pH_derivable \<Sigma> \<Gamma> L A"
    and inclusion: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> \<Omega> \<tau>"
  shows "pH_derivable \<Omega> \<Gamma> L A"
  using d
proof (induction rule: pH_derivable.induct)
  case (Assumption A)
  have sig: "pterm_in_signature \<Omega> A"
    by (rule pterm_signature_mono[OF Assumption.hyps(3) inclusion])
  show ?case by (rule pH_derivable.Assumption[OF Assumption.hyps(1,2) sig])
next
  case (Theorem A)
  show ?case by (rule pH_derivable.Theorem[OF pH_signature_mono[OF Theorem.hyps inclusion]])
next
  case (MP A B)
  show ?case by (rule pH_derivable.MP[OF MP.IH])
qed

lemma pH_set_signature_mono:
  assumes d: "pH_set_derivable \<Sigma> \<Gamma> S A"
    and inclusion: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> \<Omega> \<tau>"
  shows "pH_set_derivable \<Omega> \<Gamma> S A"
proof -
  obtain L where support: "set L \<subseteq> S" and local_d: "pH_derivable \<Sigma> \<Gamma> L A"
    using d unfolding pH_set_derivable_def by (elim exE conjE)
  have target: "pH_derivable \<Omega> \<Gamma> L A"
    by (rule pH_local_signature_mono[OF local_d inclusion])
  show ?thesis unfolding pH_set_derivable_def
    by (rule exI[where x=L], rule conjI[OF support target])
qed

end
