theory Bacon_Parametric_Theorem_Substitution
  imports Bacon_Parametric_Conversion_Substitution
begin

section \<open>Transport of signature-indexed H proofs\<close>

text \<open>
  Σ; Γ ⊢H A yields the renamed or constant-substituted theorem when
  the variable map respects types and the replacement belongs to ℒ(Σ).
  Sources: Bacon--Dorr Figure 2, p.8, and p.45 n.64.  The induction
  below retains every signature guard; it does not assume admissibility.
\<close>

subsection \<open>Transport of signature-guarded theoremhood\<close>

lemma pproof_signature_prenameI:
  assumes sig: "pterm_in_signature \<Sigma> A"
  shows "pterm_in_signature \<Sigma> (prename r A)"
  by (rule iffD2[OF prename_signature[where \<Sigma>=\<Sigma> and r=r and M=A] sig])

lemma pH_proves_prename:
  assumes d: "pH_proves \<Sigma> \<Gamma> A"
    and ren: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "pH_proves \<Sigma> \<Delta> (prename r A)"
  using d ren
proof (induction arbitrary: \<Delta> r rule: pH_proves.induct)
  case (PC \<Gamma> A)
  have sig: "pterm_in_signature \<Sigma> (prename r A)"
    by (rule pproof_signature_prenameI[OF PC.hyps(2)])
  show ?case by (rule pH_proves.PC[OF pproof_taut_prename[OF PC.hyps(1) PC.prems] sig])
next
  case (IndividualExistence \<Gamma>)
  show ?case by simp (rule pH_proves.IndividualExistence)
next
  case (UI \<rho> \<Gamma> A T)
  have lift: "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow> lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    by (rule lookup_lift_ren[OF UI.prems])
  have body_type: "has_ptype (\<rho> # \<Delta>) (prename (lift_ren r) A) Prop"
    by (rule prename_preserves_typing[OF UI.hyps(1) lift])
  have arg_type: "has_ptype \<Delta> (prename r T) \<rho>"
    by (rule prename_preserves_typing[OF UI.hyps(2) UI.prems])
  have body_sig: "pterm_in_signature \<Sigma> (prename (lift_ren r) A)"
    by (rule pproof_signature_prenameI[OF UI.hyps(3)])
  have arg_sig: "pterm_in_signature \<Sigma> (prename r T)"
    by (rule pproof_signature_prenameI[OF UI.hyps(4)])
  have commutation: "prename r (psubst0 T A) = psubst0 (prename r T) (prename (lift_ren r) A)"
    by (rule pproof_prename_psubst0)
  have result: "pH_proves \<Sigma> \<Delta> (PImp (PForall \<rho> (prename (lift_ren r) A))
      (psubst0 (prename r T) (prename (lift_ren r) A)))"
    by (rule pH_proves.UI[OF body_type arg_type body_sig arg_sig])
  show ?case using result by (simp only: prename.simps commutation)
next
  case (EG \<rho> \<Gamma> A T)
  have lift: "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow> lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    by (rule lookup_lift_ren[OF EG.prems])
  have body_type: "has_ptype (\<rho> # \<Delta>) (prename (lift_ren r) A) Prop"
    by (rule prename_preserves_typing[OF EG.hyps(1) lift])
  have arg_type: "has_ptype \<Delta> (prename r T) \<rho>"
    by (rule prename_preserves_typing[OF EG.hyps(2) EG.prems])
  have body_sig: "pterm_in_signature \<Sigma> (prename (lift_ren r) A)"
    by (rule pproof_signature_prenameI[OF EG.hyps(3)])
  have arg_sig: "pterm_in_signature \<Sigma> (prename r T)"
    by (rule pproof_signature_prenameI[OF EG.hyps(4)])
  have commutation: "prename r (psubst0 T A) = psubst0 (prename r T) (prename (lift_ren r) A)"
    by (rule pproof_prename_psubst0)
  have result: "pH_proves \<Sigma> \<Delta> (PImp (psubst0 (prename r T) (prename (lift_ren r) A))
      (PExists \<rho> (prename (lift_ren r) A)))"
    by (rule pH_proves.EG[OF body_type arg_type body_sig arg_sig])
  show ?case using result by (simp only: prename.simps commutation)
next
  case (Ref \<Gamma> M \<rho>)
  have renamed_type: "has_ptype \<Delta> (prename r M) \<rho>"
    by (rule prename_preserves_typing[OF Ref.hyps(1) Ref.prems])
  have renamed_sig: "pterm_in_signature \<Sigma> (prename r M)"
    by (rule pproof_signature_prenameI[OF Ref.hyps(2)])
  have result: "pH_proves \<Sigma> \<Delta> (PEq \<rho> (prename r M) (prename r M))"
    by (rule pH_proves.Ref[OF renamed_type renamed_sig])
  show ?case using result by (simp only: prename.simps)
next
  case (LL \<Gamma> A \<rho> B F)
  have A_type: "has_ptype \<Delta> (prename r A) \<rho>"
    by (rule prename_preserves_typing[OF LL.hyps(1) LL.prems])
  have B_type: "has_ptype \<Delta> (prename r B) \<rho>"
    by (rule prename_preserves_typing[OF LL.hyps(2) LL.prems])
  have F_type: "has_ptype \<Delta> (prename r F) (\<rho> \<rightarrow>\<^sub>o Prop)"
    by (rule prename_preserves_typing[OF LL.hyps(3) LL.prems])
  have A_sig: "pterm_in_signature \<Sigma> (prename r A)"
    by (rule pproof_signature_prenameI[OF LL.hyps(4)])
  have B_sig: "pterm_in_signature \<Sigma> (prename r B)"
    by (rule pproof_signature_prenameI[OF LL.hyps(5)])
  have F_sig: "pterm_in_signature \<Sigma> (prename r F)"
    by (rule pproof_signature_prenameI[OF LL.hyps(6)])
  have result: "pH_proves \<Sigma> \<Delta> (PImp (PEq \<rho> (prename r A) (prename r B))
      (PImp (PApp (prename r F) (prename r A)) (PApp (prename r F) (prename r B))))"
    by (rule pH_proves.LL[OF A_type B_type F_type A_sig B_sig F_sig])
  show ?case using result by (simp only: prename.simps)
next
  case (Beta \<Gamma> A B)
  have A_type: "has_ptype \<Delta> (prename r A) Prop"
    by (rule prename_preserves_typing[OF Beta.hyps(1) Beta.prems])
  have B_type: "has_ptype \<Delta> (prename r B) Prop"
    by (rule prename_preserves_typing[OF Beta.hyps(2) Beta.prems])
  have A_sig: "pterm_in_signature \<Sigma> (prename r A)"
    by (rule pproof_signature_prenameI[OF Beta.hyps(4)])
  have B_sig: "pterm_in_signature \<Sigma> (prename r B)"
    by (rule pproof_signature_prenameI[OF Beta.hyps(5)])
  have step: "pcompatible_step pbeta_contract (prename r A) (prename r B)"
    by (rule pproof_compatible_prename[where R=pbeta_contract and A=A and B=B and r=r,
          OF Beta.hyps(3)]) (rule pproof_beta_prename)
  have result: "pH_proves \<Sigma> \<Delta> (PObjIff (prename r A) (prename r B))"
    by (rule pH_proves.Beta[OF A_type B_type step A_sig B_sig])
  show ?case using result by (simp only: prename.simps)
next
  case (Eta \<Gamma> A B)
  have A_type: "has_ptype \<Delta> (prename r A) Prop"
    by (rule prename_preserves_typing[OF Eta.hyps(1) Eta.prems])
  have B_type: "has_ptype \<Delta> (prename r B) Prop"
    by (rule prename_preserves_typing[OF Eta.hyps(2) Eta.prems])
  have A_sig: "pterm_in_signature \<Sigma> (prename r A)"
    by (rule pproof_signature_prenameI[OF Eta.hyps(4)])
  have B_sig: "pterm_in_signature \<Sigma> (prename r B)"
    by (rule pproof_signature_prenameI[OF Eta.hyps(5)])
  have step: "pcompatible_step peta_contract (prename r A) (prename r B)"
    by (rule pproof_compatible_prename[where R=peta_contract and A=A and B=B and r=r,
          OF Eta.hyps(3)]) (rule pproof_eta_prename)
  have result: "pH_proves \<Sigma> \<Delta> (PObjIff (prename r A) (prename r B))"
    by (rule pH_proves.Eta[OF A_type B_type step A_sig B_sig])
  show ?case using result by (simp only: prename.simps)
next
  case (MP \<Gamma> A B)
  have left: "pH_proves \<Sigma> \<Delta> (prename r A)"
    by (rule MP.IH(1)[where \<Delta>=\<Delta> and r=r, OF MP.prems])
  have right_raw: "pH_proves \<Sigma> \<Delta> (prename r (PImp A B))"
    by (rule MP.IH(2)[where \<Delta>=\<Delta> and r=r, OF MP.prems])
  have right: "pH_proves \<Sigma> \<Delta> (PImp (prename r A) (prename r B))"
    using right_raw by (simp only: prename.simps)
  have A_sig: "pterm_in_signature \<Sigma> (prename r A)"
    by (rule pproof_signature_prenameI[OF MP.hyps(3)])
  have B_sig: "pterm_in_signature \<Sigma> (prename r B)"
    by (rule pproof_signature_prenameI[OF MP.hyps(4)])
  show ?case by (rule pH_proves.MP[OF left right A_sig B_sig])
next
  case (Gen \<Gamma> P \<rho> Q)
  have lift: "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow> lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    by (rule lookup_lift_ren[OF Gen.prems])
  have P_type: "has_ptype \<Delta> (prename r P) Prop"
    by (rule prename_preserves_typing[OF Gen.hyps(1) Gen.prems])
  have Q_type: "has_ptype (\<rho> # \<Delta>) (prename (lift_ren r) Q) Prop"
    by (rule prename_preserves_typing[OF Gen.hyps(2) lift])
  have P_sig: "pterm_in_signature \<Sigma> (prename r P)"
    by (rule pproof_signature_prenameI[OF Gen.hyps(3)])
  have Q_sig: "pterm_in_signature \<Sigma> (prename (lift_ren r) Q)"
    by (rule pproof_signature_prenameI[OF Gen.hyps(4)])
  have premise_raw: "pH_proves \<Sigma> (\<rho> # \<Delta>) (prename (lift_ren r) (PImp (pshift P) Q))"
    by (rule Gen.IH[where \<Delta>="\<rho> # \<Delta>" and r="lift_ren r", OF lift])
  have premise: "pH_proves \<Sigma> (\<rho> # \<Delta>) (PImp (pshift (prename r P)) (prename (lift_ren r) Q))"
    using premise_raw by (simp only: prename.simps pproof_prename_lift_shift)
  have result: "pH_proves \<Sigma> \<Delta> (PImp (prename r P) (PForall \<rho> (prename (lift_ren r) Q)))"
    by (rule pH_proves.Gen[OF P_type Q_type P_sig Q_sig premise])
  show ?case using result by (simp only: prename.simps)
next
  case (Inst \<rho> \<Gamma> P Q)
  have lift: "\<And>n \<tau>. lookup (\<rho> # \<Gamma>) n = Some \<tau> \<Longrightarrow> lookup (\<rho> # \<Delta>) (lift_ren r n) = Some \<tau>"
    by (rule lookup_lift_ren[OF Inst.prems])
  have P_type: "has_ptype (\<rho> # \<Delta>) (prename (lift_ren r) P) Prop"
    by (rule prename_preserves_typing[OF Inst.hyps(1) lift])
  have Q_type: "has_ptype \<Delta> (prename r Q) Prop"
    by (rule prename_preserves_typing[OF Inst.hyps(2) Inst.prems])
  have P_sig: "pterm_in_signature \<Sigma> (prename (lift_ren r) P)"
    by (rule pproof_signature_prenameI[OF Inst.hyps(3)])
  have Q_sig: "pterm_in_signature \<Sigma> (prename r Q)"
    by (rule pproof_signature_prenameI[OF Inst.hyps(4)])
  have premise_raw: "pH_proves \<Sigma> (\<rho> # \<Delta>) (prename (lift_ren r) (PImp P (pshift Q)))"
    by (rule Inst.IH[where \<Delta>="\<rho> # \<Delta>" and r="lift_ren r", OF lift])
  have premise: "pH_proves \<Sigma> (\<rho> # \<Delta>) (PImp (prename (lift_ren r) P) (pshift (prename r Q)))"
    using premise_raw by (simp only: prename.simps pproof_prename_lift_shift)
  have result: "pH_proves \<Sigma> \<Delta> (PImp (PExists \<rho> (prename (lift_ren r) P)) (prename r Q))"
    by (rule pH_proves.Inst[OF P_type Q_type P_sig Q_sig premise])
  show ?case using result by (simp only: prename.simps)
qed

lemma pH_proves_pconst:
  assumes d: "pH_proves \<Sigma> \<Gamma> A" and typed: "has_ptype \<Gamma> N \<sigma>" and sigN: "pterm_in_signature \<Sigma> N"
  shows "pH_proves \<Sigma> \<Gamma> (pconst_subst c \<sigma> N A)"
  using d typed sigN
proof (induction arbitrary: N rule: pH_proves.induct)
  case (PC \<Gamma> A)
  show ?case by (rule pH_proves.PC[OF pproof_taut_pconst[OF PC.hyps(1) PC.prems(1)] pconst_subst_signature[OF PC.hyps(2) PC.prems(2)]])
next
  case (IndividualExistence \<Gamma>)
  show ?case by simp (rule pH_proves.IndividualExistence)
next
  case (UI \<rho> \<Gamma> A T)
  have nt: "has_ptype (\<rho> # \<Gamma>) (pshift N) \<sigma>" by (rule pshift_preserves_typing[OF UI.prems(1)])
  have ns: "pterm_in_signature \<Sigma> (pshift N)" using UI.prems(2) by (simp add: pshift_def)
  show ?case by (simp only: pconst_subst.simps pproof_pconst_psubst0)
    (rule pH_proves.UI[OF pconst_subst_type[OF UI.hyps(1) nt] pconst_subst_type[OF UI.hyps(2) UI.prems(1)]
      pconst_subst_signature[OF UI.hyps(3) ns] pconst_subst_signature[OF UI.hyps(4) UI.prems(2)]])
next
  case (EG \<rho> \<Gamma> A T)
  have nt: "has_ptype (\<rho> # \<Gamma>) (pshift N) \<sigma>" by (rule pshift_preserves_typing[OF EG.prems(1)])
  have ns: "pterm_in_signature \<Sigma> (pshift N)" using EG.prems(2) by (simp add: pshift_def)
  show ?case by (simp only: pconst_subst.simps pproof_pconst_psubst0)
    (rule pH_proves.EG[OF pconst_subst_type[OF EG.hyps(1) nt] pconst_subst_type[OF EG.hyps(2) EG.prems(1)]
      pconst_subst_signature[OF EG.hyps(3) ns] pconst_subst_signature[OF EG.hyps(4) EG.prems(2)]])
next
  case (Ref \<Gamma> M \<rho>)
  show ?case by simp (rule pH_proves.Ref[OF pconst_subst_type[OF Ref.hyps(1) Ref.prems(1)] pconst_subst_signature[OF Ref.hyps(2) Ref.prems(2)]])
next
  case (LL \<Gamma> A \<rho> B F)
  show ?case by simp (rule pH_proves.LL[OF pconst_subst_type[OF LL.hyps(1) LL.prems(1)]
    pconst_subst_type[OF LL.hyps(2) LL.prems(1)] pconst_subst_type[OF LL.hyps(3) LL.prems(1)]
    pconst_subst_signature[OF LL.hyps(4) LL.prems(2)] pconst_subst_signature[OF LL.hyps(5) LL.prems(2)] pconst_subst_signature[OF LL.hyps(6) LL.prems(2)]])
next
  case (Beta \<Gamma> A B)
  have step: "pcompatible_step pbeta_contract (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B)"
    by (rule pproof_compatible_pconst[OF Beta.hyps(3)]) (rule pproof_beta_pconst)
  show ?case by simp (rule pH_proves.Beta[OF pconst_subst_type[OF Beta.hyps(1) Beta.prems(1)]
    pconst_subst_type[OF Beta.hyps(2) Beta.prems(1)] step pconst_subst_signature[OF Beta.hyps(4) Beta.prems(2)] pconst_subst_signature[OF Beta.hyps(5) Beta.prems(2)]])
next
  case (Eta \<Gamma> A B)
  have step: "pcompatible_step peta_contract (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B)"
    by (rule pproof_compatible_pconst[OF Eta.hyps(3)]) (rule pproof_eta_pconst)
  show ?case by simp (rule pH_proves.Eta[OF pconst_subst_type[OF Eta.hyps(1) Eta.prems(1)]
    pconst_subst_type[OF Eta.hyps(2) Eta.prems(1)] step pconst_subst_signature[OF Eta.hyps(4) Eta.prems(2)] pconst_subst_signature[OF Eta.hyps(5) Eta.prems(2)]])
next
  case (MP \<Gamma> A B)
  have left: "pH_proves \<Sigma> \<Gamma> (pconst_subst c \<sigma> N A)" by (rule MP.IH(1)[where N=N, OF MP.prems])
  have right: "pH_proves \<Sigma> \<Gamma> (PImp (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B))"
    using MP.IH(2)[where N=N, OF MP.prems] by simp
  show ?case by (rule pH_proves.MP[OF left right pconst_subst_signature[OF MP.hyps(3) MP.prems(2)] pconst_subst_signature[OF MP.hyps(4) MP.prems(2)]])
next
  case (Gen \<Gamma> P \<rho> Q)
  have nt: "has_ptype (\<rho> # \<Gamma>) (pshift N) \<sigma>" by (rule pshift_preserves_typing[OF Gen.prems(1)])
  have ns: "pterm_in_signature \<Sigma> (pshift N)" using Gen.prems(2) by (simp add: pshift_def)
  have premise: "pH_proves \<Sigma> (\<rho> # \<Gamma>) (PImp (pshift (pconst_subst c \<sigma> N P)) (pconst_subst c \<sigma> (pshift N) Q))"
    using Gen.IH[where N="pshift N", OF nt ns] by (simp add: pproof_pconst_shift)
  show ?case by simp (rule pH_proves.Gen[OF pconst_subst_type[OF Gen.hyps(1) Gen.prems(1)] pconst_subst_type[OF Gen.hyps(2) nt]
    pconst_subst_signature[OF Gen.hyps(3) Gen.prems(2)] pconst_subst_signature[OF Gen.hyps(4) ns] premise])
next
  case (Inst \<rho> \<Gamma> P Q)
  have nt: "has_ptype (\<rho> # \<Gamma>) (pshift N) \<sigma>" by (rule pshift_preserves_typing[OF Inst.prems(1)])
  have ns: "pterm_in_signature \<Sigma> (pshift N)" using Inst.prems(2) by (simp add: pshift_def)
  have premise: "pH_proves \<Sigma> (\<rho> # \<Gamma>) (PImp (pconst_subst c \<sigma> (pshift N) P) (pshift (pconst_subst c \<sigma> N Q)))"
    using Inst.IH[where N="pshift N", OF nt ns] by (simp add: pproof_pconst_shift)
  show ?case by simp (rule pH_proves.Inst[OF pconst_subst_type[OF Inst.hyps(1) nt] pconst_subst_type[OF Inst.hyps(2) Inst.prems(1)]
    pconst_subst_signature[OF Inst.hyps(3) ns] pconst_subst_signature[OF Inst.hyps(4) Inst.prems(2)] premise])
qed

end
