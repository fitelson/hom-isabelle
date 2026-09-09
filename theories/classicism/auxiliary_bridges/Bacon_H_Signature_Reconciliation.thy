theory Bacon_H_Signature_Reconciliation
  imports
    Bacon_BBK_Semantics_Development.Bacon_H_Signature_Proof
    Bacon_Parametric_Signature_Development.Bacon_Parametric_String_Bridge
begin

section \<open>The two signature-guarded presentations of H coincide\<close>

text \<open>
  Σ; Γ ⊢H A has the same meaning in the earlier string syntax and in
  the string instance of the parametric syntax. Source: the represented
  rules of Bacon--Dorr Figure 2, with the same context-indexed Existence
  adjustment in both presentations.

  Every rule is transported with its signature guards, including the
  intermediate formulas in MP. This connects the useful earlier calculus
  to the arbitrary-signature reconstruction. It does not yet show that an
  unrestricted H proof whose conclusion lies in Σ can be confined to Σ.
\<close>

lemma H_reconciliation_signature:
  "bbk_in_signature \<Sigma> A = oterm_in_string_signature \<Sigma> A"
  by (induction A) simp_all

lemma H_reconciliation_pterm_signature:
  "pterm_in_signature \<Sigma> A = bbk_in_signature \<Sigma> (pterm_to_oterm A)"
  by (simp only: pterm_string_signature_iff H_reconciliation_signature)

theorem H_signature_to_parametric:
  assumes "H_signature_proves \<Sigma> \<Gamma> A"
  shows "pH_on_string_syntax \<Sigma> \<Gamma> A"
  using assms
proof (induction rule: H_signature_proves.induct)
  case (PC \<Gamma> A)
  show ?case by (rule pH_on_string_PC[OF PC.hyps(1)])
    (use PC.hyps(2) in \<open>simp only: H_reconciliation_signature\<close>)
next
  case (IndividualExistence \<Gamma>)
  show ?case by (rule pH_on_string_IndividualExistence)
next
  case (UI \<sigma> \<Gamma> A T)
  show ?case by (rule pH_on_string_UI[OF UI.hyps(1,2)])
    (use UI.hyps(3,4) in \<open>simp_all only: H_reconciliation_signature\<close>)
next
  case (EG \<sigma> \<Gamma> A T)
  show ?case by (rule pH_on_string_EG[OF EG.hyps(1,2)])
    (use EG.hyps(3,4) in \<open>simp_all only: H_reconciliation_signature\<close>)
next
  case (Ref \<Gamma> M \<sigma>)
  show ?case by (rule pH_on_string_Ref[OF Ref.hyps(1)])
    (use Ref.hyps(2) in \<open>simp only: H_reconciliation_signature\<close>)
next
  case (LL \<Gamma> A \<sigma> B F)
  show ?case by (rule pH_on_string_LL[OF LL.hyps(1,2,3)])
    (use LL.hyps(4,5,6) in \<open>simp_all only: H_reconciliation_signature\<close>)
next
  case (Beta \<Gamma> A B)
  show ?case by (rule pH_on_string_Beta[OF Beta.hyps(1,2,3)])
    (use Beta.hyps(4,5) in \<open>simp_all only: H_reconciliation_signature\<close>)
next
  case (Eta \<Gamma> A B)
  show ?case by (rule pH_on_string_Eta[OF Eta.hyps(1,2,3)])
    (use Eta.hyps(4,5) in \<open>simp_all only: H_reconciliation_signature\<close>)
next
  case (MP \<Gamma> A B)
  show ?case by (rule pH_on_string_MP[OF MP.IH])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case by (rule pH_on_string_Gen[OF Gen.hyps(1,2) _ _ Gen.IH])
    (use Gen.hyps(3,4) in \<open>simp_all only: H_reconciliation_signature\<close>)
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case by (rule pH_on_string_Inst[OF Inst.hyps(1,2) _ _ Inst.IH])
    (use Inst.hyps(3,4) in \<open>simp_all only: H_reconciliation_signature\<close>)
qed

theorem parametric_to_H_signature:
  assumes "pH_proves \<Sigma> \<Gamma> A"
  shows "H_signature_proves \<Sigma> \<Gamma> (pterm_to_oterm A)"
  using assms
proof (induction rule: pH_proves.induct)
  case (PC \<Gamma> A)
  show ?case by (rule H_signature_proves.PC)
    (use PC.hyps in \<open>simp_all only: pprop_tautology_string_iff H_reconciliation_pterm_signature\<close>)
next
  case (IndividualExistence \<Gamma>)
  show ?case by (simp only: pterm_to_oterm.simps)
    (rule H_signature_proves.IndividualExistence)
next
  case (UI \<sigma> \<Gamma> A T)
  show ?case by (simp only: pterm_to_oterm.simps pterm_to_psubst0;
    rule H_signature_proves.UI[OF pterm_to_preserves_typing[OF UI.hyps(1)]
      pterm_to_preserves_typing[OF UI.hyps(2)]])
    (use UI.hyps(3,4) in \<open>simp_all only: H_reconciliation_pterm_signature\<close>)
next
  case (EG \<sigma> \<Gamma> A T)
  show ?case by (simp only: pterm_to_oterm.simps pterm_to_psubst0;
    rule H_signature_proves.EG[OF pterm_to_preserves_typing[OF EG.hyps(1)]
      pterm_to_preserves_typing[OF EG.hyps(2)]])
    (use EG.hyps(3,4) in \<open>simp_all only: H_reconciliation_pterm_signature\<close>)
next
  case (Ref \<Gamma> M \<sigma>)
  show ?case by (simp only: pterm_to_oterm.simps;
    rule H_signature_proves.Ref[OF pterm_to_preserves_typing[OF Ref.hyps(1)]])
    (use Ref.hyps(2) in \<open>simp only: H_reconciliation_pterm_signature\<close>)
next
  case (LL \<Gamma> A \<sigma> B F)
  show ?case by (simp only: pterm_to_oterm.simps;
    rule H_signature_proves.LL[OF pterm_to_preserves_typing[OF LL.hyps(1)]
      pterm_to_preserves_typing[OF LL.hyps(2)] pterm_to_preserves_typing[OF LL.hyps(3)]])
    (use LL.hyps(4,5,6) in \<open>simp_all only: H_reconciliation_pterm_signature\<close>)
next
  case (Beta \<Gamma> A B)
  have step: "compatible_step beta_contract (pterm_to_oterm A) (pterm_to_oterm B)"
    using Beta.hyps(3) by (simp only: pcompatible_beta_string_iff)
  show ?case by (simp only: pterm_to_oterm.simps;
    rule H_signature_proves.Beta[OF pterm_to_preserves_typing[OF Beta.hyps(1)]
      pterm_to_preserves_typing[OF Beta.hyps(2)] step])
    (use Beta.hyps(4,5) in \<open>simp_all only: H_reconciliation_pterm_signature\<close>)
next
  case (Eta \<Gamma> A B)
  have step: "compatible_step eta_contract (pterm_to_oterm A) (pterm_to_oterm B)"
    using Eta.hyps(3) by (simp only: pcompatible_eta_string_iff)
  show ?case by (simp only: pterm_to_oterm.simps;
    rule H_signature_proves.Eta[OF pterm_to_preserves_typing[OF Eta.hyps(1)]
      pterm_to_preserves_typing[OF Eta.hyps(2)] step])
    (use Eta.hyps(4,5) in \<open>simp_all only: H_reconciliation_pterm_signature\<close>)
next
  case (MP \<Gamma> A B)
  have implication: "H_signature_proves \<Sigma> \<Gamma> (Imp (pterm_to_oterm A) (pterm_to_oterm B))"
    using MP.IH(2) by (simp only: pterm_to_oterm.simps)
  show ?case by (rule H_signature_proves.MP[OF MP.IH(1) implication])
    (use MP.hyps(3,4) in \<open>simp_all only: H_reconciliation_pterm_signature\<close>)
next
  case (Gen \<Gamma> P \<sigma> Q)
  have premise: "H_signature_proves \<Sigma> (\<sigma> # \<Gamma>)
    (Imp (shift (pterm_to_oterm P)) (pterm_to_oterm Q))"
    using Gen.IH by (simp only: pterm_to_oterm.simps pterm_to_pshift)
  show ?case by (simp only: pterm_to_oterm.simps;
    rule H_signature_proves.Gen[OF pterm_to_preserves_typing[OF Gen.hyps(1)]
      pterm_to_preserves_typing[OF Gen.hyps(2)] _ _ premise])
    (use Gen.hyps(3,4) in \<open>simp_all only: H_reconciliation_pterm_signature\<close>)
next
  case (Inst \<sigma> \<Gamma> P Q)
  have premise: "H_signature_proves \<Sigma> (\<sigma> # \<Gamma>)
    (Imp (pterm_to_oterm P) (shift (pterm_to_oterm Q)))"
    using Inst.IH by (simp only: pterm_to_oterm.simps pterm_to_pshift)
  show ?case by (simp only: pterm_to_oterm.simps;
    rule H_signature_proves.Inst[OF pterm_to_preserves_typing[OF Inst.hyps(1)]
      pterm_to_preserves_typing[OF Inst.hyps(2)] _ _ premise])
    (use Inst.hyps(3,4) in \<open>simp_all only: H_reconciliation_pterm_signature\<close>)
qed

theorem H_signature_parametric_iff:
  "H_signature_proves \<Sigma> \<Gamma> A \<longleftrightarrow>
    pH_proves \<Sigma> \<Gamma> (pterm_of_oterm A)"
proof
  assume "H_signature_proves \<Sigma> \<Gamma> A"
  then show "pH_proves \<Sigma> \<Gamma> (pterm_of_oterm A)"
    using H_signature_to_parametric unfolding pH_on_string_syntax_def by blast
next
  assume "pH_proves \<Sigma> \<Gamma> (pterm_of_oterm A)"
  then show "H_signature_proves \<Sigma> \<Gamma> A"
    using parametric_to_H_signature by (metis pterm_to_of)
qed

end
