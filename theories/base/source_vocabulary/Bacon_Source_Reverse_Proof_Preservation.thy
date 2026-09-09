theory Bacon_Source_Reverse_Proof_Preservation
  imports Bacon_Source_Reverse_Basic_Axioms Bacon_Source_Reverse_Quantifier_Axioms
    Bacon_Source_Reverse_Quantifier_Rules
begin

section \<open>Target H proofs have source proofs in a rich variable stock\<close>

text \<open>
  If target H proves A in finite frame Γ, then source H proves the
  reverse translation of A under every type-respecting representation r
  of Γ in a rich stock G.  Source: Bacon–Dorr Figure 2, pp.7–8, with
  the infinite typed-variable convention of §1.1.

  Isabelle representation.  The induction generalizes G and r.  PC and
  each axiom family use separately checked reverse translations.  Target
  IndividualExistence is supplied by the source's derived Existence
  theorem, not by adding an eleventh source rule.  Gen/Inst invoke the
  immediate-premise induction hypothesis at a fresh extended map, then
  apply the actual source rule and its whole-formula language guard.

  Scope.  This proves target-to-source preservation for pterm_to_paper,
  arbitrary nonlogical signatures, and the represented full F types.
  It does not identify primitive and defined implication in intensional
  contexts, assert a literal syntax inverse, or finish a named-variable/α
  correspondence.  A source round-trip theorem is needed to turn this
  result into reflection for paper_to_pterm.  No source-model theorem is
  claimed, and no general reflection premise enters the induction.
\<close>

theorem pH_to_paper_global_H:
  assumes derivation: "pH_proves \<Sigma> \<Gamma> A"
    and rich: "sg_rich G"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_H \<Sigma> G (srename r (pterm_to_paper A))"
  using derivation rich map
proof (induction arbitrary: G r rule: pH_proves.induct)
  case (PC \<Gamma> A)
  show ?case by (rule pterm_to_paper_global_H_PC[where G=G and r=r, OF PC.hyps(1,2) PC.prems(2)])
next
  case (IndividualExistence \<Gamma>)
  show ?case by (rule paper_reverse_IndividualExistence[OF IndividualExistence.prems(1)])
next
  case (UI \<sigma> \<Gamma> A T)
  have A: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) A Prop"
    unfolding pterm_in_language_def by (rule conjI[OF UI.hyps(1,3)])
  have T: "pterm_in_language \<Sigma> \<Gamma> T \<sigma>"
    unfolding pterm_in_language_def by (rule conjI[OF UI.hyps(2,4)])
  show ?case by (rule paper_reverse_UI[where G=G and r=r, OF A T UI.prems(2)])
next
  case (EG \<sigma> \<Gamma> A T)
  have A: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) A Prop"
    unfolding pterm_in_language_def by (rule conjI[OF EG.hyps(1,3)])
  have T: "pterm_in_language \<Sigma> \<Gamma> T \<sigma>"
    unfolding pterm_in_language_def by (rule conjI[OF EG.hyps(2,4)])
  show ?case by (rule paper_reverse_EG[where G=G and r=r, OF A T EG.prems(2)])
next
  case (Ref \<Gamma> M \<sigma>)
  have target_axiom: "pH_proves \<Sigma> \<Gamma> (PEq \<sigma> M M)" by (rule pH_proves.Ref[OF Ref.hyps])
  have language: "pterm_in_language \<Sigma> \<Gamma> (PEq \<sigma> M M) Prop"
    by (rule pH_proves_in_language[OF target_axiom])
  show ?case by (rule paper_reverse_Ref[where G=G and r=r, OF language Ref.prems(2)])
next
  case (LL \<Gamma> A \<sigma> B F)
  have target_axiom: "pH_proves \<Sigma> \<Gamma>
    (PImp (PEq \<sigma> A B) (PImp (PApp F A) (PApp F B)))"
    by (rule pH_proves.LL[OF LL.hyps])
  have language: "pterm_in_language \<Sigma> \<Gamma>
    (PImp (PEq \<sigma> A B) (PImp (PApp F A) (PApp F B))) Prop"
    by (rule pH_proves_in_language[OF target_axiom])
  show ?case by (rule paper_reverse_LL[where G=G and r=r, OF language LL.prems(2)])
next
  case (Beta \<Gamma> A B)
  have A: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    unfolding pterm_in_language_def by (rule conjI[OF Beta.hyps(1,4)])
  have B: "pterm_in_language \<Sigma> \<Gamma> B Prop"
    unfolding pterm_in_language_def by (rule conjI[OF Beta.hyps(2,5)])
  show ?case by (rule paper_reverse_Beta[where G=G and r=r, OF A B Beta.hyps(3) Beta.prems(2)])
next
  case (Eta \<Gamma> A B)
  have A: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    unfolding pterm_in_language_def by (rule conjI[OF Eta.hyps(1,4)])
  have B: "pterm_in_language \<Sigma> \<Gamma> B Prop"
    unfolding pterm_in_language_def by (rule conjI[OF Eta.hyps(2,5)])
  show ?case by (rule paper_reverse_Eta[where G=G and r=r, OF A B Eta.hyps(3) Eta.prems(2)])
next
  case (MP \<Gamma> A B)
  have premise: "paper_global_H \<Sigma> G (srename r (pterm_to_paper A))"
    by (rule MP.IH(1)[where G=G and r=r, OF MP.prems])
  have implication: "paper_global_H \<Sigma> G (srename r (pterm_to_paper (PImp A B)))"
    by (rule MP.IH(2)[where G=G and r=r, OF MP.prems])
  show ?case by (rule paper_reverse_MP[OF premise implication])
next
  case (Gen \<Gamma> P \<sigma> Q)
  have P: "pterm_in_language \<Sigma> \<Gamma> P Prop"
    unfolding pterm_in_language_def by (rule conjI[OF Gen.hyps(1,3)])
  have Q: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) Q Prop"
    unfolding pterm_in_language_def by (rule conjI[OF Gen.hyps(2,4)])
  have rule_IH: "paper_global_H \<Sigma> G (srename s (pterm_to_paper (PImp (pshift P) Q)))"
    if extended: "\<And>k \<rho>. lookup (\<sigma> # \<Gamma>) k = Some \<rho> \<Longrightarrow> G (s k) = \<rho>" for s
    by (rule Gen.IH[where G=G and r=s, OF Gen.prems(1) extended])
  show ?case by (rule paper_back_Gen_translation[where G=G and r=r, OF Gen.prems(1) P Q Gen.prems(2) rule_IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  have P: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) P Prop"
    unfolding pterm_in_language_def by (rule conjI[OF Inst.hyps(1,3)])
  have Q: "pterm_in_language \<Sigma> \<Gamma> Q Prop"
    unfolding pterm_in_language_def by (rule conjI[OF Inst.hyps(2,4)])
  have rule_IH: "paper_global_H \<Sigma> G (srename s (pterm_to_paper (PImp P (pshift Q))))"
    if extended: "\<And>k \<rho>. lookup (\<sigma> # \<Gamma>) k = Some \<rho> \<Longrightarrow> G (s k) = \<rho>" for s
    by (rule Inst.IH[where G=G and r=s, OF Inst.prems(1) extended])
  show ?case by (rule paper_back_Inst_translation[where G=G and r=r, OF Inst.prems(1) P Q Inst.prems(2) rule_IH])
qed

lemma paper_reverse_srename_id:
  "srename id A = A"
proof -
  have lifted: "lift_ren (\<lambda>n. n) = (\<lambda>n. n)"
    by (rule ext, rename_tac n, case_tac n) simp_all
  show ?thesis by (induction A) (simp_all only: srename.simps id_def lifted)
qed

corollary pH_closed_to_paper_global_H:
  assumes derivation: "pH_proves \<Sigma> [] A" and rich: "sg_rich G"
  shows "paper_global_H \<Sigma> G (pterm_to_paper A)"
proof -
  have map: "G (id n) = \<rho>" if "lookup [] n = Some \<rho>" for n \<rho>
    using that by (simp add: lookup_def)
  have translated: "paper_global_H \<Sigma> G (srename id (pterm_to_paper A))"
    by (rule pH_to_paper_global_H[where G=G and r=id, OF derivation rich map])
  show ?thesis using translated by (simp only: paper_reverse_srename_id)
qed

end
