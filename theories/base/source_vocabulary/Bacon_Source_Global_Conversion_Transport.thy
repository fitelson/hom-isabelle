theory Bacon_Source_Global_Conversion_Transport
  imports Bacon_Source_Global_Proof_Basics Bacon_Source_Variable_Embedding
    Bacon_Source_Renaming_Conversion
begin

section \<open>Global source theoremhood along a declared-language conversion\<close>

text \<open>
  If A ≡βη B at type t in ℒ(Σ), the renamed formulas have equivalent
  theoremhood in the global source calculus. Contextual β/η supplies each
  biconditional; PC and MP transport its endpoints
  (Bacon–Dorr Figure 2, p.8).

  Isabelle representation: induction on the signature-indexed source
  conversion embeds each finite-frame endpoint into G using a type-respecting
  variable map r. Renaming preserves the raw step, and source β/η proof
  transport handles it. Symmetry and transitivity then combine theoremhood
  equivalences in HOL.

  Status: source conversion transport only. No target pH theorem,
  model, full reflection theorem, injectivity, or richness assumption is
  used. Richness remains part of interpreting G as the paper's full stock.
\<close>

lemma paper_global_conversion_transport_aux:
  assumes conversion: "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> \<tau> A B"
    and is_prop: "\<tau> = Prop"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_H \<Sigma> G (srename r A) \<longleftrightarrow> paper_global_H \<Sigma> G (srename r B)"
  using conversion is_prop map
proof (induction arbitrary: G r rule: sbeta_eta_equiv_in_signature.induct)
  case Refl
  show ?case by (rule refl)
next
  case (Beta \<Gamma> A \<tau> B)
  have at: "has_stype paper_logical_type \<Gamma> A Prop"
    using Beta.hyps(1) by (simp only: Beta.prems(1))
  have bt: "has_stype paper_logical_type \<Gamma> B Prop"
    using Beta.hyps(2) by (simp only: Beta.prems(1))
  have al: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    unfolding sterm_in_language_def by (rule conjI[OF at Beta.hyps(3)])
  have bl: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    unfolding sterm_in_language_def by (rule conjI[OF bt Beta.hyps(4)])
  have ag: "sgterm_in_language paper_logical_type \<Sigma> G (srename r A) Prop"
    by (rule source_variable_embedding_language[where G=G and r=r, OF al Beta.prems(2)])
  have bg: "sgterm_in_language paper_logical_type \<Sigma> G (srename r B) Prop"
    by (rule source_variable_embedding_language[where G=G and r=r, OF bl Beta.prems(2)])
  have step: "scompatible_step sbeta_contract (srename r A) (srename r B)"
    by (rule srename_beta_step[where r=r, OF Beta.hyps(5)])
  show ?case
  proof
    assume proved: "paper_global_H \<Sigma> G (srename r A)"
    show "paper_global_H \<Sigma> G (srename r B)"
      by (rule paper_global_H_beta_forward[OF ag bg step proved])
  next
    assume proved: "paper_global_H \<Sigma> G (srename r B)"
    show "paper_global_H \<Sigma> G (srename r A)"
      by (rule paper_global_H_beta_backward[OF ag bg step proved])
  qed
next
  case (Eta \<Gamma> A \<tau> B)
  have at: "has_stype paper_logical_type \<Gamma> A Prop"
    using Eta.hyps(1) by (simp only: Eta.prems(1))
  have bt: "has_stype paper_logical_type \<Gamma> B Prop"
    using Eta.hyps(2) by (simp only: Eta.prems(1))
  have al: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    unfolding sterm_in_language_def by (rule conjI[OF at Eta.hyps(3)])
  have bl: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    unfolding sterm_in_language_def by (rule conjI[OF bt Eta.hyps(4)])
  have ag: "sgterm_in_language paper_logical_type \<Sigma> G (srename r A) Prop"
    by (rule source_variable_embedding_language[where G=G and r=r, OF al Eta.prems(2)])
  have bg: "sgterm_in_language paper_logical_type \<Sigma> G (srename r B) Prop"
    by (rule source_variable_embedding_language[where G=G and r=r, OF bl Eta.prems(2)])
  have step: "scompatible_step seta_contract (srename r A) (srename r B)"
    by (rule srename_eta_step[where r=r, OF Eta.hyps(5)])
  show ?case
  proof
    assume proved: "paper_global_H \<Sigma> G (srename r A)"
    show "paper_global_H \<Sigma> G (srename r B)"
      by (rule paper_global_H_eta_forward[OF ag bg step proved])
  next
    assume proved: "paper_global_H \<Sigma> G (srename r B)"
    show "paper_global_H \<Sigma> G (srename r A)"
      by (rule paper_global_H_eta_backward[OF ag bg step proved])
  qed
next
  case (Sym \<Gamma> \<tau> A B)
  have original: "paper_global_H \<Sigma> G (srename r A) \<longleftrightarrow>
    paper_global_H \<Sigma> G (srename r B)"
    by (rule Sym.IH[where G=G and r=r, OF Sym.prems(1,2)])
  show ?case by (rule sym[OF original])
next
  case (Trans \<Gamma> \<tau> A B C)
  have first: "paper_global_H \<Sigma> G (srename r A) \<longleftrightarrow>
    paper_global_H \<Sigma> G (srename r B)"
    by (rule Trans.IH(1)[where G=G and r=r, OF Trans.prems(1,2)])
  have second: "paper_global_H \<Sigma> G (srename r B) \<longleftrightarrow>
    paper_global_H \<Sigma> G (srename r C)"
    by (rule Trans.IH(2)[where G=G and r=r, OF Trans.prems(1,2)])
  show ?case by (rule trans[OF first second])
qed

theorem paper_global_conversion_transport:
  assumes conversion: "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> Prop A B"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_H \<Sigma> G (srename r A) \<longleftrightarrow> paper_global_H \<Sigma> G (srename r B)"
  by (rule paper_global_conversion_transport_aux[where G=G and r=r, OF conversion refl map])

lemmas paper_global_H_conversion_iff = paper_global_conversion_transport

end
