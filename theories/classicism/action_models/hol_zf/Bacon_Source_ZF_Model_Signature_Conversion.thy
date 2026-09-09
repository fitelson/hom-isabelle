theory Bacon_Source_ZF_Model_Signature_Conversion
  imports Bacon_Source_ZF_Model_Conversion_Steps
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Signature_Conversion
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Assignment_Extension
begin

section \<open>Every intermediate R term has an adequate R-total assignment\<close>

text \<open>
  A transitive conversion chain may introduce free variables absent
  from its endpoints. We first prove invariance under an assignment
  whose domain is exactly the R-typed names. Every intermediate term
  is then adequate by its independent R typing derivation.
  Source role: C.6, p.71. No values for non-R names are required.
\<close>

lemma paper_ZF_R_total_assignment_adequate:
  assumes total: "dom g = {n. paper_R_type (G n)}"
    and language: "paper_R_in_language \<Sigma> G A \<rho>"
  shows "named_adequate g A"
  unfolding named_adequate_def
proof
  fix n
  assume free: "n \<in> named_fv A"
  have rt: "paper_R_type (G n)" by (rule paper_R_language_fv_type[OF language free])
  show "n \<in> dom g" by (simp only: total; use rt in simp)
qed

theorem paper_ZF_action_model_signature_conversion_total:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and conversion: "paper_R_beta_eta_in_signature \<Sigma> G \<rho> A B"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and total: "dom g = {n. paper_R_type (G n)}"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
    paper_ZF_action_eval Ar source target compose identity D T I G B h g"
  using conversion
proof (induction rule: paper_R_beta_eta_in_signature.induct)
  case Refl
  show ?case by (rule refl)
next
  case Beta
  show ?case by (rule paper_ZF_action_model_beta_step[
    OF model Beta.hyps(3) Beta.hyps(1,2) arrow origin typed
      paper_ZF_R_total_assignment_adequate[OF total Beta.hyps(1)]
      paper_ZF_R_total_assignment_adequate[OF total Beta.hyps(2)]])
next
  case Eta
  show ?case by (rule paper_ZF_action_model_eta_step[
    OF model Eta.hyps(3) Eta.hyps(1,2) arrow origin typed
      paper_ZF_R_total_assignment_adequate[OF total Eta.hyps(1)]
      paper_ZF_R_total_assignment_adequate[OF total Eta.hyps(2)]])
next
  case Sym
  show ?case by (rule sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule trans[OF Trans.IH])
qed

end
