theory Bacon_Source_Reverse_Quantifier_Axioms
  imports Bacon_Source_Reverse_Identity_Axioms Bacon_Source_Global_Proof_Basics
    Bacon_Source_Reverse_Conversion Bacon_Source_Renaming_Conversion
begin

section \<open>Reverse UI and EG through their literal uncontracted instances\<close>

text \<open>
  The target UI axiom ∀x:σ.A → A[T/x] reverses to the source UI
  instance ∀σ(λx.A) → (λx.A)T followed by one contextual β step.
  For EG, use (λx.A)T → ∃σ(λx.A), contracting the antecedent.
  Source: Bacon--Dorr Figure 2, pp.7–8, with Figure 1's literal arrows.

  Isabelle representation.  The map r sends each Γ-variable to a variable
  of the same type in the total stock G.  The target application redex is
  transported by pterm_to_paper_beta_step and then srename_beta_step.
  Every source proof/conversion endpoint has its whole-formula language
  guard.  Status.  No target-H proof-reflection theorem, model premise,
  richness assumption, or injectivity assumption is used.
\<close>

lemma paper_reverse_lam_language:
  assumes body: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) A Prop"
  shows "pterm_in_language \<Sigma> \<Gamma> (PLam \<sigma> A) (Arr \<sigma> Prop)"
  using body unfolding pterm_in_language_def by (auto intro: has_ptype.PLam)

lemma paper_reverse_all_language:
  assumes body: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) A Prop"
  shows "pterm_in_language \<Sigma> \<Gamma> (PForall \<sigma> A) Prop"
  using body unfolding pterm_in_language_def by (auto intro: has_ptype.PForall)

lemma paper_reverse_exists_language:
  assumes body: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) A Prop"
  shows "pterm_in_language \<Sigma> \<Gamma> (PExists \<sigma> A) Prop"
  using body unfolding pterm_in_language_def by (auto intro: has_ptype.PExists)

lemma paper_reverse_subst_language:
  assumes body: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) A Prop"
    and argument: "pterm_in_language \<Sigma> \<Gamma> T \<sigma>"
  shows "pterm_in_language \<Sigma> \<Gamma> (psubst0 T A) Prop"
proof -
  have A_type: "has_ptype (\<sigma> # \<Gamma>) A Prop"
    using body unfolding pterm_in_language_def by (rule conjunct1)
  have T_type: "has_ptype \<Gamma> T \<sigma>"
    using argument unfolding pterm_in_language_def by (rule conjunct1)
  have A_sig: "pterm_in_signature \<Sigma> A"
    using body unfolding pterm_in_language_def by (rule conjunct2)
  have T_sig: "pterm_in_signature \<Sigma> T"
    using argument unfolding pterm_in_language_def by (rule conjunct2)
  show ?thesis unfolding pterm_in_language_def
    by (rule conjI[OF psubst0_preserves_typing[OF A_type T_type]
      source_target_subst0_signature[OF A_sig T_sig]])
qed

theorem paper_reverse_UI:
  assumes body: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) A Prop"
    and argument: "pterm_in_language \<Sigma> \<Gamma> T \<sigma>"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_H \<Sigma> G
    (srename r (pterm_to_paper (PImp (PForall \<sigma> A) (psubst0 T A))))"
proof -
  let ?U = "PImp (PForall \<sigma> A) (PApp (PLam \<sigma> A) T)"
  let ?V = "PImp (PForall \<sigma> A) (psubst0 T A)"
  let ?F = "SLam \<sigma> (srename (lift_ren r) (pterm_to_paper A))"
  let ?T = "srename r (pterm_to_paper T)"
  have app_language: "pterm_in_language \<Sigma> \<Gamma> (PApp (PLam \<sigma> A) T) Prop"
    by (rule source_target_app_language[OF paper_reverse_lam_language[OF body] argument])
  have U_language: "pterm_in_language \<Sigma> \<Gamma> ?U Prop"
    by (rule source_target_imp_language[OF paper_reverse_all_language[OF body] app_language])
  have V_language: "pterm_in_language \<Sigma> \<Gamma> ?V Prop"
    by (rule source_target_imp_language[OF paper_reverse_all_language[OF body]
      paper_reverse_subst_language[OF body argument]])
  have source_language: "sgterm_in_language paper_logical_type \<Sigma> G (srename r (pterm_to_paper ?U)) Prop"
    by (rule paper_back_embedding_language[where G=G and r=r, OF U_language map])
  have target_language: "sgterm_in_language paper_logical_type \<Sigma> G (srename r (pterm_to_paper ?V)) Prop"
    by (rule paper_back_embedding_language[where G=G and r=r, OF V_language map])
  have axiom_guard: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_imp (SApp (SLogical (SAll \<sigma>)) ?F) (SApp ?F ?T)) Prop"
    using source_language by (simp only: pterm_to_paper.simps srename.simps srename_paper_imp)
  have source_proof: "paper_global_H \<Sigma> G (srename r (pterm_to_paper ?U))"
    using paper_global_H.UI[OF axiom_guard]
    by (simp only: pterm_to_paper.simps srename.simps srename_paper_imp)
  have root_step: "pcompatible_step pbeta_contract (PApp (PLam \<sigma> A) T) (psubst0 T A)"
    by (rule pcompatible_step.root[where R=pbeta_contract]) (rule pbeta_contract.beta)
  have target_step: "pcompatible_step pbeta_contract ?U ?V"
    by (rule pcompatible_step.Imp_right[OF root_step])
  have source_step: "scompatible_step sbeta_contract
    (srename r (pterm_to_paper ?U)) (srename r (pterm_to_paper ?V))"
    by (rule srename_beta_step[OF pterm_to_paper_beta_step[OF target_step]])
  show ?thesis by (rule paper_global_H_beta_forward[OF source_language target_language source_step source_proof])
qed

theorem paper_reverse_EG:
  assumes body: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) A Prop"
    and argument: "pterm_in_language \<Sigma> \<Gamma> T \<sigma>"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_H \<Sigma> G
    (srename r (pterm_to_paper (PImp (psubst0 T A) (PExists \<sigma> A))))"
proof -
  let ?U = "PImp (PApp (PLam \<sigma> A) T) (PExists \<sigma> A)"
  let ?V = "PImp (psubst0 T A) (PExists \<sigma> A)"
  let ?F = "SLam \<sigma> (srename (lift_ren r) (pterm_to_paper A))"
  let ?T = "srename r (pterm_to_paper T)"
  have app_language: "pterm_in_language \<Sigma> \<Gamma> (PApp (PLam \<sigma> A) T) Prop"
    by (rule source_target_app_language[OF paper_reverse_lam_language[OF body] argument])
  have U_language: "pterm_in_language \<Sigma> \<Gamma> ?U Prop"
    by (rule source_target_imp_language[OF app_language paper_reverse_exists_language[OF body]])
  have V_language: "pterm_in_language \<Sigma> \<Gamma> ?V Prop"
    by (rule source_target_imp_language[OF paper_reverse_subst_language[OF body argument]
      paper_reverse_exists_language[OF body]])
  have source_language: "sgterm_in_language paper_logical_type \<Sigma> G (srename r (pterm_to_paper ?U)) Prop"
    by (rule paper_back_embedding_language[where G=G and r=r, OF U_language map])
  have target_language: "sgterm_in_language paper_logical_type \<Sigma> G (srename r (pterm_to_paper ?V)) Prop"
    by (rule paper_back_embedding_language[where G=G and r=r, OF V_language map])
  have axiom_guard: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_imp (SApp ?F ?T) (SApp (SLogical (SEx \<sigma>)) ?F)) Prop"
    using source_language by (simp only: pterm_to_paper.simps srename.simps srename_paper_imp)
  have source_proof: "paper_global_H \<Sigma> G (srename r (pterm_to_paper ?U))"
    using paper_global_H.EG[OF axiom_guard]
    by (simp only: pterm_to_paper.simps srename.simps srename_paper_imp)
  have root_step: "pcompatible_step pbeta_contract (PApp (PLam \<sigma> A) T) (psubst0 T A)"
    by (rule pcompatible_step.root[where R=pbeta_contract]) (rule pbeta_contract.beta)
  have target_step: "pcompatible_step pbeta_contract ?U ?V"
    by (rule pcompatible_step.Imp_left[OF root_step])
  have source_step: "scompatible_step sbeta_contract
    (srename r (pterm_to_paper ?U)) (srename r (pterm_to_paper ?V))"
    by (rule srename_beta_step[OF pterm_to_paper_beta_step[OF target_step]])
  show ?thesis by (rule paper_global_H_beta_forward[OF source_language target_language source_step source_proof])
qed

end
