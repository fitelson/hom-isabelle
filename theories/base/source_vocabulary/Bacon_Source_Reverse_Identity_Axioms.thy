theory Bacon_Source_Reverse_Identity_Axioms
  imports Bacon_Source_Global_PC_Embedding
begin

section \<open>Language guards for the reverse variable interpretation\<close>

text \<open>
  A target expression of ℒ(Σ), typed under Γ, becomes a globally typed
  source expression when every declared variable is sent to a variable of
  the same type in G. Nonlogical names and the signature are unchanged.

  This is language preservation only. It does not turn a target proof
  into a source proof without checking the corresponding inference rule.
\<close>

lemma paper_back_embedding_language:
  assumes language: "pterm_in_language \<Sigma> \<Gamma> A \<tau>"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "sgterm_in_language paper_logical_type \<Sigma> G (srename r (pterm_to_paper A)) \<tau>"
  by (rule source_variable_embedding_language[where G=G and r=r,
    OF pterm_to_paper_language[OF language] map])

lemma paper_back_proof_language:
  assumes derivation: "pH_proves \<Sigma> \<Gamma> A"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "sgterm_in_language paper_logical_type \<Sigma> G (srename r (pterm_to_paper A)) Prop"
  by (rule paper_back_embedding_language[where G=G and r=r,
    OF pH_proves_in_language[OF derivation] map])

section \<open>Ref and LL become their literal source axiom instances\<close>

text \<open>
  A =σ A and A =σ B → (FA → FB) are exactly the Ref and LL
  axiom families of Bacon–Dorr Figure 2. Reverse translation uses the
  first-class source identity constant and both literal defined arrows.

  Each proof below invokes the source axiom after checking its whole-formula
  language guard. No target proof-reflection theorem, source richness,
  injectivity, or model assumption is used.
\<close>

theorem paper_reverse_Ref:
  assumes language: "pterm_in_language \<Sigma> \<Gamma> (PEq \<sigma> A A) Prop"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_H \<Sigma> G (srename r (pterm_to_paper (PEq \<sigma> A A)))"
proof -
  let ?A = "srename r (pterm_to_paper A)"
  have guard: "sgterm_in_language paper_logical_type \<Sigma> G
    (SApp (SApp (SLogical (SEq \<sigma>)) ?A) ?A) Prop"
    using paper_back_embedding_language[where G=G and r=r, OF language map]
    by (simp only: pterm_to_paper.simps srename.simps)
  show ?thesis using paper_global_H.Ref[OF guard]
    by (simp only: pterm_to_paper.simps srename.simps)
qed

theorem paper_reverse_LL:
  assumes language: "pterm_in_language \<Sigma> \<Gamma>
    (PImp (PEq \<sigma> A B) (PImp (PApp F A) (PApp F B))) Prop"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_H \<Sigma> G (srename r (pterm_to_paper
    (PImp (PEq \<sigma> A B) (PImp (PApp F A) (PApp F B)))))"
proof -
  let ?A = "srename r (pterm_to_paper A)"
  let ?B = "srename r (pterm_to_paper B)"
  let ?F = "srename r (pterm_to_paper F)"
  have guard: "sgterm_in_language paper_logical_type \<Sigma> G
    (paper_imp (SApp (SApp (SLogical (SEq \<sigma>)) ?A) ?B)
      (paper_imp (SApp ?F ?A) (SApp ?F ?B))) Prop"
    using paper_back_embedding_language[where G=G and r=r, OF language map]
    by (simp only: pterm_to_paper.simps srename.simps srename_paper_imp)
  show ?thesis using paper_global_H.LL[OF guard]
    by (simp only: pterm_to_paper.simps srename.simps srename_paper_imp)
qed

end
