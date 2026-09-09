theory Bacon_Source_Closing_Proof_Transport
  imports Bacon_Source_Closing_Structure
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Theorem_Substitution
begin

section \<open>Closing transports target H proofs by typed renaming\<close>

text \<open>
  Translation commutes with closing vₙ: ⟦closeₙ(A)⟧ is obtained by
  sending target slot n to 0 and every other slot k to k + 1.
  If n is absent from P, this is simply the target shift of ⟦P⟧.
  Source role: finite-frame preservation of Bacon–Dorr Figure 2 Gen and
  Inst, p.8; the source remains the fixed global variable stock.

  Isabelle representation: paper_target_H_close reuses the proved
  pH_proves_prename theorem with the explicit sclose_lookup map.  Its input
  is a target H proof of the literal source translation.  It does not assume
  that a whole paper_global_H derivation has already been translated, and
  it does not substitute model truth for proof transport.  No source
  connective is replaced by primitive PImp in these equations.
\<close>

lemma paper_to_pterm_close:
  "paper_to_pterm (sclose n A) =
    prename (\<lambda>k. if k = n then 0 else Suc k) (paper_to_pterm A)"
  by (simp only: sclose_def paper_to_pterm_rename)

lemma paper_to_pterm_close_fresh:
  assumes fresh: "n \<notin> sfv A"
  shows "paper_to_pterm (sclose n A) = pshift (paper_to_pterm A)"
  by (simp only: sclose_fresh_eq_sshift[OF fresh] paper_to_pterm_shift)

lemma paper_target_H_rename:
  assumes derivation: "pH_proves \<Sigma> \<Gamma> (paper_to_pterm A)"
    and ren: "\<And>k \<rho>. lookup \<Gamma> k = Some \<rho> \<Longrightarrow> lookup \<Delta> (r k) = Some \<rho>"
  shows "pH_proves \<Sigma> \<Delta> (paper_to_pterm (srename r A))"
proof -
  have target: "pH_proves \<Sigma> \<Delta> (prename r (paper_to_pterm A))"
    by (rule pH_proves_prename[where r=r, OF derivation ren])
  show ?thesis using target by (simp only: paper_to_pterm_rename)
qed

theorem paper_target_H_close:
  assumes derivation: "pH_proves \<Sigma> \<Gamma> (paper_to_pterm A)"
    and variable: "lookup \<Gamma> n = Some \<sigma>"
  shows "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (paper_to_pterm (sclose n A))"
proof -
  have ren: "lookup (\<sigma> # \<Gamma>) (if k = n then 0 else Suc k) = Some \<rho>"
    if index: "lookup \<Gamma> k = Some \<rho>" for k \<rho>
    by (rule sclose_lookup[OF variable index])
  have target: "pH_proves \<Sigma> (\<sigma> # \<Gamma>)
    (prename (\<lambda>k. if k = n then 0 else Suc k) (paper_to_pterm A))"
    by (rule pH_proves_prename[where r="\<lambda>k. if k = n then 0 else Suc k", OF derivation ren])
  show ?thesis using target by (simp only: paper_to_pterm_close)
qed

end
