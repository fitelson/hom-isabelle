theory Bacon_Source_Reverse_Guarded_Conversion
  imports Bacon_Source_Reverse_Conversion
begin

section \<open>Reverse translation of whole guarded conversion chains\<close>

text \<open>
  A ≡βη B in the target's declared language implies back(A) ≡βη back(B)
  in the first-class paper language. Every endpoint and every intermediate
  conversion node retains both its type and its signature guard.
  Source role: Definition 3.1(ii.d) under interpretation pullback.

  This is a syntactic theorem. It requires no H or Classicism proof, model,
  signature inhabitants, or equation identifying primitive target implication
  with the paper's defined operator.
\<close>

theorem pterm_to_paper_guarded_conversion:
  assumes conversion: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<sigma> A B"
  shows "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> \<sigma>
    (pterm_to_paper A) (pterm_to_paper B)"
  using conversion
proof (induction rule: pbeta_eta_equiv_in_signature.induct)
  case Refl
  show ?case by (rule sbeta_eta_equiv_in_signature.Refl[OF pterm_to_paper_type[OF Refl.hyps(1)]])
    (simp only: pterm_to_paper_signature_iff Refl.hyps(2))
next
  case Beta
  show ?case
    by (rule sbeta_eta_equiv_in_signature.Beta[OF
      pterm_to_paper_type[OF Beta.hyps(1)] pterm_to_paper_type[OF Beta.hyps(2)]
      _ _ pterm_to_paper_beta_step[OF Beta.hyps(5)]])
      (simp_all only: pterm_to_paper_signature_iff Beta.hyps(3,4))
next
  case Eta
  show ?case
    by (rule sbeta_eta_equiv_in_signature.Eta[OF
      pterm_to_paper_type[OF Eta.hyps(1)] pterm_to_paper_type[OF Eta.hyps(2)]
      _ _ pterm_to_paper_eta_step[OF Eta.hyps(5)]])
      (simp_all only: pterm_to_paper_signature_iff Eta.hyps(3,4))
next
  case Sym
  show ?case by (rule sbeta_eta_equiv_in_signature.Sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule sbeta_eta_equiv_in_signature.Trans[OF Trans.IH])
qed

end
