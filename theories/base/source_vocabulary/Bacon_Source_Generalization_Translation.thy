theory Bacon_Source_Generalization_Translation
  imports Bacon_Source_Binder_Conversion Bacon_Source_Closing_Proof_Transport
begin

section \<open>Moving a chosen free variable into the binder slot\<close>

text \<open>
  Gen sends P → Q to P → ∀v.Q when v is not free in P; Inst sends
  P → Q to (∃v.P) → Q when v is not free in Q
  (Bacon–Dorr Figure 2, p.8).

  Isabelle representation: lookup Γ n = Some σ fixes the chosen variable's
  type. The proved target renaming rule moves slot n to zero and shifts
  every other slot. The closing helpers retain the literal source arrow;
  the outermost theoremhood bridge exposes target PImp for Gen/Inst.

  Status: finite-frame rule transport. No semantic premise, rich-stock
  premise, or removal of an unused context slot is assumed here.
\<close>

lemma paper_target_closed_implication:
  assumes P: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> P Prop"
    and Q: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> Q Prop"
    and variable: "lookup \<Gamma> n = Some \<sigma>"
    and premise: "pH_proves \<Sigma> \<Gamma> (paper_to_pterm (paper_imp P Q))"
  shows "pH_proves \<Sigma> (\<sigma> # \<Gamma>)
    (PImp (paper_to_pterm (sclose n P)) (paper_to_pterm (sclose n Q)))"
proof -
  note pc = sclose_language[OF P variable]
  note qc = sclose_language[OF Q variable]
  have closed: "pH_proves \<Sigma> (\<sigma> # \<Gamma>)
    (paper_to_pterm (paper_imp (sclose n P) (sclose n Q)))"
    using paper_target_H_close[OF premise variable] by (simp only: sclose_paper_imp)
  show ?thesis by (rule iffD1[OF paper_imp_translation_proves_iff[OF pc qc] closed])
qed

section \<open>Finite-frame preservation of literal source Gen\<close>

text \<open>
  ⊢H ⟦P → Q⟧ yields ⊢H ⟦P → ∀σ(λv:σ.Q)⟧,
  with v absent from P. Closing that absent variable is exactly shifting P.

  Isabelle representation: target Gen produces a direct PForall binder.
  The checked binder conversion then restores the source quantifier
  application, and the outer arrow is restored at theoremhood level.
  Status: no identity between primitive and source-defined implication.
\<close>

theorem paper_Gen_translation:
  assumes variable: "lookup \<Gamma> n = Some \<sigma>"
    and P: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> P Prop"
    and Q: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> Q Prop"
    and fresh: "n \<notin> sfv P"
    and premise: "pH_proves \<Sigma> \<Gamma> (paper_to_pterm (paper_imp P Q))"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm
    (paper_imp P (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> (sclose n Q)))))"
proof -
  note pl = iffD2[OF paper_to_pterm_language_iff P]
  note pd = pl[unfolded pterm_in_language_def]
  note qc = sclose_language[OF Q variable]
  note qd = iffD2[OF paper_to_pterm_language_iff qc, unfolded pterm_in_language_def]
  have lifted: "pH_proves \<Sigma> (\<sigma> # \<Gamma>)
    (PImp (pshift (paper_to_pterm P)) (paper_to_pterm (sclose n Q)))"
    using paper_target_closed_implication[OF P Q variable premise]
    by (simp only: sclose_fresh_eq_sshift[OF fresh] paper_to_pterm_shift)
  have generalized: "pH_proves \<Sigma> \<Gamma>
    (PImp (paper_to_pterm P) (PForall \<sigma> (paper_to_pterm (sclose n Q))))"
    by (rule pH_proves.Gen[OF conjunct1[OF pd] conjunct1[OF qd]
      conjunct2[OF pd] conjunct2[OF qd] lifted])
  have head: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (SLogical (SAll \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_source_logical_language[where l="SAll \<sigma>"] by simp
  note abstraction = paper_binder_abstraction_language[OF qc]
  note quantified = paper_source_app_language[OF head abstraction]
  note conversion = source_conversion_Imp_right[OF paper_all_binder_conversion[OF qc] pl]
  have literal_quantifier: "pH_proves \<Sigma> \<Gamma>
    (PImp (paper_to_pterm P)
      (paper_to_pterm (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> (sclose n Q)))))"
    by (rule source_pH_conversion_backward[OF conversion generalized])
  show ?thesis by (rule iffD2[OF paper_imp_translation_proves_iff[OF P quantified] literal_quantifier])
qed

section \<open>Finite-frame preservation of literal source Inst\<close>

text \<open>
  ⊢H ⟦P → Q⟧ yields ⊢H ⟦(∃σ(λv:σ.P)) → Q⟧,
  with v absent from Q. The same closing operation now leaves Q shifted.

  Isabelle representation: apply target Inst, restore the literal existential
  application by β conversion, and restore the source arrow by its outermost
  theoremhood bridge.
  Status: finite-frame preservation only; whole-proof support management
  for the global source relation remains a separate induction.
\<close>

theorem paper_Inst_translation:
  assumes variable: "lookup \<Gamma> n = Some \<sigma>"
    and P: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> P Prop"
    and Q: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> Q Prop"
    and fresh: "n \<notin> sfv Q"
    and premise: "pH_proves \<Sigma> \<Gamma> (paper_to_pterm (paper_imp P Q))"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm
    (paper_imp (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (sclose n P))) Q))"
proof -
  note ql = iffD2[OF paper_to_pterm_language_iff Q]
  note qd = ql[unfolded pterm_in_language_def]
  note pc = sclose_language[OF P variable]
  note pd = iffD2[OF paper_to_pterm_language_iff pc, unfolded pterm_in_language_def]
  have lifted: "pH_proves \<Sigma> (\<sigma> # \<Gamma>)
    (PImp (paper_to_pterm (sclose n P)) (pshift (paper_to_pterm Q)))"
    using paper_target_closed_implication[OF P Q variable premise]
    by (simp only: sclose_fresh_eq_sshift[OF fresh] paper_to_pterm_shift)
  have instantiated: "pH_proves \<Sigma> \<Gamma>
    (PImp (PExists \<sigma> (paper_to_pterm (sclose n P))) (paper_to_pterm Q))"
    by (rule pH_proves.Inst[OF conjunct1[OF pd] conjunct1[OF qd]
      conjunct2[OF pd] conjunct2[OF qd] lifted])
  have head: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (SLogical (SEx \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_source_logical_language[where l="SEx \<sigma>"] by simp
  note abstraction = paper_binder_abstraction_language[OF pc]
  note quantified = paper_source_app_language[OF head abstraction]
  note conversion = source_conversion_Imp_left[OF paper_ex_binder_conversion[OF pc] ql]
  have literal_quantifier: "pH_proves \<Sigma> \<Gamma>
    (PImp (paper_to_pterm (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> (sclose n P))))
      (paper_to_pterm Q))"
    by (rule source_pH_conversion_backward[OF conversion instantiated])
  show ?thesis by (rule iffD2[OF paper_imp_translation_proves_iff[OF quantified Q] literal_quantifier])
qed

end
