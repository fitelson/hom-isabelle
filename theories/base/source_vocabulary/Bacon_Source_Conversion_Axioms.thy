theory Bacon_Source_Conversion_Axioms
  imports Bacon_Source_Identity_Axioms
begin

section \<open>Literal biconditionals for contextual β and η\<close>

text \<open>
  Φ[(λv.A)B] ↔ Φ[A[B/v]] and Φ[λv.Fv] ↔ Φ[F] are Figure 2's
  conversion axioms (Bacon–Dorr pp. 7–8).  Φ may include binders.

  Isabelle representation: the source contextual step maps to the
  corresponding target step.  Target β/η yields PObjIff; PC derives its
  material form, and genuine conversion restores the literal Figure 1
  source biconditional.

  Status: finite-frame preservation of both axiom families, not
  replacement of arbitrary materially equivalent subterms.
\<close>

lemma paper_iff_translation_from_target:
  fixes A B :: "'c paper_term"
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    and proved: "pH_proves \<Sigma> \<Gamma> (PObjIff (paper_to_pterm A) (paper_to_pterm B))"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm (paper_iff A B))"
proof -
  let ?AB = "PDisj (PNeg (paper_to_pterm A)) (paper_to_pterm B)"
  let ?BA = "PDisj (PNeg (paper_to_pterm B)) (paper_to_pterm A)"
  note al = iffD2[OF paper_to_pterm_language_iff A]
  note bl = iffD2[OF paper_to_pterm_language_iff B]
  note ab = source_target_material_imp_language[OF al bl, unfolded pterm_in_language_def]
  note ba = source_target_material_imp_language[OF bl al, unfolded pterm_in_language_def]
  have typed: "has_ptype \<Gamma> (PConj ?AB ?BA) Prop"
    by (rule has_ptype.PConj[OF conjunct1[OF ab] conjunct1[OF ba]])
  have names: "pterm_in_signature \<Sigma> (PConj ?AB ?BA)"
    using conjunct2[OF ab] conjunct2[OF ba] by simp
  have language: "pterm_in_language \<Sigma> \<Gamma> (PConj ?AB ?BA) Prop"
    unfolding pterm_in_language_def by (rule conjI[OF typed names])
  have material: "pH_proves \<Sigma> \<Gamma> (PConj ?AB ?BA)"
  proof (rule source_pH_PC_consequence[OF proved language])
    show "\<And>v. pprop_eval v (PObjIff (paper_to_pterm A) (paper_to_pterm B)) \<Longrightarrow>
      pprop_eval v (PConj ?AB ?BA)"
      by (simp only: pprop_eval.simps; blast)
  qed
  show ?thesis by (rule source_pH_conversion_backward[OF paper_iff_application[OF A B] material])
qed

theorem paper_Beta_translation:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    and step: "scompatible_step sbeta_contract A B"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm (paper_iff A B))"
proof -
  note ad = iffD2[OF paper_to_pterm_language_iff A, unfolded pterm_in_language_def]
  note bd = iffD2[OF paper_to_pterm_language_iff B, unfolded pterm_in_language_def]
  have target_step: "pcompatible_step pbeta_contract (paper_to_pterm A) (paper_to_pterm B)"
    by (rule sterm_translation_beta_step[OF step paper_logical_translation_rename
      paper_logical_translation_subst])
  have target_proof: "pH_proves \<Sigma> \<Gamma> (PObjIff (paper_to_pterm A) (paper_to_pterm B))"
    by (rule pH_proves.Beta[OF conjunct1[OF ad] conjunct1[OF bd] target_step
      conjunct2[OF ad] conjunct2[OF bd]])
  show ?thesis by (rule paper_iff_translation_from_target[OF A B target_proof])
qed

theorem paper_Eta_translation:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    and step: "scompatible_step seta_contract A B"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm (paper_iff A B))"
proof -
  note ad = iffD2[OF paper_to_pterm_language_iff A, unfolded pterm_in_language_def]
  note bd = iffD2[OF paper_to_pterm_language_iff B, unfolded pterm_in_language_def]
  have target_step: "pcompatible_step peta_contract (paper_to_pterm A) (paper_to_pterm B)"
    by (rule sterm_translation_eta_step[OF step paper_logical_translation_rename])
  have target_proof: "pH_proves \<Sigma> \<Gamma> (PObjIff (paper_to_pterm A) (paper_to_pterm B))"
    by (rule pH_proves.Eta[OF conjunct1[OF ad] conjunct1[OF bd] target_step
      conjunct2[OF ad] conjunct2[OF bd]])
  show ?thesis by (rule paper_iff_translation_from_target[OF A B target_proof])
qed

end
