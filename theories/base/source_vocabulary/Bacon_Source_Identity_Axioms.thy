theory Bacon_Source_Identity_Axioms
  imports Bacon_Source_Quantifier_Axioms
begin

section \<open>Literal source reflexivity and Leibniz's Law\<close>

text \<open>
  Ref is A =σ A; LL is (A =σ B) → (FA → FB), with A,B:σ and
  F:σ → t (Bacon–Dorr Figure 2, p. 8).

  Isabelle representation: identity is a saturated source logical constant,
  and both source arrows retain Figure 1's literal λ-definition.
  The target LL theorem first yields a material consequent by PC.  Only
  genuine β conversion then restores the inner literal source implication;
  the final outer arrow uses the theoremhood bridge.

  Status: finite-frame target proofs of these source axiom instances.
  No identity between primitive PImp and the source arrow is used.
\<close>

lemma paper_source_eq_language:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B \<sigma>"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (SApp (SApp (SLogical (SEq \<sigma>)) A) B) Prop"
proof -
  have head: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (SLogical (SEq \<sigma>)) (Arr \<sigma> (Arr \<sigma> Prop))"
    using paper_source_logical_language[where l="SEq \<sigma>"] by simp
  show ?thesis by (rule paper_source_app_language[OF paper_source_app_language[OF head A] B])
qed

lemma paper_source_imp_language:
  fixes A B :: "'c paper_term"
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_imp A B) Prop"
proof -
  note ad = A[unfolded sterm_in_language_def]
  note bd = B[unfolded sterm_in_language_def]
  have typed: "has_stype paper_logical_type \<Gamma> (paper_imp A B) Prop"
    by (rule paper_imp_type[OF conjunct1[OF ad] conjunct1[OF bd]])
  have names: "sterm_in_signature \<Sigma> (paper_imp A B)"
    using conjunct2[OF ad] conjunct2[OF bd] by simp
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF typed names])
qed

theorem paper_Ref_translation:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
  shows "pH_proves \<Sigma> \<Gamma>
    (paper_to_pterm (SApp (SApp (SLogical (SEq \<sigma>)) A) A))"
proof -
  note target = iffD2[OF paper_to_pterm_language_iff A, unfolded pterm_in_language_def]
  have ref: "pH_proves \<Sigma> \<Gamma> (PEq \<sigma> (paper_to_pterm A) (paper_to_pterm A))"
    by (rule pH_proves.Ref[OF conjunct1[OF target] conjunct2[OF target]])
  show ?thesis by (rule source_pH_conversion_backward[OF paper_eq_application[OF A A] ref])
qed

theorem paper_LL_translation:
  fixes A B F :: "'c paper_term"
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B \<sigma>"
    and F: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm
    (paper_imp (SApp (SApp (SLogical (SEq \<sigma>)) A) B) (paper_imp (SApp F A) (SApp F B))))"
proof -
  let ?E = "SApp (SApp (SLogical (SEq \<sigma>)) A) B"
  let ?FA = "SApp F A"
  let ?FB = "SApp F B"
  let ?I = "paper_imp ?FA ?FB"
  let ?Eq = "PEq \<sigma> (paper_to_pterm A) (paper_to_pterm B)"
  let ?MI = "PDisj (PNeg (paper_to_pterm ?FA)) (paper_to_pterm ?FB)"
  note ad = iffD2[OF paper_to_pterm_language_iff A, unfolded pterm_in_language_def]
  note bd = iffD2[OF paper_to_pterm_language_iff B, unfolded pterm_in_language_def]
  note fd = iffD2[OF paper_to_pterm_language_iff F, unfolded pterm_in_language_def]
  note fa_l = paper_source_app_language[OF F A]
  note fb_l = paper_source_app_language[OF F B]
  note eq_l = paper_source_eq_language[OF A B]
  note inner_l = paper_source_imp_language[OF fa_l fb_l]
  note fa_t = iffD2[OF paper_to_pterm_language_iff fa_l]
  note fb_t = iffD2[OF paper_to_pterm_language_iff fb_l]
  note inner_t = iffD2[OF paper_to_pterm_language_iff inner_l]
  note eq_conv = paper_eq_application[OF A B]
  note inner_conv = paper_imp_application[OF fa_l fb_l]
  note eq_t = source_conversion_right_language[OF eq_conv]
  have raw: "pH_proves \<Sigma> \<Gamma>
    (PImp ?Eq (PImp (paper_to_pterm ?FA) (paper_to_pterm ?FB)))"
    using pH_proves.LL[OF conjunct1[OF ad] conjunct1[OF bd] conjunct1[OF fd]
      conjunct2[OF ad] conjunct2[OF bd] conjunct2[OF fd]]
    by (simp only: sterm_translation.simps)
  have material_language: "pterm_in_language \<Sigma> \<Gamma> (PImp ?Eq ?MI) Prop"
    by (rule source_target_imp_language[OF eq_t source_target_material_imp_language[OF fa_t fb_t]])
  have material: "pH_proves \<Sigma> \<Gamma> (PImp ?Eq ?MI)"
  proof (rule source_pH_PC_consequence[OF raw material_language])
    show "\<And>v. pprop_eval v (PImp ?Eq (PImp (paper_to_pterm ?FA) (paper_to_pterm ?FB))) \<Longrightarrow>
      pprop_eval v (PImp ?Eq ?MI)"
      by (simp only: pprop_eval.simps; blast)
  qed
  note first = source_conversion_Imp_left[OF eq_conv inner_t]
  note second = source_conversion_Imp_right[OF inner_conv eq_t]
  have literal_primitive: "pH_proves \<Sigma> \<Gamma>
    (PImp (paper_to_pterm ?E) (paper_to_pterm ?I))"
    by (rule source_pH_conversion_backward[
      OF pbeta_eta_equiv_in_signature.Trans[OF first second] material])
  show ?thesis by (rule iffD2[OF paper_imp_translation_proves_iff[OF eq_l inner_l] literal_primitive])
qed

end
