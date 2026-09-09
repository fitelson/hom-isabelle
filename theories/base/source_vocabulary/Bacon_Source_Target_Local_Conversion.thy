theory Bacon_Source_Target_Local_Conversion
  imports Bacon_Source_Proof_Connectives
    "Bacon_Parametric_Signature_Development.Bacon_Parametric_Local_Derivability"
begin

section \<open>A formula biconditional for literal source implication\<close>

text \<open>
  For source formulas A,B ∈ ℒ(Σ), target H proves
  tr(A → B) ↔ (tr(A) → tr(B)).  The left arrow is Figure 1's
  literal λ-defined source operation; the right arrow is target PImp.
  First β-normalize the literal formula to ¬tr(A) ∨ tr(B), then use PC
  and transitivity of formula biconditionals.
  Sources: Bacon--Dorr Figures 1–2, pp.6–8.

  Isabelle representation.  PObjIff is a target formula, not PEq.
  Status.  The result supplies a theorem usable under undischarged local
  assumptions.  It is stronger than a bare equivalence of theoremhood
  predicates, but does not identify the implication operators or license
  replacement in arbitrary intensional contexts.
\<close>

theorem paper_imp_translation_formula_iff:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
  shows "pH_proves \<Sigma> \<Gamma> (PObjIff (paper_to_pterm (paper_imp A B))
    (PImp (paper_to_pterm A) (paper_to_pterm B)))"
proof -
  let ?L = "paper_to_pterm (paper_imp A B)"
  let ?M = "PDisj (PNeg (paper_to_pterm A)) (paper_to_pterm B)"
  let ?I = "PImp (paper_to_pterm A) (paper_to_pterm B)"
  have A_target: "pterm_in_language \<Sigma> \<Gamma> (paper_to_pterm A) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff A])
  have B_target: "pterm_in_language \<Sigma> \<Gamma> (paper_to_pterm B) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff B])
  have conversion: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop ?L ?M"
    by (rule paper_imp_application[OF A B])
  have L_language: "pterm_in_language \<Sigma> \<Gamma> ?L Prop"
    by (rule source_conversion_left_language[OF conversion])
  have M_language: "pterm_in_language \<Sigma> \<Gamma> ?M Prop"
    by (rule source_conversion_right_language[OF conversion])
  have I_language: "pterm_in_language \<Sigma> \<Gamma> ?I Prop"
    by (rule source_target_imp_language[OF A_target B_target])
  have converted: "pH_proves \<Sigma> \<Gamma> (PObjIff ?L ?M)"
    by (rule source_conversion_formula_iff[OF conversion])
  have material: "pH_proves \<Sigma> \<Gamma> (PObjIff ?M ?I)"
  proof (rule source_pH_PC)
    show "has_ptype \<Gamma> (PObjIff ?M ?I) Prop"
      using M_language I_language unfolding pterm_in_language_def
      by (auto intro: has_ptype.PConj has_ptype.PImp)
    show "pterm_in_signature \<Sigma> (PObjIff ?M ?I)"
      using M_language I_language unfolding pterm_in_language_def by simp
    show "\<And>v. pprop_eval v (PObjIff ?M ?I)" by simp
  qed
  show ?thesis by (rule source_pH_iff_trans[OF L_language M_language I_language converted material])
qed

section \<open>Formula biconditionals transport target set derivability\<close>

text \<open>
  A theorem M ↔ N permits Σ;Γ;S ⊢H M to be replaced by
  Σ;Γ;S ⊢H N, and conversely.  S may be infinite: the existing
  pH_set_derivable relation retains finite proof support.
  Isabelle representation.  The biconditional is projected to a PImp
  theorem by PC and MP, lifted by pH_set_Theorem, and applied by pH_set_MP.
  Status.  No deduction, quantifier, or equivalence rule is applied to
  the undischarged assumptions S.
\<close>

lemma source_pH_set_formula_iff_forward:
  assumes M: "pterm_in_language \<Sigma> \<Gamma> M Prop"
    and N: "pterm_in_language \<Sigma> \<Gamma> N Prop"
    and equivalent: "pH_proves \<Sigma> \<Gamma> (PObjIff M N)"
    and derivation: "pH_set_derivable \<Sigma> \<Gamma> S M"
  shows "pH_set_derivable \<Sigma> \<Gamma> S N"
proof -
  have projection: "pH_proves \<Sigma> \<Gamma> (PImp (PObjIff M N) (PImp M N))"
  proof (rule source_pH_PC)
    show "has_ptype \<Gamma> (PImp (PObjIff M N) (PImp M N)) Prop"
      using M N unfolding pterm_in_language_def
      by (auto intro: has_ptype.PConj has_ptype.PImp)
    show "pterm_in_signature \<Sigma> (PImp (PObjIff M N) (PImp M N))"
      using M N unfolding pterm_in_language_def by simp
    show "\<And>v. pprop_eval v (PImp (PObjIff M N) (PImp M N))"
      by (simp only: pprop_eval.simps; blast)
  qed
  have implication: "pH_proves \<Sigma> \<Gamma> (PImp M N)"
    by (rule source_pH_MP[OF equivalent projection])
  show ?thesis by (rule pH_set_MP[OF derivation pH_set_Theorem[OF implication]])
qed

lemma source_pH_set_formula_iff_backward:
  assumes M: "pterm_in_language \<Sigma> \<Gamma> M Prop"
    and N: "pterm_in_language \<Sigma> \<Gamma> N Prop"
    and equivalent: "pH_proves \<Sigma> \<Gamma> (PObjIff M N)"
    and derivation: "pH_set_derivable \<Sigma> \<Gamma> S N"
  shows "pH_set_derivable \<Sigma> \<Gamma> S M"
  by (rule source_pH_set_formula_iff_forward[OF N M
    source_pH_iff_sym[OF M N equivalent] derivation])

lemma source_pH_set_conversion_forward:
  assumes conversion: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop M N"
    and derivation: "pH_set_derivable \<Sigma> \<Gamma> S M"
  shows "pH_set_derivable \<Sigma> \<Gamma> S N"
  by (rule source_pH_set_formula_iff_forward[OF source_conversion_left_language[OF conversion]
    source_conversion_right_language[OF conversion] source_conversion_formula_iff[OF conversion] derivation])

lemma source_pH_set_conversion_backward:
  assumes conversion: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop M N"
    and derivation: "pH_set_derivable \<Sigma> \<Gamma> S N"
  shows "pH_set_derivable \<Sigma> \<Gamma> S M"
  by (rule source_pH_set_formula_iff_backward[OF source_conversion_left_language[OF conversion]
    source_conversion_right_language[OF conversion] source_conversion_formula_iff[OF conversion] derivation])

theorem paper_imp_translation_set_iff:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
  shows "pH_set_derivable \<Sigma> \<Gamma> S (paper_to_pterm (paper_imp A B)) \<longleftrightarrow>
    pH_set_derivable \<Sigma> \<Gamma> S (PImp (paper_to_pterm A) (paper_to_pterm B))"
proof -
  let ?L = "paper_to_pterm (paper_imp A B)"
  let ?I = "PImp (paper_to_pterm A) (paper_to_pterm B)"
  have L_language: "pterm_in_language \<Sigma> \<Gamma> ?L Prop"
    by (rule source_conversion_left_language[OF paper_imp_application[OF A B]])
  have A_target: "pterm_in_language \<Sigma> \<Gamma> (paper_to_pterm A) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff A])
  have B_target: "pterm_in_language \<Sigma> \<Gamma> (paper_to_pterm B) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff B])
  have I_language: "pterm_in_language \<Sigma> \<Gamma> ?I Prop"
    by (rule source_target_imp_language[OF A_target B_target])
  have equivalent: "pH_proves \<Sigma> \<Gamma> (PObjIff ?L ?I)"
    by (rule paper_imp_translation_formula_iff[OF A B])
  show ?thesis
  proof
    assume "pH_set_derivable \<Sigma> \<Gamma> S ?L"
    then show "pH_set_derivable \<Sigma> \<Gamma> S ?I"
      by (rule source_pH_set_formula_iff_forward[OF L_language I_language equivalent])
  next
    assume "pH_set_derivable \<Sigma> \<Gamma> S ?I"
    then show "pH_set_derivable \<Sigma> \<Gamma> S ?L"
      by (rule source_pH_set_formula_iff_backward[OF L_language I_language equivalent])
  qed
qed

corollary paper_set_MP_translation:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    and first: "pH_set_derivable \<Sigma> \<Gamma> S (paper_to_pterm A)"
    and second: "pH_set_derivable \<Sigma> \<Gamma> S (paper_to_pterm (paper_imp A B))"
  shows "pH_set_derivable \<Sigma> \<Gamma> S (paper_to_pterm B)"
proof -
  have implication: "pH_set_derivable \<Sigma> \<Gamma> S (PImp (paper_to_pterm A) (paper_to_pterm B))"
    by (rule iffD1[OF paper_imp_translation_set_iff[OF A B] second])
  show ?thesis by (rule pH_set_MP[OF first implication])
qed

end
