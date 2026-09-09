theory Bacon_Source_Proof_Connectives
  imports Bacon_Source_PC_Translation
begin

section \<open>Top-level implication in the source and target proof systems\<close>

text \<open>
  The paper defines A → B by applying λpq.¬p ∨ q, whereas the target
  calculus uses PImp in its inference rules. PC and MP connect the
  theoremhood of these formulas. Source: Bacon--Dorr Figures 1 and 2.

  The equivalences below concern theoremhood at the outermost formula
  level. They do not identify the two operators or license replacement
  within arbitrary intensional contexts. This is the proof-level bridge
  needed for transporting source MP, Gen, Inst, and implication axioms.
\<close>

lemma source_pH_PC_consequence:
  assumes proved: "pH_proves \<Sigma> \<Gamma> A"
    and target: "pterm_in_language \<Sigma> \<Gamma> B Prop"
    and consequence: "\<And>v. pprop_eval v A \<Longrightarrow> pprop_eval v B"
  shows "pH_proves \<Sigma> \<Gamma> B"
proof -
  have at: "has_ptype \<Gamma> A Prop" by (rule pH_proves_formula[OF proved])
  have an: "pterm_in_signature \<Sigma> A" by (rule pH_proves_in_signature[OF proved])
  have bt: "has_ptype \<Gamma> B Prop" and bn: "pterm_in_signature \<Sigma> B"
    using target unfolding pterm_in_language_def by blast+
  have bridge: "pH_proves \<Sigma> \<Gamma> (PImp A B)"
  proof (rule source_pH_PC)
    show "has_ptype \<Gamma> (PImp A B) Prop" by (rule has_ptype.PImp[OF at bt])
    show "pterm_in_signature \<Sigma> (PImp A B)" using an bn by simp
    show "\<And>v. pprop_eval v (PImp A B)"
      using consequence by (simp only: pprop_eval.simps; blast)
  qed
  show ?thesis by (rule source_pH_MP[OF proved bridge])
qed

lemma source_pH_conversion_forward:
  assumes conversion: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop A B"
    and proved: "pH_proves \<Sigma> \<Gamma> A"
  shows "pH_proves \<Sigma> \<Gamma> B"
  by (rule source_pH_conversion_backward[OF
    pbeta_eta_equiv_in_signature.Sym[OF conversion] proved])

lemma source_target_material_imp_language:
  assumes A: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    and B: "pterm_in_language \<Sigma> \<Gamma> B Prop"
  shows "pterm_in_language \<Sigma> \<Gamma> (PDisj (PNeg A) B) Prop"
  using A B unfolding pterm_in_language_def
  by (auto intro: has_ptype.PNeg has_ptype.PDisj)

lemma source_target_imp_language:
  assumes A: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    and B: "pterm_in_language \<Sigma> \<Gamma> B Prop"
  shows "pterm_in_language \<Sigma> \<Gamma> (PImp A B) Prop"
  using A B unfolding pterm_in_language_def by (auto intro: has_ptype.PImp)

lemma source_target_material_imp_proves_iff:
  assumes A: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    and B: "pterm_in_language \<Sigma> \<Gamma> B Prop"
  shows "pH_proves \<Sigma> \<Gamma> (PDisj (PNeg A) B) \<longleftrightarrow>
    pH_proves \<Sigma> \<Gamma> (PImp A B)"
proof
  assume proved: "pH_proves \<Sigma> \<Gamma> (PDisj (PNeg A) B)"
  show "pH_proves \<Sigma> \<Gamma> (PImp A B)"
    by (rule source_pH_PC_consequence[OF proved source_target_imp_language[OF A B]])
      (simp only: pprop_eval.simps; blast)
next
  assume proved: "pH_proves \<Sigma> \<Gamma> (PImp A B)"
  show "pH_proves \<Sigma> \<Gamma> (PDisj (PNeg A) B)"
    by (rule source_pH_PC_consequence[OF proved source_target_material_imp_language[OF A B]])
      (simp only: pprop_eval.simps; blast)
qed

theorem paper_imp_translation_proves_iff:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm (paper_imp A B)) \<longleftrightarrow>
    pH_proves \<Sigma> \<Gamma> (PImp (paper_to_pterm A) (paper_to_pterm B))"
proof -
  let ?M = "PDisj (PNeg (paper_to_pterm A)) (paper_to_pterm B)"
  have al: "pterm_in_language \<Sigma> \<Gamma> (paper_to_pterm A) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff A])
  have bl: "pterm_in_language \<Sigma> \<Gamma> (paper_to_pterm B) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff B])
  have conversion: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_imp A B)) ?M" by (rule paper_imp_application[OF A B])
  have converted: "pH_proves \<Sigma> \<Gamma> (paper_to_pterm (paper_imp A B)) \<longleftrightarrow>
    pH_proves \<Sigma> \<Gamma> ?M"
    using source_pH_conversion_forward[OF conversion]
      source_pH_conversion_backward[OF conversion] by blast
  show ?thesis using converted source_target_material_imp_proves_iff[OF al bl] by blast
qed

corollary paper_MP_translation:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    and first: "pH_proves \<Sigma> \<Gamma> (paper_to_pterm A)"
    and second: "pH_proves \<Sigma> \<Gamma> (paper_to_pterm (paper_imp A B))"
  shows "pH_proves \<Sigma> \<Gamma> (paper_to_pterm B)"
  by (rule source_pH_MP[OF first iffD1[OF paper_imp_translation_proves_iff[OF A B] second]])

end
