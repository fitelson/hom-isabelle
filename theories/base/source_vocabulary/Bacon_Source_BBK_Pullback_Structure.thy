theory Bacon_Source_BBK_Pullback_Structure
  imports Bacon_Source_BBK_Interface Bacon_Source_Logical_Applications
begin

section \<open>Structural clauses of the target-to-source interpretation\<close>

text \<open>
  Interpret a paper term A by the target denotation of its translation:
  ⟦A⟧ᴾᵍ := ⟦tr(A)⟧ᵀᵍ. The domains and valuation are unchanged.
  Source: Bacon–Dorr Definition 3.1(i–ii), pp.43–44.

  Isabelle representation: in an existing pbbk_model, paper_target_denote
  is the displayed pullback. Typing/signature preservation, literal
  application translation, free-slot correspondence, and guarded conversion
  preservation verify the structural fields of paper_db_bbk_structure.

  Status: finite-frame structural lemmas only. Truth clauses and locale
  interpretation are not supplied here. No named-model equivalence,
  Functionality, full function spaces, proposition collapse, or identity
  between primitive and defined implication is asserted.
\<close>

context pbbk_model
begin

definition paper_target_denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'c paper_term \<Rightarrow> 'v" where
  "paper_target_denote g A = denote g (paper_to_pterm A)"

lemma paper_target_domain_nonempty:
  "domain \<sigma> \<noteq> {}"
  by (rule domain_nonempty)

lemma paper_target_denote_type:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "paper_target_denote g A \<in> domain \<sigma>"
proof -
  note target = iffD2[OF paper_to_pterm_language_iff language, unfolded pterm_in_language_def]
  show ?thesis unfolding paper_target_denote_def
    by (rule denote_type[OF conjunct1[OF target] conjunct2[OF target] env])
qed

lemma paper_target_denote_var:
  assumes index: "lookup \<Gamma> n = Some \<sigma>" and env: "pbbk_env_typed domain \<Gamma> g"
  shows "paper_target_denote g (SVar n) = g n"
  unfolding paper_target_denote_def sterm_translation.simps
  by (rule denote_var[OF index env])

lemma paper_target_denote_application_cong:
  fixes F A H B :: "'c paper_term"
  assumes F: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> \<tau>)"
    and A: "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>"
    and H: "sterm_in_language paper_logical_type signature \<Delta> H (Arr \<sigma> \<tau>)"
    and B: "sterm_in_language paper_logical_type signature \<Delta> B \<sigma>"
    and env_g: "pbbk_env_typed domain \<Gamma> g"
    and env_h: "pbbk_env_typed domain \<Delta> h"
    and function_eq: "paper_target_denote g F = paper_target_denote h H"
    and argument_eq: "paper_target_denote g A = paper_target_denote h B"
  shows "paper_target_denote g (SApp F A) = paper_target_denote h (SApp H B)"
proof -
  note ft = iffD2[OF paper_to_pterm_language_iff F, unfolded pterm_in_language_def]
  note at = iffD2[OF paper_to_pterm_language_iff A, unfolded pterm_in_language_def]
  note ht = iffD2[OF paper_to_pterm_language_iff H, unfolded pterm_in_language_def]
  note bt = iffD2[OF paper_to_pterm_language_iff B, unfolded pterm_in_language_def]
  have left_names: "pterm_in_signature signature (PApp (paper_to_pterm F) (paper_to_pterm A))"
    using conjunct2[OF ft] conjunct2[OF at] by simp
  have right_names: "pterm_in_signature signature (PApp (paper_to_pterm H) (paper_to_pterm B))"
    using conjunct2[OF ht] conjunct2[OF bt] by simp
  show ?thesis unfolding paper_target_denote_def sterm_translation.simps
    by (rule denote_application_cong[OF conjunct1[OF ft] conjunct1[OF at]
      conjunct1[OF ht] conjunct1[OF bt] left_names right_names env_g env_h
      function_eq[unfolded paper_target_denote_def] argument_eq[unfolded paper_target_denote_def]])
qed

lemma paper_target_denote_locality:
  assumes first: "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>"
    and second: "sterm_in_language paper_logical_type signature \<Delta> A \<sigma>"
    and env_g: "pbbk_env_typed domain \<Gamma> g"
    and env_h: "pbbk_env_typed domain \<Delta> h"
    and agrees: "\<And>n. n \<in> sfv A \<Longrightarrow> g n = h n"
  shows "paper_target_denote g A = paper_target_denote h A"
proof -
  note first_target = iffD2[OF paper_to_pterm_language_iff first, unfolded pterm_in_language_def]
  note second_target = iffD2[OF paper_to_pterm_language_iff second, unfolded pterm_in_language_def]
  have target_agreement: "\<And>n. n \<in> pbbk_fv (paper_to_pterm A) \<Longrightarrow> g n = h n"
  proof -
    fix n
    assume member: "n \<in> pbbk_fv (paper_to_pterm A)"
    have source_member: "n \<in> sfv A" using member by (simp only: paper_to_pterm_fv)
    show "g n = h n" by (rule agrees[OF source_member])
  qed
  show ?thesis unfolding paper_target_denote_def
    by (rule denote_locality[OF conjunct1[OF first_target] conjunct1[OF second_target]
      conjunct2[OF first_target] env_g env_h target_agreement])
qed

lemma paper_target_denote_beta_eta:
  assumes conversion: "sbeta_eta_equiv_in_signature paper_logical_type signature \<Gamma> \<sigma> A B"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "paper_target_denote g A = paper_target_denote g B"
proof -
  have target: "pbeta_eta_equiv_in_signature signature \<Gamma> \<sigma> (paper_to_pterm A) (paper_to_pterm B)"
    by (rule paper_to_pterm_conversion[OF conversion])
  note fields = pbeta_eta_equiv_in_signature_data[OF target]
  note names = conjunct2[OF conjunct2[OF fields]]
  show ?thesis unfolding paper_target_denote_def
    by (rule denote_beta_eta[OF target conjunct1[OF names] conjunct2[OF names] env])
qed

subsection \<open>The separately stated renaming-coherence extension\<close>

text \<open>
  Renaming free slots preserves denotation under the corresponding
  assignment change. This is the explicit de Bruijn coherence extension
  in paper_db_bbk_model, not an added clause attributed to the printed
  list in Definition 3.1.

  Isabelle representation: the target pbbk_model already assumes this
  injective-renaming property. Translation commutes literally with that
  renaming, so its pullback satisfies the same property.
  Status: verification of the separate extension; no derivation of
  renaming coherence from the weaker paper_db_bbk_structure is claimed.
\<close>

lemma paper_target_denote_rename:
  assumes language: "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>"
    and injective: "inj r"
    and env: "pbbk_env_typed domain \<Delta> g"
    and types: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "paper_target_denote g (srename r A) = paper_target_denote (\<lambda>n. g (r n)) A"
proof -
  note target = iffD2[OF paper_to_pterm_language_iff language, unfolded pterm_in_language_def]
  have renamed: "denote g (prename r (paper_to_pterm A)) = denote (\<lambda>n. g (r n)) (paper_to_pterm A)"
    by (rule denote_rename[where \<Gamma>=\<Gamma> and \<Delta>=\<Delta> and r=r and g=g
      and M="paper_to_pterm A", OF conjunct1[OF target] conjunct2[OF target] injective env types])
  show ?thesis using renamed by (simp only: paper_target_denote_def paper_to_pterm_rename)
qed

end

end
