theory Bacon_Source_BBK_Closed_Soundness
  imports Bacon_Source_BBK_Model_Existence
    Bacon_Source_Vocabulary_Development.Bacon_Source_BBK_Reverse_Model
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Set_Soundness
begin

section \<open>Closed-set soundness in every independently specified source structure\<close>

text \<open>
  If S ⊢H A for sentences S,A of ℒ(Σ), every source structure that
  makes S true at g makes A true at g. Construct the reverse target model,
  translate the derivation, and recover source denotations after the source
  round trip. Source role: the soundness part of Bacon–Dorr Theorem 3.2.

  This quantifies over every independently specified finite-frame source
  structure on every semantic carrier, not just constructed canonical models.
  It is not yet the separate named-variable/adequate-assignment theorem.
  Neither richness of G nor countability is needed for this direction.
\<close>

context paper_db_bbk_structure
begin

theorem paper_db_closed_set_soundness:
  assumes sentences: "paper_sentence_set signature S"
    and conclusion: "sterm_in_language paper_logical_type signature [] A Prop"
    and derivation: "paper_global_derivable signature G S A"
    and assumed_true: "\<And>B. B \<in> S \<Longrightarrow> valuation (denote g B)"
  shows "valuation (denote g A)"
proof -
  interpret Target: pbbk_model signature domain "\<lambda>h M. denote h (pterm_to_paper M)" valuation
    by (rule paper_db_to_pbbk_model[OF paper_db_bbk_structure_axioms])
  have translated: "pH_set_derivable signature [] (image paper_to_pterm S) (paper_to_pterm A)"
    by (rule paper_closed_set_preservation[OF sentences conclusion derivation])
  have premises_true: "valuation (denote g (pterm_to_paper B))"
    if member: "B \<in> image paper_to_pterm S" for B
  proof -
    obtain C where original: "C \<in> S" and eq: "B = paper_to_pterm C" using member by auto
    have language: "sterm_in_language paper_logical_type signature [] C Prop"
      by (rule paper_sentence_set_member[OF sentences original])
    have recovery: "denote g (pterm_to_paper (paper_to_pterm C)) = denote g C"
      by (rule paper_db_roundtrip_denotation[OF language pbbk_env_empty])
    show ?thesis using assumed_true[OF original] by (simp only: eq recovery)
  qed
  have target_truth: "valuation (denote g (pterm_to_paper (paper_to_pterm A)))"
    by (rule Target.pH_set_BBK_soundness[OF translated pbbk_env_empty premises_true])
  show ?thesis using target_truth
    by (simp only: paper_db_roundtrip_denotation[OF conclusion pbbk_env_empty])
qed

corollary paper_db_closed_H_soundness:
  assumes conclusion: "sterm_in_language paper_logical_type signature [] A Prop"
    and derivation: "paper_global_H signature G A"
  shows "valuation (denote g A)"
proof -
  have sentences: "paper_sentence_set signature {}" by (simp add: paper_sentence_set_def)
  have local_proof: "paper_global_derivable signature G {} A"
    by (rule paper_global_derivable.Theorem[OF derivation])
  show ?thesis by (rule paper_db_closed_set_soundness[OF sentences conclusion local_proof]) simp
qed

end

end
