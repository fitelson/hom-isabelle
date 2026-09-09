theory Bacon_Source_Relational_Assignment_Denotation
  imports Bacon_Source_Relational_Assignment_Extension Bacon_Source_Relational_BBK_Interface
begin

section \<open>R-supported extension preserves existing interpretations\<close>

text \<open>
  The extension gᴿ is typed and adequate for every R term. If g was
  already adequate for A, then ⟦A⟧ᵍᴿ=⟦A⟧ᵍ by locality.
  Source: Definition 3.1(ii.c), p.44. This permits interpretation of an
  intermediate formula whose free variables were not assigned by g.
  It does not change the value of a conclusion already covered by g.

  Status: derived facts in the independent R model. The resulting
  assignment is defined exactly at R-typed names, not at every F name.
  No total-completion field, F model, or proof-theoretic rule is assumed.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_completed_assignment_typed:
  assumes typed: "named_env_typed domain stock g"
  shows "named_env_typed domain stock (paper_R_complete_assignment domain stock g)"
  by (rule paper_R_complete_assignment_typed[OF domain_nonempty typed])

lemma paper_R_completed_assignment_domain:
  assumes typed: "named_env_typed domain stock g"
  shows "dom (paper_R_complete_assignment domain stock g) = {n. paper_R_type (stock n)}"
proof -
  have old_support: "dom g \<subseteq> {n. paper_R_type (stock n)}"
  proof
    fix n
    assume defined: "n \<in> dom g"
    obtain a where assigned: "g n = Some a" using defined by blast
    have rt: "paper_R_type (stock n)" by (rule paper_R_assigned_variable_type[OF typed assigned])
    show "n \<in> {n. paper_R_type (stock n)}" using rt by simp
  qed
  show ?thesis using old_support by (auto simp: paper_R_complete_assignment_domain)
qed

theorem paper_R_completed_assignment_denote:
  assumes language: "paper_R_in_language signature stock A \<sigma>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
  shows "denote (paper_R_complete_assignment domain stock g) A = denote g A"
proof -
  have extended_typed: "named_env_typed domain stock (paper_R_complete_assignment domain stock g)"
    by (rule paper_R_completed_assignment_typed[OF typed])
  have extended_adequate: "named_adequate (paper_R_complete_assignment domain stock g) A"
    by (rule paper_R_complete_assignment_language_adequate[OF language])
  show ?thesis
  proof (rule denote_locality[OF language extended_typed typed extended_adequate adequate])
    fix n
    assume free: "n \<in> named_fv A"
    show "paper_R_complete_assignment domain stock g n = g n"
      by (rule paper_R_complete_assignment_agrees[OF adequate free])
  qed
qed

end

end
