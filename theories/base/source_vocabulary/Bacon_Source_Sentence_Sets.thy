theory Bacon_Source_Sentence_Sets
  imports Bacon_Source_Proof_Correspondence Bacon_Source_Local_Deduction
begin

section \<open>Sets of closed sentences in the declared source language\<close>

text \<open>
  S is a set of closed sentences of ℒ(Σ). This is a language condition,
  not an assertion that S already contains H or is deductively closed.
  No finiteness or countability condition is imposed on S or its names.
  Source role: the sentence sets used in Bacon–Dorr Theorem 3.2.
\<close>

definition paper_sentence_set :: "'c ssignature \<Rightarrow> 'c paper_term set \<Rightarrow> bool" where
  "paper_sentence_set \<Sigma> S \<longleftrightarrow>
    (\<forall>A\<in>S. sterm_in_language paper_logical_type \<Sigma> [] A Prop)"

lemma paper_sentence_set_member:
  assumes sentences: "paper_sentence_set \<Sigma> S" and member: "A \<in> S"
  shows "sterm_in_language paper_logical_type \<Sigma> [] A Prop"
  by (rule bspec[OF sentences[unfolded paper_sentence_set_def] member])

lemma paper_sentence_global_language:
  assumes sentence: "sterm_in_language paper_logical_type \<Sigma> [] A Prop"
  shows "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
proof -
  have prefix: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G 0) A Prop"
    using sentence by (simp add: source_prefix_def)
  show ?thesis by (rule source_prefix_language_to_global[OF prefix])
qed

lemma paper_sentence_set_target:
  assumes sentences: "paper_sentence_set \<Sigma> S"
  shows "pH_typed_theory \<Sigma> [] (image paper_to_pterm S)"
proof (unfold pH_typed_theory_def, rule ballI)
  fix B
  assume member: "B \<in> image paper_to_pterm S"
  obtain A where eq: "B = paper_to_pterm A" and source_member: "A \<in> S"
    using member by (elim imageE)
  have language: "pterm_in_language \<Sigma> [] (paper_to_pterm A) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff paper_sentence_set_member[OF sentences source_member]])
  show "has_ptype [] B Prop \<and> pterm_in_signature \<Sigma> B"
    using language by (simp only: eq pterm_in_language_def)
qed

end
