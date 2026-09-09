theory Bacon_Source_Relational_Closed_Henkin_Theory
  imports Bacon_Source_Relational_Closed_Witness_Completeness
begin

section \<open>The explicit syntactic properties required of the closed Henkin theory\<close>

definition paper_R_closed_Henkin_theory ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> bool" where
  "paper_R_closed_Henkin_theory \<Omega> G M \<longleftrightarrow>
    paper_R_closed_theory \<Omega> G M \<and> paper_R_named_consistent \<Omega> G M \<and>
    (\<forall>A. paper_R_sentence \<Omega> G A \<longrightarrow> A \<in> M \<or> named_paper_not A \<in> M) \<and>
    (\<forall>A. paper_R_named_derivable \<Omega> G M A \<longrightarrow> named_fv A = {} \<longrightarrow> A \<in> M) \<and>
    paper_R_closed_constant_witness_complete \<Omega> G M"

lemma paper_R_closed_Henkin_closed:
  "paper_R_closed_Henkin_theory \<Omega> G M \<Longrightarrow> paper_R_closed_theory \<Omega> G M"
  unfolding paper_R_closed_Henkin_theory_def by blast

lemma paper_R_closed_Henkin_consistent:
  "paper_R_closed_Henkin_theory \<Omega> G M \<Longrightarrow> paper_R_named_consistent \<Omega> G M"
  unfolding paper_R_closed_Henkin_theory_def by blast

lemma paper_R_closed_Henkin_decides:
  "paper_R_closed_Henkin_theory \<Omega> G M \<Longrightarrow> paper_R_sentence \<Omega> G A \<Longrightarrow>
    A \<in> M \<or> named_paper_not A \<in> M"
  unfolding paper_R_closed_Henkin_theory_def by blast

lemma paper_R_closed_Henkin_consequence:
  "paper_R_closed_Henkin_theory \<Omega> G M \<Longrightarrow> paper_R_named_derivable \<Omega> G M A \<Longrightarrow>
    named_fv A = {} \<Longrightarrow> A \<in> M"
  unfolding paper_R_closed_Henkin_theory_def by blast

lemma paper_R_closed_Henkin_witness_complete:
  "paper_R_closed_Henkin_theory \<Omega> G M \<Longrightarrow> paper_R_closed_constant_witness_complete \<Omega> G M"
  unfolding paper_R_closed_Henkin_theory_def by blast

theorem paper_R_closed_maximal_Henkin:
  assumes maximal: "paper_R_closed_maximal_extension \<Omega> G S M" and rich: "paper_R_rich G"
    and conditionals: "\<And>\<sigma> F. paper_R_in_language \<Omega> G F (Arr \<sigma> Prop) \<Longrightarrow>
      named_fv F = {} \<Longrightarrow> \<exists>c\<in>\<Omega> \<sigma>. paper_R_witness_axiom G \<sigma> F c \<in> M"
  shows "paper_R_closed_Henkin_theory \<Omega> G M"
proof -
  have closed: "paper_R_closed_theory \<Omega> G M" by (rule paper_R_closed_maximal_theory[OF maximal])
  have consistent: "paper_R_named_consistent \<Omega> G M" by (rule paper_R_closed_maximal_consistent[OF maximal])
  have decides: "\<forall>A. paper_R_sentence \<Omega> G A \<longrightarrow> A \<in> M \<or> named_paper_not A \<in> M"
    by (intro allI impI; rule paper_R_closed_maximal_decides[OF maximal rich]; assumption)
  have consequences: "\<forall>A. paper_R_named_derivable \<Omega> G M A \<longrightarrow> named_fv A = {} \<longrightarrow> A \<in> M"
    by (intro allI impI; rule paper_R_closed_maximal_consequence[OF maximal]; assumption)
  have witnesses: "paper_R_closed_constant_witness_complete \<Omega> G M"
    by (rule paper_R_closed_witness_complete_from_conditionals[OF maximal conditionals])
  show ?thesis unfolding paper_R_closed_Henkin_theory_def
    by (rule conjI[OF closed conjI[OF consistent conjI[OF decides conjI[OF consequences witnesses]]]])
qed

end
