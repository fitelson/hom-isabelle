theory Bacon_Source_Relational_Maximal_Theory
  imports Bacon_Source_Relational_Closed_Theory Bacon_Source_Relational_Consequence_Closure
begin

section \<open>Closed consequences already belong to a maximal closed theory\<close>

text \<open>
  Maximality is among consistent sets of CLOSED R formulas. A closed
  local consequence can be inserted without losing consistency, so it
  already belongs. An open consequence is not covered by this argument.
  Source role: the closed-decision Henkin construction for Theorem 3.2,
  p.45 n.64. Neither witnesses nor a semantic model are asserted.
\<close>

lemma paper_R_sentence_not:
  assumes sentence: "paper_R_sentence \<Sigma> G A"
  shows "paper_R_sentence \<Sigma> G (named_paper_not A)"
proof (rule paper_R_sentenceI)
  show "paper_R_in_language \<Sigma> G (named_paper_not A) Prop"
    by (rule paper_R_named_not_language[OF paper_R_sentence_language[OF sentence]])
  show "named_fv (named_paper_not A) = {}"
    by (simp only: named_paper_primitive_fv; rule paper_R_sentence_closed[OF sentence])
qed

lemma paper_R_closed_maximal_member_derivable:
  assumes maximal: "paper_R_closed_maximal_extension \<Sigma> G S M" and member: "A \<in> M"
  shows "paper_R_named_derivable \<Sigma> G M A"
  by (rule paper_R_named_derivable.Assumption[OF member];
    rule paper_R_sentence_language[OF paper_R_closed_theory_member[OF paper_R_closed_maximal_theory[OF maximal] member]])

theorem paper_R_closed_maximal_consequence:
  assumes maximal: "paper_R_closed_maximal_extension \<Sigma> G S M"
    and derivation: "paper_R_named_derivable \<Sigma> G M A" and closed: "named_fv A = {}"
  shows "A \<in> M"
proof -
  have sentence: "paper_R_sentence \<Sigma> G A"
    by (rule paper_R_sentenceI[OF paper_R_named_derivable_language[OF derivation] closed])
  have closed_M: "paper_R_closed_theory \<Sigma> G M" by (rule paper_R_closed_maximal_theory[OF maximal])
  have enlarged: "paper_R_closed_theory \<Sigma> G (insert A M)"
    by (simp only: paper_R_closed_theory_insert; rule conjI[OF sentence closed_M])
  have consistent: "paper_R_named_consistent \<Sigma> G (insert A M)"
    by (rule paper_R_named_consistent_insert_derivable[OF paper_R_closed_maximal_consistent[OF maximal] derivation])
  have equality: "insert A M = M"
    by (rule paper_R_closed_maximal_eq[OF maximal subset_insertI enlarged consistent])
  show ?thesis using insertI1[of A M] by (simp only: equality)
qed

corollary paper_R_closed_maximal_membership_iff:
  assumes maximal: "paper_R_closed_maximal_extension \<Sigma> G S M" and sentence: "paper_R_sentence \<Sigma> G A"
  shows "A \<in> M \<longleftrightarrow> paper_R_named_derivable \<Sigma> G M A"
  using paper_R_closed_maximal_member_derivable[OF maximal]
    paper_R_closed_maximal_consequence[OF maximal _ paper_R_sentence_closed[OF sentence]] by blast

lemma paper_R_closed_maximal_no_contradictory_members:
  assumes maximal: "paper_R_closed_maximal_extension \<Sigma> G S M"
  shows "\<not> (A \<in> M \<and> named_paper_not A \<in> M)"
proof
  assume both: "A \<in> M \<and> named_paper_not A \<in> M"
  have positive: "paper_R_named_derivable \<Sigma> G M A"
    by (rule paper_R_closed_maximal_member_derivable[OF maximal conjunct1[OF both]])
  have negative: "paper_R_named_derivable \<Sigma> G M (named_paper_not A)"
    by (rule paper_R_closed_maximal_member_derivable[OF maximal conjunct2[OF both]])
  show False by (rule paper_R_named_consistentD[OF paper_R_closed_maximal_consistent[OF maximal] positive negative])
qed

section \<open>Exactly one of each closed formula and its negation belongs\<close>

theorem paper_R_closed_maximal_decides:
  assumes maximal: "paper_R_closed_maximal_extension \<Sigma> G S M"
    and rich: "paper_R_rich G" and sentence: "paper_R_sentence \<Sigma> G A"
  shows "A \<in> M \<or> named_paper_not A \<in> M"
proof -
  have closed_M: "paper_R_closed_theory \<Sigma> G M" by (rule paper_R_closed_maximal_theory[OF maximal])
  have negated: "paper_R_sentence \<Sigma> G (named_paper_not A)" by (rule paper_R_sentence_not[OF sentence])
  have choice: "paper_R_named_consistent \<Sigma> G (insert A M) \<or>
      paper_R_named_consistent \<Sigma> G (insert (named_paper_not A) M)"
    by (rule paper_R_named_consistent_decision_extension[
      OF rich paper_R_closed_maximal_consistent[OF maximal] paper_R_sentence_language[OF sentence]])
  have insert_member: "B \<in> M" if bs: "paper_R_sentence \<Sigma> G B"
    and bc: "paper_R_named_consistent \<Sigma> G (insert B M)" for B
  proof -
    have enlarged: "paper_R_closed_theory \<Sigma> G (insert B M)"
      by (simp only: paper_R_closed_theory_insert; rule conjI[OF bs closed_M])
    have equality: "insert B M = M" by (rule paper_R_closed_maximal_eq[OF maximal subset_insertI enlarged bc])
    show ?thesis using insertI1[of B M] by (simp only: equality)
  qed
  show ?thesis using choice insert_member[OF sentence] insert_member[OF negated] by blast
qed

corollary paper_R_closed_maximal_negation_iff:
  assumes maximal: "paper_R_closed_maximal_extension \<Sigma> G S M"
    and rich: "paper_R_rich G" and sentence: "paper_R_sentence \<Sigma> G A"
  shows "named_paper_not A \<in> M \<longleftrightarrow> A \<notin> M"
  using paper_R_closed_maximal_decides[OF maximal rich sentence]
    paper_R_closed_maximal_no_contradictory_members[OF maximal, where A=A] by blast

corollary paper_R_closed_maximal_exactly_one:
  assumes maximal: "paper_R_closed_maximal_extension \<Sigma> G S M"
    and rich: "paper_R_rich G" and sentence: "paper_R_sentence \<Sigma> G A"
  shows "(A \<in> M) \<noteq> (named_paper_not A \<in> M)"
  using paper_R_closed_maximal_negation_iff[OF maximal rich sentence] by blast

end
