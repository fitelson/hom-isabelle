theory Bacon_Source_Relational_Henkin_Boolean_Membership
  imports Bacon_Source_Relational_Boolean_PC Bacon_Source_Relational_Closed_Henkin_Theory
    Bacon_Source_Relational_Identity_Classes
begin

section \<open>Closed Boolean terms and internal consequence closure\<close>

lemma paper_R_closed_terms_not:
  assumes first: "A \<in> paper_R_closed_terms \<Omega> G Prop"
  shows "named_paper_not A \<in> paper_R_closed_terms \<Omega> G Prop"
  using first unfolding paper_R_closed_terms_def
  by (auto simp: named_paper_primitive_fv intro: paper_R_named_not_language)

lemma paper_R_closed_terms_and:
  assumes first: "A \<in> paper_R_closed_terms \<Omega> G Prop" and second: "B \<in> paper_R_closed_terms \<Omega> G Prop"
  shows "named_paper_and A B \<in> paper_R_closed_terms \<Omega> G Prop"
  using first second unfolding paper_R_closed_terms_def
  by (auto simp: named_paper_primitive_fv intro: paper_R_named_and_language)

lemma paper_R_closed_terms_or:
  assumes first: "A \<in> paper_R_closed_terms \<Omega> G Prop" and second: "B \<in> paper_R_closed_terms \<Omega> G Prop"
  shows "named_paper_or A B \<in> paper_R_closed_terms \<Omega> G Prop"
  using first second unfolding paper_R_closed_terms_def
  by (auto simp: named_paper_primitive_fv intro: paper_R_named_or_language)

lemma paper_R_closed_Henkin_member_derivable:
  assumes Henkin: "paper_R_closed_Henkin_theory \<Omega> G M" and member: "A \<in> M"
  shows "paper_R_named_derivable \<Omega> G M A"
  by (rule paper_R_named_derivable.Assumption[OF member];
    rule paper_R_sentence_language[OF paper_R_closed_theory_member[OF paper_R_closed_Henkin_closed[OF Henkin] member]])

lemma paper_R_closed_Henkin_H_MP:
  assumes Henkin: "paper_R_closed_Henkin_theory \<Omega> G M" and member: "A \<in> M"
    and conditional: "paper_R_named_H \<Omega> G (named_paper_imp G A B)"
    and conclusion: "B \<in> paper_R_closed_terms \<Omega> G Prop"
  shows "B \<in> M"
proof -
  have derivation: "paper_R_named_derivable \<Omega> G M B"
    by (rule paper_R_named_derivable.MP[OF paper_R_closed_Henkin_member_derivable[OF Henkin member]
      paper_R_named_derivable.Theorem[OF conditional] paper_R_closed_terms_language[OF conclusion]])
  show ?thesis by (rule paper_R_closed_Henkin_consequence[
    OF Henkin derivation paper_R_closed_terms_closed[OF conclusion]])
qed

lemma paper_R_closed_Henkin_H_MP2:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and first: "A \<in> M" and second: "B \<in> M"
    and conditional: "paper_R_named_H \<Omega> G (named_paper_imp G A (named_paper_imp G B C))"
    and conclusion: "C \<in> paper_R_closed_terms \<Omega> G Prop"
  shows "C \<in> M"
proof -
  have a: "paper_R_named_derivable \<Omega> G M A" by (rule paper_R_closed_Henkin_member_derivable[OF Henkin first])
  have b: "paper_R_named_derivable \<Omega> G M B" by (rule paper_R_closed_Henkin_member_derivable[OF Henkin second])
  have cl: "paper_R_in_language \<Omega> G C Prop" by (rule paper_R_closed_terms_language[OF conclusion])
  have bl: "paper_R_in_language \<Omega> G B Prop" by (rule paper_R_named_derivable_language[OF b])
  have bc: "paper_R_named_derivable \<Omega> G M (named_paper_imp G B C)"
    by (rule paper_R_named_derivable.MP[OF a paper_R_named_derivable.Theorem[OF conditional]
      paper_R_named_paper_imp_language[OF rich bl cl]])
  have c: "paper_R_named_derivable \<Omega> G M C" by (rule paper_R_named_derivable.MP[OF b bc cl])
  show ?thesis by (rule paper_R_closed_Henkin_consequence[OF Henkin c paper_R_closed_terms_closed[OF conclusion]])
qed

section \<open>Boolean membership laws follow from native syntax, not a model\<close>

text \<open>
  For closed R propositions, ¬A∈M iff A∉M,
  A∧B∈M iff A∈M and B∈M, and A∨B∈M iff A∈M or B∈M.
  Source: the propositional step of Theorem 3.2, footnote 64, p.45.
  Negation uses closed decisions and consistency; conjunction and
  disjunction use the displayed native R-PC certificates and MP.
  No semantic R-BBK law or equality-from-truth inference is used.
\<close>

theorem paper_R_closed_Henkin_not_member:
  assumes Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and first: "A \<in> paper_R_closed_terms \<Omega> G Prop"
  shows "named_paper_not A \<in> M \<longleftrightarrow> A \<notin> M"
proof
  assume negative: "named_paper_not A \<in> M"
  show "A \<notin> M"
  proof
    assume positive: "A \<in> M"
    show False by (rule paper_R_named_consistentD[OF paper_R_closed_Henkin_consistent[OF Henkin]
      paper_R_closed_Henkin_member_derivable[OF Henkin positive]
      paper_R_closed_Henkin_member_derivable[OF Henkin negative]])
  qed
next
  assume absent: "A \<notin> M"
  have sentence: "paper_R_sentence \<Omega> G A"
    by (rule paper_R_sentenceI[OF paper_R_closed_terms_language[OF first] paper_R_closed_terms_closed[OF first]])
  show "named_paper_not A \<in> M" using paper_R_closed_Henkin_decides[OF Henkin sentence] absent by blast
qed

theorem paper_R_closed_Henkin_and_member:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and first: "A \<in> paper_R_closed_terms \<Omega> G Prop" and second: "B \<in> paper_R_closed_terms \<Omega> G Prop"
  shows "named_paper_and A B \<in> M \<longleftrightarrow> A \<in> M \<and> B \<in> M"
proof -
  have al: "paper_R_in_language \<Omega> G A Prop" by (rule paper_R_closed_terms_language[OF first])
  have bl: "paper_R_in_language \<Omega> G B Prop" by (rule paper_R_closed_terms_language[OF second])
  show ?thesis
  proof
    assume conjunction: "named_paper_and A B \<in> M"
    have a: "A \<in> M" by (rule paper_R_closed_Henkin_H_MP[
      OF Henkin conjunction paper_R_named_H_and_left[OF rich al bl] first])
    have b: "B \<in> M" by (rule paper_R_closed_Henkin_H_MP[
      OF Henkin conjunction paper_R_named_H_and_right[OF rich al bl] second])
    show "A \<in> M \<and> B \<in> M" by (rule conjI[OF a b])
  next
    assume both: "A \<in> M \<and> B \<in> M"
    show "named_paper_and A B \<in> M" by (rule paper_R_closed_Henkin_H_MP2[
      OF rich Henkin conjunct1[OF both] conjunct2[OF both] paper_R_named_H_and_intro[OF rich al bl]
        paper_R_closed_terms_and[OF first second]])
  qed
qed

theorem paper_R_closed_Henkin_or_member:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and first: "A \<in> paper_R_closed_terms \<Omega> G Prop" and second: "B \<in> paper_R_closed_terms \<Omega> G Prop"
  shows "named_paper_or A B \<in> M \<longleftrightarrow> A \<in> M \<or> B \<in> M"
proof -
  have al: "paper_R_in_language \<Omega> G A Prop" by (rule paper_R_closed_terms_language[OF first])
  have bl: "paper_R_in_language \<Omega> G B Prop" by (rule paper_R_closed_terms_language[OF second])
  have result: "named_paper_or A B \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_closed_terms_or[OF first second])
  show ?thesis
  proof
    assume disjunction: "named_paper_or A B \<in> M"
    show "A \<in> M \<or> B \<in> M"
    proof (cases "A \<in> M")
      case True
      show ?thesis by (rule disjI1[OF True])
    next
      case False
      have negative: "named_paper_not A \<in> M"
        by (rule iffD2[OF paper_R_closed_Henkin_not_member[OF Henkin first] False])
      have b: "B \<in> M" by (rule paper_R_closed_Henkin_H_MP2[
        OF rich Henkin disjunction negative paper_R_named_H_or_resolve[OF rich al bl] second])
      show ?thesis by (rule disjI2[OF b])
    qed
  next
    assume alternatives: "A \<in> M \<or> B \<in> M"
    show "named_paper_or A B \<in> M"
    proof (rule disjE[OF alternatives])
      assume a: "A \<in> M"
      show ?thesis by (rule paper_R_closed_Henkin_H_MP[OF Henkin a paper_R_named_H_or_left[OF rich al bl] result])
    next
      assume b: "B \<in> M"
      show ?thesis by (rule paper_R_closed_Henkin_H_MP[OF Henkin b paper_R_named_H_or_right[OF rich al bl] result])
    qed
  qed
qed

end
