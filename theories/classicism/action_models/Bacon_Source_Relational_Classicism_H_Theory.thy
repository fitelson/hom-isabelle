theory Bacon_Source_Relational_Classicism_H_Theory
  imports Bacon_Source_Relational_H_Theory_Necessitation Bacon_Source_Relational_Classicism_A3
begin

section \<open>Source-defined C instantiates the independent H-theory conditions\<close>

theorem paper_R_classicism_is_H_theory:
  "paper_R_H_theory \<Sigma> G {A. paper_R_classicism_proves \<Sigma> G A}"
proof (rule paper_R_H_theoryI)
  fix A
  assume "A \<in> {A. paper_R_classicism_proves \<Sigma> G A}"
  then have "paper_R_classicism_proves \<Sigma> G A" by simp
  then show "paper_R_in_language \<Sigma> G A Prop" by (rule paper_R_classicism_proves_language)
next
  fix A
  assume "paper_R_named_H \<Sigma> G A"
  then have "paper_R_classicism_proves \<Sigma> G A" by (rule paper_R_classicism_proves.H)
  then show "A \<in> {A. paper_R_classicism_proves \<Sigma> G A}" by simp
next
  fix A B
  assume first: "A \<in> {A. paper_R_classicism_proves \<Sigma> G A}"
    and second: "named_paper_imp G A B \<in> {A. paper_R_classicism_proves \<Sigma> G A}"
    and language: "paper_R_in_language \<Sigma> G B Prop"
  have "paper_R_classicism_proves \<Sigma> G B" using first second
    by (auto intro: paper_R_classicism_proves.MP[OF _ _ language])
  then show "B \<in> {A. paper_R_classicism_proves \<Sigma> G A}" by simp
next
  fix P Q n \<sigma>
  assume premise: "named_paper_imp G P Q \<in> {A. paper_R_classicism_proves \<Sigma> G A}"
    and variable: "G n = \<sigma>" and fresh: "n \<notin> named_fv P"
    and language: "paper_R_in_language \<Sigma> G (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))) Prop"
  have old: "paper_R_classicism_proves \<Sigma> G (named_paper_imp G P Q)" using premise by simp
  have "paper_R_classicism_proves \<Sigma> G (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)))"
    by (rule paper_R_classicism_proves.Gen[OF old variable fresh language])
  then show "named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)) \<in> {A. paper_R_classicism_proves \<Sigma> G A}" by simp
next
  fix P Q n \<sigma>
  assume premise: "named_paper_imp G P Q \<in> {A. paper_R_classicism_proves \<Sigma> G A}"
    and variable: "G n = \<sigma>" and fresh: "n \<notin> named_fv Q"
    and language: "paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop"
  have old: "paper_R_classicism_proves \<Sigma> G (named_paper_imp G P Q)" using premise by simp
  have "paper_R_classicism_proves \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q)"
    by (rule paper_R_classicism_proves.Inst[OF old variable fresh language])
  then show "named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q \<in> {A. paper_R_classicism_proves \<Sigma> G A}" by simp
qed

theorem paper_R_classicism_is_PE_closed:
  assumes rich: "paper_R_rich G"
  shows "paper_R_PE_closed \<Sigma> G {A. paper_R_classicism_proves \<Sigma> G A}"
  unfolding paper_R_PE_closed_def
  by (intro allI impI; simp only: mem_Collect_eq;
    rule paper_R_classicism_propositional_equivalence[OF rich]; assumption)

corollary paper_R_classicism_necessitation:
  assumes rich: "paper_R_rich G" and premise: "paper_R_classicism_proves \<Sigma> G P"
  shows "paper_R_classicism_proves \<Sigma> G (paper_R_named_box G P)"
proof -
  have member: "P \<in> {A. paper_R_classicism_proves \<Sigma> G A}" using premise by simp
  have "paper_R_named_box G P \<in> {A. paper_R_classicism_proves \<Sigma> G A}"
    by (rule paper_R_H_theory_necessitation[OF rich paper_R_classicism_is_H_theory
      paper_R_classicism_is_PE_closed[OF rich] member])
  then show ?thesis by simp
qed

text \<open>
  The H-theory structure follows only from the p.12 constructors.
  PE is supplied by the independently proved A.3 corollary; the generic
  p.17 Necessitation proof then applies. No new primitive inference rule
  is added to either H or C, and no model is assumed.
\<close>

end
