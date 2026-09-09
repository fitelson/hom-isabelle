theory Bacon_Source_Relational_H_Theory
  imports Bacon_Source_Relational_Local_Consequence
begin

section \<open>H-theories in the fixed native R language\<close>

text \<open>
  An H-theory is a set of R formulas containing native H and closed
  under MP, Gen and Inst with their exact eigenvariable and language
  guards. Source: pp.6–8 and the H-theories considered in Theorem 3.12,
  pp.51–52 n.73. These are conditions on a supplied set, not a new
  inductive calculus or an assertion that all such theories are C.

  R-richness is a separate language-availability hypothesis where needed.
  Propositional Equivalence closure is declared separately below; it is
  not silently built into H or the H-theory definition.
\<close>

definition paper_R_H_theory :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> bool" where
  "paper_R_H_theory \<Sigma> G T \<longleftrightarrow>
    (\<forall>A\<in>T. paper_R_in_language \<Sigma> G A Prop) \<and>
    (\<forall>A. paper_R_named_H \<Sigma> G A \<longrightarrow> A \<in> T) \<and>
    (\<forall>A B. A \<in> T \<longrightarrow> named_paper_imp G A B \<in> T \<longrightarrow>
      paper_R_in_language \<Sigma> G B Prop \<longrightarrow> B \<in> T) \<and>
    (\<forall>P Q n \<sigma>. named_paper_imp G P Q \<in> T \<longrightarrow> G n = \<sigma> \<longrightarrow> n \<notin> named_fv P \<longrightarrow>
      paper_R_in_language \<Sigma> G (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))) Prop \<longrightarrow>
      named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)) \<in> T) \<and>
    (\<forall>P Q n \<sigma>. named_paper_imp G P Q \<in> T \<longrightarrow> G n = \<sigma> \<longrightarrow> n \<notin> named_fv Q \<longrightarrow>
      paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop \<longrightarrow>
      named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q \<in> T)"

definition paper_R_PE_closed :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> bool" where
  "paper_R_PE_closed \<Sigma> G T \<longleftrightarrow>
    (\<forall>P Q. paper_R_in_language \<Sigma> G P Prop \<longrightarrow> paper_R_in_language \<Sigma> G Q Prop \<longrightarrow>
      named_paper_iff G P Q \<in> T \<longrightarrow> named_paper_eq Prop P Q \<in> T)"

lemma paper_R_H_theoryI:
  assumes language: "\<And>A. A \<in> T \<Longrightarrow> paper_R_in_language \<Sigma> G A Prop"
    and base: "\<And>A. paper_R_named_H \<Sigma> G A \<Longrightarrow> A \<in> T"
    and mp: "\<And>A B. A \<in> T \<Longrightarrow> named_paper_imp G A B \<in> T \<Longrightarrow>
      paper_R_in_language \<Sigma> G B Prop \<Longrightarrow> B \<in> T"
    and gen: "\<And>P Q n \<sigma>. named_paper_imp G P Q \<in> T \<Longrightarrow> G n = \<sigma> \<Longrightarrow> n \<notin> named_fv P \<Longrightarrow>
      paper_R_in_language \<Sigma> G (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))) Prop \<Longrightarrow>
      named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)) \<in> T"
    and inst: "\<And>P Q n \<sigma>. named_paper_imp G P Q \<in> T \<Longrightarrow> G n = \<sigma> \<Longrightarrow> n \<notin> named_fv Q \<Longrightarrow>
      paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop \<Longrightarrow>
      named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q \<in> T"
  shows "paper_R_H_theory \<Sigma> G T"
  using assms unfolding paper_R_H_theory_def by blast

lemma paper_R_H_theory_language:
  "paper_R_H_theory \<Sigma> G T \<Longrightarrow> A \<in> T \<Longrightarrow> paper_R_in_language \<Sigma> G A Prop"
  unfolding paper_R_H_theory_def by blast

lemma paper_R_H_theory_H:
  "paper_R_H_theory \<Sigma> G T \<Longrightarrow> paper_R_named_H \<Sigma> G A \<Longrightarrow> A \<in> T"
  unfolding paper_R_H_theory_def by blast

lemma paper_R_H_theory_MP:
  "paper_R_H_theory \<Sigma> G T \<Longrightarrow> A \<in> T \<Longrightarrow> named_paper_imp G A B \<in> T \<Longrightarrow>
    paper_R_in_language \<Sigma> G B Prop \<Longrightarrow> B \<in> T"
  unfolding paper_R_H_theory_def by blast

lemma paper_R_H_theory_Gen:
  "paper_R_H_theory \<Sigma> G T \<Longrightarrow> named_paper_imp G P Q \<in> T \<Longrightarrow>
    G n = \<sigma> \<Longrightarrow> n \<notin> named_fv P \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))) Prop \<Longrightarrow>
    named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)) \<in> T"
  unfolding paper_R_H_theory_def by blast

lemma paper_R_H_theory_Inst:
  "paper_R_H_theory \<Sigma> G T \<Longrightarrow> named_paper_imp G P Q \<in> T \<Longrightarrow>
    G n = \<sigma> \<Longrightarrow> n \<notin> named_fv Q \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop \<Longrightarrow>
    named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q \<in> T"
  unfolding paper_R_H_theory_def by blast

lemma paper_R_PE_closedD:
  "paper_R_PE_closed \<Sigma> G T \<Longrightarrow> paper_R_in_language \<Sigma> G P Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> G Q Prop \<Longrightarrow> named_paper_iff G P Q \<in> T \<Longrightarrow>
    named_paper_eq Prop P Q \<in> T"
  unfolding paper_R_PE_closed_def by blast

theorem paper_R_H_theory_local_consequences:
  assumes theory_h: "paper_R_H_theory \<Sigma> G T"
    and derivation: "paper_R_named_derivable \<Sigma> G S A" and subset: "S \<subseteq> T"
  shows "A \<in> T"
  using derivation subset
proof (induction rule: paper_R_named_derivable.induct)
  case Assumption
  show ?case using Assumption.hyps(1) Assumption.prems by blast
next
  case Theorem
  show ?case by (rule paper_R_H_theory_H[OF theory_h Theorem.hyps])
next
  case MP
  show ?case by (rule paper_R_H_theory_MP[OF theory_h MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
qed

end
