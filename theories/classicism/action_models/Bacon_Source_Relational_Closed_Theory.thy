theory Bacon_Source_Relational_Closed_Theory
  imports Bacon_Source_Relational_Consistency
begin

section \<open>Closed R formulas and their premise sets\<close>

text \<open>
  A sentence is an R formula of ℒ(Σ) with no free variables.
  A closed theory here is merely a SET of such sentences; its name
  does not assert deductive closure, negation completeness, witnesses,
  or any model property. Source: §1.1, pp.5–6, and the sentence-set
  model-existence statement of Theorem 3.2, pp.44–45.
\<close>

definition paper_R_sentence :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "paper_R_sentence \<Sigma> G A \<longleftrightarrow> paper_R_in_language \<Sigma> G A Prop \<and> named_fv A = {}"

definition paper_R_closed_theory :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> bool" where
  "paper_R_closed_theory \<Sigma> G S \<longleftrightarrow> (\<forall>A\<in>S. paper_R_sentence \<Sigma> G A)"

lemma paper_R_sentenceI:
  "paper_R_in_language \<Sigma> G A Prop \<Longrightarrow> named_fv A = {} \<Longrightarrow> paper_R_sentence \<Sigma> G A"
  unfolding paper_R_sentence_def by blast

lemma paper_R_sentence_language:
  "paper_R_sentence \<Sigma> G A \<Longrightarrow> paper_R_in_language \<Sigma> G A Prop"
  unfolding paper_R_sentence_def by blast

lemma paper_R_sentence_closed:
  "paper_R_sentence \<Sigma> G A \<Longrightarrow> named_fv A = {}"
  unfolding paper_R_sentence_def by blast

lemma paper_R_closed_theory_member:
  "paper_R_closed_theory \<Sigma> G S \<Longrightarrow> A \<in> S \<Longrightarrow> paper_R_sentence \<Sigma> G A"
  unfolding paper_R_closed_theory_def by blast

lemma paper_R_closed_theory_empty:
  "paper_R_closed_theory \<Sigma> G {}"
  by (simp add: paper_R_closed_theory_def)

lemma paper_R_closed_theory_insert:
  "paper_R_closed_theory \<Sigma> G (insert A S) \<longleftrightarrow>
    paper_R_sentence \<Sigma> G A \<and> paper_R_closed_theory \<Sigma> G S"
  by (simp add: paper_R_closed_theory_def)

lemma paper_R_closed_theory_subset:
  "paper_R_closed_theory \<Sigma> G T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> paper_R_closed_theory \<Sigma> G S"
  unfolding paper_R_closed_theory_def by blast

lemma paper_R_closed_theory_Union:
  assumes members: "\<And>S. S \<in> \<C> \<Longrightarrow> paper_R_closed_theory \<Sigma> G S"
  shows "paper_R_closed_theory \<Sigma> G (\<Union>\<C>)"
  using members unfolding paper_R_closed_theory_def by blast

section \<open>Maximality only among closed consistent extensions\<close>

definition paper_R_closed_maximal_extension ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> 'c paper_named_term set \<Rightarrow> bool" where
  "paper_R_closed_maximal_extension \<Sigma> G S M \<longleftrightarrow>
    S \<subseteq> M \<and> paper_R_closed_theory \<Sigma> G M \<and> paper_R_named_consistent \<Sigma> G M \<and>
    (\<forall>U. M \<subseteq> U \<longrightarrow> paper_R_closed_theory \<Sigma> G U \<longrightarrow>
      paper_R_named_consistent \<Sigma> G U \<longrightarrow> U = M)"

lemma paper_R_closed_maximal_extends:
  "paper_R_closed_maximal_extension \<Sigma> G S M \<Longrightarrow> S \<subseteq> M"
  unfolding paper_R_closed_maximal_extension_def by blast

lemma paper_R_closed_maximal_theory:
  "paper_R_closed_maximal_extension \<Sigma> G S M \<Longrightarrow> paper_R_closed_theory \<Sigma> G M"
  unfolding paper_R_closed_maximal_extension_def by blast

lemma paper_R_closed_maximal_consistent:
  "paper_R_closed_maximal_extension \<Sigma> G S M \<Longrightarrow> paper_R_named_consistent \<Sigma> G M"
  unfolding paper_R_closed_maximal_extension_def by blast

lemma paper_R_closed_maximal_eq:
  "paper_R_closed_maximal_extension \<Sigma> G S M \<Longrightarrow> M \<subseteq> U \<Longrightarrow>
    paper_R_closed_theory \<Sigma> G U \<Longrightarrow> paper_R_named_consistent \<Sigma> G U \<Longrightarrow> U = M"
  unfolding paper_R_closed_maximal_extension_def by blast

end
