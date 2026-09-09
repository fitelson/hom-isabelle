theory Bacon_Source_Relational_Naming_Charts
  imports Bacon_Source_Relational_Naming_Syntax
begin

section \<open>Distinct fresh variables for a finite set of typed new names\<close>

text \<open>
  A chart sends each (σ,a) in a finite support to a distinct variable of
  type σ, avoiding a specified finite set of names. Only its values on
  that support are constrained. In particular, this is not an injection
  from all of D into the variable stock, even when D is uncountable.

  For a term, the avoided set includes all its variable names, including
  binders. No freshness from the domain of a partial assignment is imposed.
  This leaf constructs no denotation and asserts no chart independence.
\<close>

definition paper_R_naming_chart ::
  "sgcontext \<Rightarrow> (otype \<times> 'v) set \<Rightarrow> nat set \<Rightarrow>
    ((otype \<times> 'v) \<Rightarrow> nat) \<Rightarrow> bool" where
  "paper_R_naming_chart G K N x \<longleftrightarrow>
    inj_on x K \<and> (\<forall>k\<in>K. G (x k) = fst k) \<and> x ` K \<inter> N = {}"

lemma paper_R_naming_chart_injective:
  "paper_R_naming_chart G K N x \<Longrightarrow> inj_on x K"
  unfolding paper_R_naming_chart_def by blast

lemma paper_R_naming_chart_type:
  assumes chart: "paper_R_naming_chart G K N x" and member: "k \<in> K"
  shows "G (x k) = fst k"
  using chart member unfolding paper_R_naming_chart_def by blast

lemma paper_R_naming_chart_fresh:
  assumes chart: "paper_R_naming_chart G K N x" and member: "k \<in> K"
  shows "x k \<notin> N"
  using chart member unfolding paper_R_naming_chart_def by blast

lemma paper_R_naming_chart_restrict:
  assumes chart: "paper_R_naming_chart G K N x" and support: "L \<subseteq> K" and avoid: "P \<subseteq> N"
  shows "paper_R_naming_chart G L P x"
  using chart support avoid unfolding paper_R_naming_chart_def
  by (auto intro: inj_on_subset; blast)

theorem paper_R_naming_chart_exists:
  assumes rich: "paper_R_rich G" and finite: "finite K"
    and types: "\<forall>k\<in>K. paper_R_type (fst k)" and avoid: "finite N"
  shows "\<exists>x. paper_R_naming_chart G K N x"
  using finite types
proof (induction rule: finite_induct)
  case empty
  show ?case by (simp add: paper_R_naming_chart_def)
next
  case (insert k K)
  have previous_types: "\<forall>j\<in>K. paper_R_type (fst j)"
    and new_type: "paper_R_type (fst k)" using insert.prems by auto
  obtain x where old_chart: "paper_R_naming_chart G K N x"
    using insert.IH[OF previous_types] by blast
  have old_inj: "inj_on x K" and old_type: "\<forall>j\<in>K. G (x j) = fst j"
    and old_fresh: "x ` K \<inter> N = {}"
    using old_chart unfolding paper_R_naming_chart_def by blast+
  have finite_forbidden: "finite (N \<union> x ` K)" using avoid insert.hyps(1) by simp
  have infinite_stock: "infinite {n. G n = fst k}"
    by (rule paper_R_rich_type[OF rich new_type])
  have fresh_exists: "\<exists>n. G n = fst k \<and> n \<notin> N \<union> x ` K"
  proof (rule ccontr)
    assume absent: "\<not> (\<exists>n. G n = fst k \<and> n \<notin> N \<union> x ` K)"
    have subset: "{n. G n = fst k} \<subseteq> N \<union> x ` K" using absent by auto
    have "finite {n. G n = fst k}" by (rule finite_subset[OF subset finite_forbidden])
    with infinite_stock show False by contradiction
  qed
  obtain n where nt: "G n = fst k" and fresh: "n \<notin> N \<union> x ` K"
    using fresh_exists by blast
  have injective: "inj_on (x(k := n)) (insert k K)"
    using old_inj fresh insert.hyps(2) by (auto simp: inj_on_def)
  have correctly_typed: "\<forall>j\<in>insert k K. G ((x(k := n)) j) = fst j"
    using old_type nt by auto
  have disjoint: "(x(k := n)) ` insert k K \<inter> N = {}"
    using old_fresh fresh by auto
  have chart: "paper_R_naming_chart G (insert k K) N (x(k := n))"
    unfolding paper_R_naming_chart_def by (rule conjI[OF injective], rule conjI[OF correctly_typed disjoint])
  show ?case by (rule exI[where x="x(k := n)"], rule chart)
qed

theorem paper_R_naming_chart_for_term:
  assumes rich: "paper_R_rich G"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A \<tau>"
    and avoid: "finite N"
  obtains x where "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A \<union> N) x"
proof -
  note finish = that
  have typed: "paper_R_has_type G A \<tau>" using language unfolding paper_R_in_language_def by blast
  have types: "\<forall>k\<in>paper_R_naming_support A. paper_R_type (fst k)"
    by (rule paper_R_naming_support_R_types[OF typed])
  have finite_avoid: "finite (named_vars A \<union> N)" using named_vars_finite avoid by simp
  obtain x where chart: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A \<union> N) x"
    using paper_R_naming_chart_exists[OF rich paper_R_naming_support_finite types finite_avoid] by blast
  show thesis by (rule finish[OF chart])
qed

end
