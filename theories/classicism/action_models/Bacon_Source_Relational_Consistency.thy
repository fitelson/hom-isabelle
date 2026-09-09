theory Bacon_Source_Relational_Consistency
  imports Bacon_Source_Relational_Explosion
begin

section \<open>Consistency excludes local contradictory pairs, including open ones\<close>

text \<open>
  S is Hᴿ-consistent when no A and ¬A are both locally derivable
  from S. The quantified witness A may be open. An actually used
  derivation supplies its own R-language guard; unused elements of S
  are unrestricted. Source role: Theorem 3.2, footnote 64, pp.44–45,
  and the finite-diagram consistency argument of footnote 73, pp.51–52.

  This is a syntactic LOCAL consequence notion, not a model-existence
  definition. It does not assert that arbitrary open S has a model
  making all its members true under every assignment. Later canonical
  existence must use closed sentences or justified universal closures.
  Finite character below is syntactic, not semantic compactness.
\<close>

definition paper_R_named_consistent ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> bool" where
  "paper_R_named_consistent \<Sigma> G S \<longleftrightarrow>
    \<not> (\<exists>A. paper_R_named_derivable \<Sigma> G S A \<and>
      paper_R_named_derivable \<Sigma> G S (named_paper_not A))"

lemma paper_R_named_consistentI:
  assumes excludes: "\<And>A. paper_R_named_derivable \<Sigma> G S A \<Longrightarrow>
    paper_R_named_derivable \<Sigma> G S (named_paper_not A) \<Longrightarrow> False"
  shows "paper_R_named_consistent \<Sigma> G S"
  using excludes unfolding paper_R_named_consistent_def by blast

lemma paper_R_named_consistentD:
  assumes consistent: "paper_R_named_consistent \<Sigma> G S"
    and positive: "paper_R_named_derivable \<Sigma> G S A"
    and negative: "paper_R_named_derivable \<Sigma> G S (named_paper_not A)"
  shows False
  using assms unfolding paper_R_named_consistent_def by blast

lemma paper_R_named_inconsistentE:
  assumes inconsistent: "\<not> paper_R_named_consistent \<Sigma> G S"
  obtains A where "paper_R_named_derivable \<Sigma> G S A"
    "paper_R_named_derivable \<Sigma> G S (named_paper_not A)"
  using inconsistent that unfolding paper_R_named_consistent_def by blast

theorem paper_R_named_consistent_mono:
  assumes consistent: "paper_R_named_consistent \<Sigma> G T" and subset: "S \<subseteq> T"
  shows "paper_R_named_consistent \<Sigma> G S"
proof (rule paper_R_named_consistentI)
  fix A
  assume positive: "paper_R_named_derivable \<Sigma> G S A"
    and negative: "paper_R_named_derivable \<Sigma> G S (named_paper_not A)"
  show False by (rule paper_R_named_consistentD[
    OF consistent paper_R_named_derivable_mono[OF positive subset]
      paper_R_named_derivable_mono[OF negative subset]])
qed

section \<open>Every inconsistency has finite premise support\<close>

lemma paper_R_named_inconsistent_finite_support:
  assumes inconsistent: "\<not> paper_R_named_consistent \<Sigma> G S"
  obtains T where "finite T" "T \<subseteq> S" "\<not> paper_R_named_consistent \<Sigma> G T"
proof -
  obtain A where positive: "paper_R_named_derivable \<Sigma> G S A"
    and negative: "paper_R_named_derivable \<Sigma> G S (named_paper_not A)"
    by (rule paper_R_named_inconsistentE[OF inconsistent])
  obtain U where uf: "finite U" and us: "U \<subseteq> S" and up: "paper_R_named_derivable \<Sigma> G U A"
    using paper_R_named_derivable_finite_support[OF positive] by blast
  obtain V where vf: "finite V" and vs: "V \<subseteq> S"
    and vn: "paper_R_named_derivable \<Sigma> G V (named_paper_not A)"
    using paper_R_named_derivable_finite_support[OF negative] by blast
  have positive_union: "paper_R_named_derivable \<Sigma> G (U \<union> V) A"
    by (rule paper_R_named_derivable_mono[OF up Un_upper1])
  have negative_union: "paper_R_named_derivable \<Sigma> G (U \<union> V) (named_paper_not A)"
    by (rule paper_R_named_derivable_mono[OF vn Un_upper2])
  have finite_union: "finite (U \<union> V)" using uf vf by simp
  have subset_union: "U \<union> V \<subseteq> S" using us vs by blast
  have bad: "\<not> paper_R_named_consistent \<Sigma> G (U \<union> V)"
    using positive_union negative_union unfolding paper_R_named_consistent_def by blast
  show thesis by (rule that[OF finite_union subset_union bad])
qed

theorem paper_R_named_consistent_finite_character:
  "paper_R_named_consistent \<Sigma> G S \<longleftrightarrow>
    (\<forall>T. finite T \<longrightarrow> T \<subseteq> S \<longrightarrow> paper_R_named_consistent \<Sigma> G T)"
proof
  assume consistent: "paper_R_named_consistent \<Sigma> G S"
  show "\<forall>T. finite T \<longrightarrow> T \<subseteq> S \<longrightarrow> paper_R_named_consistent \<Sigma> G T"
    by (intro allI impI, rule paper_R_named_consistent_mono[OF consistent]; assumption)
next
  assume every: "\<forall>T. finite T \<longrightarrow> T \<subseteq> S \<longrightarrow> paper_R_named_consistent \<Sigma> G T"
  show "paper_R_named_consistent \<Sigma> G S"
  proof (rule ccontr)
    assume bad: "\<not> paper_R_named_consistent \<Sigma> G S"
    obtain T where finite: "finite T" and subset: "T \<subseteq> S"
      and inconsistent: "\<not> paper_R_named_consistent \<Sigma> G T"
      by (rule paper_R_named_inconsistent_finite_support[OF bad])
    show False using every finite subset inconsistent by blast
  qed
qed

section \<open>Explosion and the negated-conclusion extension\<close>

theorem paper_R_named_inconsistent_explosion:
  assumes rich: "paper_R_rich G" and inconsistent: "\<not> paper_R_named_consistent \<Sigma> G S"
    and conclusion: "paper_R_in_language \<Sigma> G B Prop"
  shows "paper_R_named_derivable \<Sigma> G S B"
proof -
  obtain A where positive: "paper_R_named_derivable \<Sigma> G S A"
    and negative: "paper_R_named_derivable \<Sigma> G S (named_paper_not A)"
    by (rule paper_R_named_inconsistentE[OF inconsistent])
  show ?thesis by (rule paper_R_named_derivable_explosion[OF rich positive negative conclusion])
qed

lemma paper_R_named_underivable_consistent:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G B Prop"
    and underivable: "\<not> paper_R_named_derivable \<Sigma> G S B"
  shows "paper_R_named_consistent \<Sigma> G S"
proof (rule ccontr)
  assume bad: "\<not> paper_R_named_consistent \<Sigma> G S"
  have derivation: "paper_R_named_derivable \<Sigma> G S B"
    by (rule paper_R_named_inconsistent_explosion[OF rich bad language])
  show False using underivable derivation by contradiction
qed

text \<open>
  If B is an underivable R formula, S∪{¬B} remains locally consistent.
  The existing consistency of S need not be assumed separately:
  underivability already implies it by explosion. The proof discharges
  ¬B using the local deduction theorem and an explicit native R-PC
  certificate; it does not build a negation-complete open theory.
\<close>

theorem paper_R_named_consistent_insert_not:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G B Prop"
    and underivable: "\<not> paper_R_named_derivable \<Sigma> G S B"
  shows "paper_R_named_consistent \<Sigma> G (insert (named_paper_not B) S)"
proof (rule paper_R_named_consistentI)
  fix A
  assume positive: "paper_R_named_derivable \<Sigma> G (insert (named_paper_not B) S) A"
    and negative: "paper_R_named_derivable \<Sigma> G (insert (named_paper_not B) S) (named_paper_not A)"
  have derivation: "paper_R_named_derivable \<Sigma> G S B"
    by (rule paper_R_named_derivable_reductio[OF rich language positive negative])
  show False using underivable derivation by contradiction
qed

end
