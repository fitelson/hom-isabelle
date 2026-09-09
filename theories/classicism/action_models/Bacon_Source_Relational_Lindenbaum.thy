theory Bacon_Source_Relational_Lindenbaum
  imports Bacon_Source_Relational_Closed_Theory "HOL.Zorn"
begin

section \<open>Native finite proof support controls nonempty chain unions\<close>

lemma paper_R_named_consistent_chain_Union:
  assumes chain: "subset.chain Family \<C>" and nonempty: "\<C> \<noteq> {}"
    and members: "\<And>U. U \<in> \<C> \<Longrightarrow> paper_R_named_consistent \<Sigma> G U"
  shows "paper_R_named_consistent \<Sigma> G (\<Union>\<C>)"
proof (rule ccontr)
  assume bad: "\<not> paper_R_named_consistent \<Sigma> G (\<Union>\<C>)"
  obtain F where finite: "finite F" and covered: "F \<subseteq> \<Union>\<C>"
    and inconsistent: "\<not> paper_R_named_consistent \<Sigma> G F"
    by (rule paper_R_named_inconsistent_finite_support[OF bad])
  obtain U where member: "U \<in> \<C>" and cover_member: "F \<subseteq> U"
    by (rule finite_subset_Union_chain[OF finite covered nonempty chain])
  have consistent: "paper_R_named_consistent \<Sigma> G F"
    by (rule paper_R_named_consistent_mono[OF members[OF member] cover_member])
  show False using inconsistent consistent by contradiction
qed

section \<open>Zorn extension in the fixed signature and stock\<close>

text \<open>
  Order the consistent closed extensions of S by inclusion. A nonempty
  chain has its union as an upper bound: any contradiction would have
  finite premise support in one member. The empty chain uses the given
  S itself. Zorn's lemma then supplies a maximal member.

  Source role: the closed-formula Lindenbaum stage of Theorem 3.2,
  p.45 n.64. The nonlogical carrier, signature and S can be arbitrarily
  large. No enumeration, richness, witness, Henkin theory, fullness or
  semantic compactness premise is used. Decision and consequence closure
  of the maximal set are separate native proof-theoretic lemmas.
\<close>

theorem paper_R_closed_maximal_extension_exists:
  assumes closed: "paper_R_closed_theory \<Sigma> G S"
    and consistent: "paper_R_named_consistent \<Sigma> G S"
  shows "\<exists>M. paper_R_closed_maximal_extension \<Sigma> G S M"
proof -
  let ?Family = "{U. S \<subseteq> U \<and> paper_R_closed_theory \<Sigma> G U \<and> paper_R_named_consistent \<Sigma> G U}"
  have initial: "S \<in> ?Family" using closed consistent by simp
  have upper_bounds: "\<exists>U\<in>?Family. \<forall>X\<in>\<C>. X \<subseteq> U"
    if chain: "subset.chain ?Family \<C>" for \<C>
  proof (cases "\<C> = {}")
    case True
    have bound: "\<forall>X\<in>\<C>. X \<subseteq> S" by (simp only: True; simp)
    show ?thesis by (rule bexI[where x=S], rule bound, rule initial)
  next
    case False
    have inside: "\<C> \<subseteq> ?Family" using chain unfolding subset_chain_def by blast
    have closed_members: "paper_R_closed_theory \<Sigma> G U" if "U \<in> \<C>" for U
      using subsetD[OF inside that] by simp
    have consistent_members: "paper_R_named_consistent \<Sigma> G U" if "U \<in> \<C>" for U
      using subsetD[OF inside that] by simp
    obtain U where member: "U \<in> \<C>" using False by blast
    have contains_S: "S \<subseteq> U" using subsetD[OF inside member] by simp
    have extends: "S \<subseteq> \<Union>\<C>" by (rule subset_trans[OF contains_S Union_upper[OF member]])
    have closed_union: "paper_R_closed_theory \<Sigma> G (\<Union>\<C>)"
      by (rule paper_R_closed_theory_Union[OF closed_members])
    have consistent_union: "paper_R_named_consistent \<Sigma> G (\<Union>\<C>)"
      by (rule paper_R_named_consistent_chain_Union[OF chain False consistent_members])
    have union_member: "\<Union>\<C> \<in> ?Family" using extends closed_union consistent_union by simp
    have bound: "\<forall>X\<in>\<C>. X \<subseteq> \<Union>\<C>" by (intro ballI; rule Union_upper; assumption)
    show ?thesis by (rule bexI[where x="\<Union>\<C>"], rule bound, rule union_member)
  qed
  obtain M where member: "M \<in> ?Family" and maximal: "\<forall>U\<in>?Family. M \<subseteq> U \<longrightarrow> U = M"
    using subset_Zorn[OF upper_bounds] by blast
  have extends: "S \<subseteq> M" and closed_M: "paper_R_closed_theory \<Sigma> G M"
    and consistent_M: "paper_R_named_consistent \<Sigma> G M" using member by simp_all
  have maximal_closed: "\<forall>U. M \<subseteq> U \<longrightarrow> paper_R_closed_theory \<Sigma> G U \<longrightarrow>
      paper_R_named_consistent \<Sigma> G U \<longrightarrow> U = M"
  proof (intro allI impI)
    fix U
    assume contains: "M \<subseteq> U" and closed_U: "paper_R_closed_theory \<Sigma> G U"
      and consistent_U: "paper_R_named_consistent \<Sigma> G U"
    have extends_U: "S \<subseteq> U" by (rule subset_trans[OF extends contains])
    have in_family: "U \<in> ?Family" using extends_U closed_U consistent_U by simp
    show "U = M" using maximal in_family contains by blast
  qed
  have result: "paper_R_closed_maximal_extension \<Sigma> G S M"
    unfolding paper_R_closed_maximal_extension_def
    by (rule conjI[OF extends conjI[OF closed_M conjI[OF consistent_M maximal_closed]]])
  show ?thesis by (rule exI[where x=M], rule result)
qed

end
