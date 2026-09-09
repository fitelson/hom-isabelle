theory Bacon_Book_Closed_Maximal_Extension
  imports Bacon_Book_Consistency_Unions "HOL.Zorn"
begin

section \<open>Maximal consistency among closed formulas\<close>

text \<open>
  A consistent set S of typed closed formulas extends to a maximal
  consistent set M of typed closed formulas, in the SAME signature Σ
  and variable stock G. Source role: the closed-formula completion stage
  in the repaired route toward Bacon's Chapter 15 model construction.

  This is maximality among closed premise sets, not an assertion that M
  is a global higher-order theory or decides all open formulas. No witness
  completeness is claimed. Zorn's lemma is used without an enumeration,
  a countability restriction, a richness premise, or a model assumption.
\<close>

definition book_closed_formula_set ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_closed_formula_set \<Sigma> G S \<longleftrightarrow>
    (\<forall>A\<in>S. book_theory_formula \<Sigma> G A \<and> named_fv A = {})"

lemma book_closed_formula_set_member:
  assumes closed_set: "book_closed_formula_set \<Sigma> G S" and member: "A \<in> S"
  shows "book_theory_formula \<Sigma> G A \<and> named_fv A = {}"
  using closed_set member unfolding book_closed_formula_set_def by blast

lemma book_closed_formula_set_Union:
  assumes members: "\<And>U. U \<in> \<C> \<Longrightarrow> book_closed_formula_set \<Sigma> G U"
  shows "book_closed_formula_set \<Sigma> G (\<Union>\<C>)"
proof (unfold book_closed_formula_set_def, rule ballI)
  fix A
  assume member: "A \<in> \<Union>\<C>"
  obtain U where U_member: "U \<in> \<C>" and A_member: "A \<in> U"
    using member by blast
  show "book_theory_formula \<Sigma> G A \<and> named_fv A = {}"
    by (rule book_closed_formula_set_member[OF members[OF U_member] A_member])
qed

definition book_closed_maximal_extension ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_closed_maximal_extension \<Sigma> G S M \<longleftrightarrow>
    S \<subseteq> M \<and> book_closed_formula_set \<Sigma> G M \<and> book_theory_consistent \<Sigma> G M \<and>
    (\<forall>U. M \<subseteq> U \<longrightarrow> book_closed_formula_set \<Sigma> G U \<longrightarrow>
      book_theory_consistent \<Sigma> G U \<longrightarrow> U = M)"

section \<open>Chain upper bounds and Zorn's lemma\<close>

text \<open>
  Order the consistent closed-formula extensions of S by inclusion.
  For an empty chain, S itself is an upper bound. For a nonempty chain,
  its union still extends S, still contains only typed closed formulas,
  and is consistent by finite proof support. Thus every chain has an
  upper bound in the same family.
\<close>

theorem book_closed_maximal_extension_exists:
  assumes closed_S: "book_closed_formula_set \<Sigma> G S"
    and consistent_S: "book_theory_consistent \<Sigma> G S"
  shows "\<exists>M. book_closed_maximal_extension \<Sigma> G S M"
proof -
  let ?F = "{U. S \<subseteq> U \<and> book_closed_formula_set \<Sigma> G U \<and> book_theory_consistent \<Sigma> G U}"
  have initial: "S \<in> ?F" using closed_S consistent_S by simp
  have upper_bounds: "\<exists>U\<in>?F. \<forall>X\<in>\<C>. X \<subseteq> U"
    if chain: "subset.chain ?F \<C>" for \<C>
  proof (cases "\<C> = {}")
    case True
    have bound: "\<forall>X\<in>\<C>. X \<subseteq> S" by (simp add: True)
    show ?thesis by (rule bexI[where x=S], rule bound, rule initial)
  next
    case False
    have inside: "\<C> \<subseteq> ?F"
      using chain unfolding subset_chain_def by (rule conjunct1)
    have comparison: "\<forall>U\<in>\<C>. \<forall>V\<in>\<C>. U \<subseteq> V \<or> V \<subseteq> U"
      using chain unfolding subset_chain_def by (rule conjunct2)
    have comparable: "U \<subseteq> V \<or> V \<subseteq> U" if "U \<in> \<C>" and "V \<in> \<C>" for U V
      by (rule bspec[OF bspec[OF comparison that(1)] that(2)])
    have all_closed: "book_closed_formula_set \<Sigma> G U" if "U \<in> \<C>" for U
    proof -
      have member: "U \<in> ?F" by (rule subsetD[OF inside that])
      show ?thesis using member by simp
    qed
    have all_consistent: "book_theory_consistent \<Sigma> G U" if "U \<in> \<C>" for U
    proof -
      have member: "U \<in> ?F" by (rule subsetD[OF inside that])
      show ?thesis using member by simp
    qed
    obtain U where U_member: "U \<in> \<C>" using False by blast
    have U_in_family: "U \<in> ?F" by (rule subsetD[OF inside U_member])
    have extends_U: "S \<subseteq> U" using U_in_family by simp
    have extends_union: "S \<subseteq> \<Union>\<C>"
      by (rule subset_trans[OF extends_U Union_upper[OF U_member]])
    have closed_union: "book_closed_formula_set \<Sigma> G (\<Union>\<C>)"
      by (rule book_closed_formula_set_Union[OF all_closed])
    have consistent_union: "book_theory_consistent \<Sigma> G (\<Union>\<C>)"
      by (rule book_theory_consistent_chain_Union[OF False comparable all_consistent])
    have union_member: "\<Union>\<C> \<in> ?F" using extends_union closed_union consistent_union by simp
    have bound: "\<forall>X\<in>\<C>. X \<subseteq> \<Union>\<C>"
      by (rule ballI, rule Union_upper, assumption)
    show ?thesis by (rule bexI[where x="\<Union>\<C>"], rule bound, rule union_member)
  qed
  obtain M where M_member: "M \<in> ?F"
    and maximal: "\<forall>U\<in>?F. M \<subseteq> U \<longrightarrow> U = M"
    using subset_Zorn[OF upper_bounds] by blast
  have extends: "S \<subseteq> M" and closed_M: "book_closed_formula_set \<Sigma> G M"
    and consistent_M: "book_theory_consistent \<Sigma> G M" using M_member by simp_all
  have maximal_closed: "\<forall>U. M \<subseteq> U \<longrightarrow> book_closed_formula_set \<Sigma> G U \<longrightarrow>
    book_theory_consistent \<Sigma> G U \<longrightarrow> U = M"
  proof (intro allI impI)
    fix U
    assume contains_M: "M \<subseteq> U" and closed_U: "book_closed_formula_set \<Sigma> G U"
      and consistent_U: "book_theory_consistent \<Sigma> G U"
    have extends_U: "S \<subseteq> U" by (rule subset_trans[OF extends contains_M])
    have U_member: "U \<in> ?F" using extends_U closed_U consistent_U by simp
    show "U = M" by (rule mp[OF bspec[OF maximal U_member] contains_M])
  qed
  have result: "book_closed_maximal_extension \<Sigma> G S M"
    unfolding book_closed_maximal_extension_def
    by (rule conjI[OF extends conjI[OF closed_M conjI[OF consistent_M maximal_closed]]])
  show ?thesis by (rule exI[where x=M], rule result)
qed

end
