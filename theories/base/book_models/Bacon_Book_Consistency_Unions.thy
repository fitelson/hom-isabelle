theory Bacon_Book_Consistency_Unions
  imports Bacon_Book_Theory_Consistency
begin

section \<open>A finite subset of a directed union lies in one member\<close>

text \<open>
  If a nonempty family is directed by inclusion, each finite subset of
  its union is contained in one member. The induction combines the member
  covering the new element with the member covering the previous finite
  subset. Directedness is essential: this is not a theorem about arbitrary
  families of sets.

  Source role: the finite-proof-support argument at the end of Bacon's
  Proposition 15.4, p.319, without restricting the family to an enumerated
  sequence. This lemma is ordinary set theory and imposes no bound on the
  ambient type or the cardinality of the family.
\<close>

lemma book_finite_directed_cover:
  assumes finite_F: "finite F" and included: "F \<subseteq> \<Union>\<C>"
    and nonempty: "\<C> \<noteq> {}"
    and directed: "\<And>U V. U \<in> \<C> \<Longrightarrow> V \<in> \<C> \<Longrightarrow>
      \<exists>W\<in>\<C>. U \<union> V \<subseteq> W"
  shows "\<exists>U\<in>\<C>. F \<subseteq> U"
  using finite_F included
proof (induction rule: finite_induct)
  case empty
  obtain U where member: "U \<in> \<C>" using nonempty by blast
  show ?case by (rule bexI[where x=U]; simp add: member)
next
  case (insert a F)
  have a_union: "a \<in> \<Union>\<C>" and F_union: "F \<subseteq> \<Union>\<C>"
    using insert.prems by auto
  obtain U where U_member: "U \<in> \<C>" and a_member: "a \<in> U" using a_union by blast
  obtain V where V_member: "V \<in> \<C>" and F_member: "F \<subseteq> V"
    using insert.IH[OF F_union] by blast
  obtain W where W_member: "W \<in> \<C>" and bound: "U \<union> V \<subseteq> W"
    using directed[OF U_member V_member] by blast
  have covered: "insert a F \<subseteq> W" using a_member F_member bound by blast
  show ?case by (rule bexI[where x=W]; fact)
qed

section \<open>Directed unions preserve proof-theoretic consistency\<close>

text \<open>
  A nonempty directed union of consistent premise sets is consistent.
  An alleged contradiction has finite support, which lies in one member;
  that member would then be inconsistent. No soundness, model existence,
  semantic compactness, or richness assumption is used.

  The signature Σ and variable stock G are fixed throughout this theorem.
  Transport between changing witness signatures remains a separate proof
  obligation. For an empty family, an initial consistent set can instead
  provide the upper bound in a later maximal-extension construction.
\<close>

theorem book_theory_consistent_directed_Union:
  assumes nonempty: "\<C> \<noteq> {}"
    and directed: "\<And>U V. U \<in> \<C> \<Longrightarrow> V \<in> \<C> \<Longrightarrow>
      \<exists>W\<in>\<C>. U \<union> V \<subseteq> W"
    and consistent: "\<And>U. U \<in> \<C> \<Longrightarrow> book_theory_consistent \<Sigma> G U"
  shows "book_theory_consistent \<Sigma> G (\<Union>\<C>)"
proof (rule iffD2[OF book_theory_consistent_finite_iff], intro allI impI)
  fix F
  assume finite_F: "finite F" and included: "F \<subseteq> \<Union>\<C>"
  obtain U where member: "U \<in> \<C>" and covered: "F \<subseteq> U"
    using book_finite_directed_cover[OF finite_F included nonempty directed] by blast
  show "book_theory_consistent \<Sigma> G F"
    by (rule book_theory_consistent_subset[OF consistent[OF member] covered])
qed

corollary book_theory_consistent_chain_Union:
  assumes nonempty: "\<C> \<noteq> {}"
    and chain: "\<And>U V. U \<in> \<C> \<Longrightarrow> V \<in> \<C> \<Longrightarrow> U \<subseteq> V \<or> V \<subseteq> U"
    and consistent: "\<And>U. U \<in> \<C> \<Longrightarrow> book_theory_consistent \<Sigma> G U"
  shows "book_theory_consistent \<Sigma> G (\<Union>\<C>)"
proof (rule book_theory_consistent_directed_Union[OF nonempty _ consistent])
  fix U V
  assume U_member: "U \<in> \<C>" and V_member: "V \<in> \<C>"
  show "\<exists>W\<in>\<C>. U \<union> V \<subseteq> W"
    using chain[OF U_member V_member] U_member V_member by blast
qed

end
