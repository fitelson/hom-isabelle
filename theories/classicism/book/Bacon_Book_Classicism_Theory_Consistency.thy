theory Bacon_Book_Classicism_Theory_Consistency
  imports Bacon_Book_Classicism_Least_Theory
    Bacon_Book_Environment_Development.Bacon_Book_Theory_Consistency
begin

section \<open>Theories extending C, without Equivalence under new assumptions\<close>

definition book_C_theory_derivable ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term \<Rightarrow> bool" where
  "book_C_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_theory_derivable \<Sigma> G ({B. book_C_proves \<Sigma> G B} \<union> S) A"

definition book_C_theory_consistent ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_C_theory_consistent \<Sigma> G S \<longleftrightarrow>
    \<not> book_C_theory_derivable \<Sigma> G S (book_bottom G)"

lemma book_C_theory_derivable_mono:
  assumes derivation: "book_C_theory_derivable \<Sigma> G S A" and subset: "S \<subseteq> T"
  shows "book_C_theory_derivable \<Sigma> G T A"
  using derivation unfolding book_C_theory_derivable_def
  by (rule book_theory_derivable_mono; use subset in blast)

theorem book_C_theory_empty_iff:
  assumes rich: "sg_rich G"
  shows "book_C_theory_derivable \<Sigma> G {} A \<longleftrightarrow> book_C_proves \<Sigma> G A"
proof
  assume derivation: "book_C_theory_derivable \<Sigma> G {} A"
  have base: "book_theory_derivable \<Sigma> G {B. book_C_proves \<Sigma> G B} A"
    using derivation by (simp add: book_C_theory_derivable_def)
  show "book_C_proves \<Sigma> G A" by (rule book_C_contains_theory_derivation[OF rich base]; simp)
next
  assume derivation: "book_C_proves \<Sigma> G A"
  show "book_C_theory_derivable \<Sigma> G {} A" unfolding book_C_theory_derivable_def
    by (rule book_theory_derivable.Assumption; (simp add: derivation | rule book_C_proves_language[OF rich derivation]))
qed

theorem book_C_theory_finite_support:
  assumes derivation: "book_C_theory_derivable \<Sigma> G S A"
  obtains U where "finite U" "U \<subseteq> S" "book_C_theory_derivable \<Sigma> G U A"
proof -
  let ?C = "{B. book_C_proves \<Sigma> G B}"
  have base: "book_theory_derivable \<Sigma> G (?C \<union> S) A"
    using derivation unfolding book_C_theory_derivable_def .
  obtain V where finite: "finite V" and subset: "V \<subseteq> ?C \<union> S"
    and supported: "book_theory_derivable \<Sigma> G V A"
    using book_theory_derivable_finite_support[OF base] by blast
  have fin: "finite (V \<inter> S)" using finite by simp
  have inc: "V \<inter> S \<subseteq> S" by blast
  have retained: "V \<subseteq> ?C \<union> (V \<inter> S)" using subset by blast
  have result: "book_C_theory_derivable \<Sigma> G (V \<inter> S) A"
    unfolding book_C_theory_derivable_def by (rule book_theory_derivable_mono[OF supported retained])
  show thesis by (rule that[OF fin inc result])
qed

theorem book_C_theory_consistent_finite_character:
  "book_C_theory_consistent \<Sigma> G S \<longleftrightarrow>
    (\<forall>U. finite U \<longrightarrow> U \<subseteq> S \<longrightarrow> book_C_theory_consistent \<Sigma> G U)"
proof
  assume consistent: "book_C_theory_consistent \<Sigma> G S"
  show "\<forall>U. finite U \<longrightarrow> U \<subseteq> S \<longrightarrow> book_C_theory_consistent \<Sigma> G U"
  proof (intro allI impI)
    fix U
    assume "finite U" and subset: "U \<subseteq> S"
    show "book_C_theory_consistent \<Sigma> G U"
      using consistent book_C_theory_derivable_mono[OF _ subset]
      unfolding book_C_theory_consistent_def by blast
  qed
next
  assume finite_parts: "\<forall>U. finite U \<longrightarrow> U \<subseteq> S \<longrightarrow> book_C_theory_consistent \<Sigma> G U"
  show "book_C_theory_consistent \<Sigma> G S"
  proof (unfold book_C_theory_consistent_def, rule notI)
    assume contradiction: "book_C_theory_derivable \<Sigma> G S (book_bottom G)"
    obtain U where finite: "finite U" and subset: "U \<subseteq> S"
      and proof_bottom: "book_C_theory_derivable \<Sigma> G U (book_bottom G)"
      by (rule book_C_theory_finite_support[OF contradiction])
    show False using finite_parts finite subset proof_bottom unfolding book_C_theory_consistent_def by blast
  qed
qed

text \<open>
  Theorem 18.4 concerns consistent higher-order theories containing C.
  Adding S therefore means ordinary Chapter 5 theory closure of C∪S,
  not closing the new assumptions under Equivalence or Necessitation.
  Empty-premise consequence is proved to recover exactly C theoremhood.

  The finite-support and finite-character proofs keep the complete C
  theorem set fixed while reducing only the additional assumptions S.
  These are proof-theoretic results, not semantic compactness or a
  canonical successor-world existence theorem. Closed-premise discharge,
  witness extension and the modal lifting lemma remain required.
\<close>

end
