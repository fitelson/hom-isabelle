theory Bacon_Book_Lambda_I_Closed_Negation_Complete
  imports Bacon_Book_Lambda_I_Closed_Maximal_Extension
begin

section \<open>Adjoining a consequence preserves consistency\<close>

text \<open>
  If S is consistent and S ⊢ A, then S∪{A} is consistent.
  A contradiction from the larger premise set would, by cut, already
  be a contradiction from S. The explicit language guard on S permits
  every old premise to be used by the original Assumption constructor.
  This argument uses neither deduction nor semantic compactness.
\<close>

lemma book_lambda_I_consistent_insert_consequence:
  assumes consistent: "book_lambda_I_consistent \<Sigma> G S"
    and consequence: "book_lambda_I_derivable \<Sigma> G S A"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G B"
  shows "book_lambda_I_consistent \<Sigma> G (insert A S)"
proof (unfold book_lambda_I_consistent_def, rule notI)
  assume contradiction: "book_lambda_I_derivable \<Sigma> G (insert A S) (book_bottom G)"
  have original: "book_lambda_I_derivable \<Sigma> G S (book_bottom G)"
  proof (rule book_lambda_I_derivable_cut[OF contradiction])
    fix B
    assume member: "B \<in> insert A S"
    show "book_lambda_I_derivable \<Sigma> G S B"
    proof (cases "B = A")
      case True
      show ?thesis using consequence by (simp only: True)
    next
      case False
      have old_member: "B \<in> S" using member False by simp
      show ?thesis by (rule book_lambda_I_derivable.Assumption[OF old_member language[OF old_member]])
    qed
  qed
  show False using consistent original unfolding book_lambda_I_consistent_def by blast
qed

section \<open>Closure under closed consequences\<close>

text \<open>
  If M is maximal among consistent sets of typed CLOSED formulas,
  every closed formula derivable from M belongs to M. Adjoining it
  preserves both the closed-formula language and consistency, so
  maximality forces the enlarged set to equal M.
  No richness premise is needed for this closure property.
\<close>

theorem book_lambda_I_closed_maximal_derivable_member:
  assumes maximal: "book_lambda_I_closed_maximal_extension \<Sigma> G S M"
    and al: "book_lambda_I_formula \<Sigma> G A" and closed: "named_fv A = {}"
    and derivation: "book_lambda_I_derivable \<Sigma> G M A"
  shows "A \<in> M"
proof -
  have closed_M: "book_lambda_I_closed_formula_set \<Sigma> G M"
    and consistent_M: "book_lambda_I_consistent \<Sigma> G M"
    and maximality: "\<forall>U. M \<subseteq> U \<longrightarrow> book_lambda_I_closed_formula_set \<Sigma> G U \<longrightarrow>
      book_lambda_I_consistent \<Sigma> G U \<longrightarrow> U = M"
    using maximal unfolding book_lambda_I_closed_maximal_extension_def by blast+
  have language: "book_lambda_I_formula \<Sigma> G B" if "B \<in> M" for B
    by (rule conjunct1[OF book_lambda_I_closed_formula_set_member[OF closed_M that]])
  have consistent_insert: "book_lambda_I_consistent \<Sigma> G (insert A M)"
    by (rule book_lambda_I_consistent_insert_consequence[OF consistent_M derivation language])
  have closed_insert: "book_lambda_I_closed_formula_set \<Sigma> G (insert A M)"
    using closed_M al closed unfolding book_lambda_I_closed_formula_set_def by auto
  have equality: "insert A M = M"
    using maximality subset_insertI closed_insert consistent_insert by blast
  show ?thesis using equality by blast
qed

section \<open>Decisions for closed formulas only\<close>

text \<open>
  Under a rich stock, for each typed closed λI formula A, either A∈M
  or ¬A∈M, where M is a λI-maximal λI-consistent set of closed λI
  formulas (book_lambda_I_closed_maximal_extension). If A∉M then
  closed-consequence closure gives M ⊬ A. The repaired consistency
  corollary makes M∪{¬A} λI-consistent, and λI maximality puts ¬A in M.
  Nonrelevant typed closed formulas are outside M by definition and are
  not decided.
  Source role: the CLOSED-formula replacement for the inconsistent
  all-open global-theory reading of Definition 15.3, p.319.

  These results do not make M a global higher-order theory: open axiom
  instances need not belong to this closed set. They assert neither
  all-open negation completeness nor witness completeness.
\<close>

theorem book_lambda_I_closed_maximal_decides:
  assumes rich: "sg_rich G"
    and maximal: "book_lambda_I_closed_maximal_extension \<Sigma> G S M"
    and al: "book_lambda_I_formula \<Sigma> G A" and closed: "named_fv A = {}"
  shows "A \<in> M \<or> book_not G A \<in> M"
proof (cases "A \<in> M")
  case True
  show ?thesis by (rule disjI1[OF True])
next
  case False
  have nonderivable: "\<not> book_lambda_I_derivable \<Sigma> G M A"
  proof
    assume derivation: "book_lambda_I_derivable \<Sigma> G M A"
    have member: "A \<in> M"
      by (rule book_lambda_I_closed_maximal_derivable_member[OF maximal al closed derivation])
    show False by (rule notE[OF False member])
  qed
  have closed_M: "book_lambda_I_closed_formula_set \<Sigma> G M"
    and maximality: "\<forall>U. M \<subseteq> U \<longrightarrow> book_lambda_I_closed_formula_set \<Sigma> G U \<longrightarrow>
      book_lambda_I_consistent \<Sigma> G U \<longrightarrow> U = M"
    using maximal unfolding book_lambda_I_closed_maximal_extension_def by blast+
  have nal: "book_lambda_I_formula \<Sigma> G (book_not G A)"
    by (rule book_lambda_I_not_language[OF rich al])
  have negative_closed: "named_fv (book_not G A) = {}"
    by (simp only: book_not_fv closed)
  have closed_insert: "book_lambda_I_closed_formula_set \<Sigma> G (insert (book_not G A) M)"
    using closed_M nal negative_closed unfolding book_lambda_I_closed_formula_set_def by auto
  have consistent_insert: "book_lambda_I_consistent \<Sigma> G (insert (book_not G A) M)"
    by (rule book_lambda_I_consistent_insert_not[OF rich al closed nonderivable])
  have equality: "insert (book_not G A) M = M"
    using maximality subset_insertI closed_insert consistent_insert by blast
  have member: "book_not G A \<in> M" using equality by blast
  show ?thesis by (rule disjI2[OF member])
qed

theorem book_lambda_I_closed_maximal_negation_iff:
  assumes rich: "sg_rich G"
    and maximal: "book_lambda_I_closed_maximal_extension \<Sigma> G S M"
    and al: "book_lambda_I_formula \<Sigma> G A" and closed: "named_fv A = {}"
  shows "book_not G A \<in> M \<longleftrightarrow> A \<notin> M"
proof
  assume negative_member: "book_not G A \<in> M"
  show "A \<notin> M"
  proof
    assume positive_member: "A \<in> M"
    have nal: "book_lambda_I_formula \<Sigma> G (book_not G A)"
      by (rule book_lambda_I_not_language[OF rich al])
    have positive: "book_lambda_I_certificate \<Sigma> G M A"
      by (rule book_lambda_I_certificate.Assumption[OF positive_member al])
    have negative: "book_lambda_I_certificate \<Sigma> G M (book_not G A)"
      by (rule book_lambda_I_certificate.Assumption[OF negative_member nal])
    have bottom_certificate: "book_lambda_I_certificate \<Sigma> G M (book_bottom G)"
      by (rule book_lambda_I_certificate_not_elim[OF rich positive negative])
    have contradiction: "book_lambda_I_derivable \<Sigma> G M (book_bottom G)"
      by (rule book_lambda_I_certificate_embeds[OF bottom_certificate])
    have consistent_M: "book_lambda_I_consistent \<Sigma> G M"
      using maximal unfolding book_lambda_I_closed_maximal_extension_def by blast
    show False using consistent_M contradiction unfolding book_lambda_I_consistent_def by blast
  qed
next
  assume absent: "A \<notin> M"
  have decision: "A \<in> M \<or> book_not G A \<in> M"
    by (rule book_lambda_I_closed_maximal_decides[OF rich maximal al closed])
  show "book_not G A \<in> M" using decision absent by blast
qed

corollary book_lambda_I_closed_decision_extension_exists:
  assumes rich: "sg_rich G" and closed_S: "book_lambda_I_closed_formula_set \<Sigma> G S"
    and consistent_S: "book_lambda_I_consistent \<Sigma> G S"
  shows "\<exists>M. book_lambda_I_closed_maximal_extension \<Sigma> G S M \<and>
    (\<forall>A. book_lambda_I_formula \<Sigma> G A \<longrightarrow> named_fv A = {} \<longrightarrow>
      A \<in> M \<or> book_not G A \<in> M)"
proof -
  obtain M where maximal: "book_lambda_I_closed_maximal_extension \<Sigma> G S M"
    using book_lambda_I_closed_maximal_extension_exists[OF closed_S consistent_S] by blast
  have decisions: "\<forall>A. book_lambda_I_formula \<Sigma> G A \<longrightarrow> named_fv A = {} \<longrightarrow>
      A \<in> M \<or> book_not G A \<in> M"
    by (intro allI impI; rule book_lambda_I_closed_maximal_decides[OF rich maximal]; assumption)
  show ?thesis by (rule exI[where x=M], rule conjI[OF maximal decisions])
qed

end
