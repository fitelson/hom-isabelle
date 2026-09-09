theory Bacon_Source_Relational_Local_Signature_Conservativity
  imports Bacon_Source_Relational_Local_Retraction Bacon_Source_Relational_Consistency
begin

section \<open>Choose one R-typed replacement family outside a finite support\<close>

lemma paper_R_rich_retraction_family:
  assumes rich: "paper_R_rich G" and finite: "finite N"
  obtains v where "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
    and "\<And>\<rho>. v \<rho> \<notin> N"
proof -
  let ?v = "\<lambda>\<rho>. SOME n. G n = (if paper_R_type \<rho> then \<rho> else Prop) \<and> n \<notin> N"
  have chosen: "G (?v \<rho>) = (if paper_R_type \<rho> then \<rho> else Prop) \<and> ?v \<rho> \<notin> N" for \<rho>
  proof (rule someI_ex)
    have rt: "paper_R_type (if paper_R_type \<rho> then \<rho> else Prop)" by simp
    show "\<exists>n. G n = (if paper_R_type \<rho> then \<rho> else Prop) \<and> n \<notin> N"
      by (rule paper_R_rich_avoiding_variable[OF rich rt finite])
  qed
  have stock: "G (?v \<rho>) = \<rho>" if rt: "paper_R_type \<rho>" for \<rho>
    using conjunct1[OF chosen[of \<rho>]] by (simp only: if_P[OF rt])
  have fresh: "\<And>\<rho>. ?v \<rho> \<notin> N" by (rule conjunct2[OF chosen])
  show thesis by (rule that[OF stock fresh])
qed

theorem paper_R_named_derivable_foreign_constants_eliminate:
  assumes rich: "paper_R_rich G" and derivation: "paper_R_named_derivable \<Sigma> G S A"
    and premise_names: "\<And>B. B \<in> S \<Longrightarrow> named_in_signature \<Omega> B"
    and conclusion_names: "named_in_signature \<Omega> A"
  shows "paper_R_named_derivable \<Omega> G S A"
proof -
  obtain N where support: "paper_R_local_retraction_support \<Omega> G S A N"
    using paper_R_named_derivable_retraction_support[OF derivation premise_names] by blast
  have finite: "finite N" by (rule paper_R_local_retraction_support_finite[OF support])
  obtain v where stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
    and fresh: "\<And>\<rho>. v \<rho> \<notin> N"
    by (rule paper_R_rich_retraction_family[OF rich finite]; rule that; assumption)
  have retracted: "paper_R_named_derivable \<Omega> G S (named_retract \<Omega> v A)"
    by (rule paper_R_local_retraction_support_apply[OF support stock fresh])
  show ?thesis using retracted by (simp only: named_retract_fixed[OF conclusion_names])
qed

corollary paper_R_named_derivable_signature_iff:
  assumes rich: "paper_R_rich G"
    and left_premises: "\<And>B. B \<in> S \<Longrightarrow> named_in_signature \<Sigma> B"
    and right_premises: "\<And>B. B \<in> S \<Longrightarrow> named_in_signature \<Omega> B"
    and left_conclusion: "named_in_signature \<Sigma> A" and right_conclusion: "named_in_signature \<Omega> A"
  shows "paper_R_named_derivable \<Sigma> G S A \<longleftrightarrow> paper_R_named_derivable \<Omega> G S A"
  using paper_R_named_derivable_foreign_constants_eliminate[OF rich _ right_premises right_conclusion]
    paper_R_named_derivable_foreign_constants_eliminate[OF rich _ left_premises left_conclusion] by blast

section \<open>Transport consistency using one common retraction of both proofs\<close>

text \<open>
  An alleged Σ contradiction consists of two finite proofs, possibly
  with a foreign open conclusion A. Choose the SAME replacement family
  outside the union of their supports. The resulting Ω proofs derive
  ret(A) and ¬ret(A), contradicting Ω consistency. No original-language
  assumption on A is needed, and no freshness for all of S is imposed.

  There is no signature-inclusion hypothesis in this syntactic statement.
  If Σ omits some premise names, those premises may be unusable in Σ;
  interpreting the conclusion as ordinary language enlargement additionally
  requires Ω⊆Σ. No model, F calculus or closed inhabitants are assumed.
\<close>

theorem paper_R_named_consistent_signature_transport:
  assumes rich: "paper_R_rich G" and consistent: "paper_R_named_consistent \<Omega> G S"
    and premise_names: "\<And>B. B \<in> S \<Longrightarrow> named_in_signature \<Omega> B"
  shows "paper_R_named_consistent \<Sigma> G S"
proof (rule paper_R_named_consistentI)
  fix A
  assume positive: "paper_R_named_derivable \<Sigma> G S A"
    and negative: "paper_R_named_derivable \<Sigma> G S (named_paper_not A)"
  obtain N where first: "paper_R_local_retraction_support \<Omega> G S A N"
    using paper_R_named_derivable_retraction_support[OF positive premise_names] by blast
  obtain K where second: "paper_R_local_retraction_support \<Omega> G S (named_paper_not A) K"
    using paper_R_named_derivable_retraction_support[OF negative premise_names] by blast
  have finite: "finite (N \<union> K)"
    by (rule finite_UnI[OF paper_R_local_retraction_support_finite[OF first] paper_R_local_retraction_support_finite[OF second]])
  obtain v where stock: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow> G (v \<rho>) = \<rho>"
    and fresh: "\<And>\<rho>. v \<rho> \<notin> N \<union> K"
    by (rule paper_R_rich_retraction_family[OF rich finite]; rule that; assumption)
  have fn: "\<And>\<rho>. v \<rho> \<notin> N" and fk: "\<And>\<rho>. v \<rho> \<notin> K" using fresh by blast+
  have retracted_positive: "paper_R_named_derivable \<Omega> G S (named_retract \<Omega> v A)"
    by (rule paper_R_local_retraction_support_apply[OF first stock fn])
  have retracted_negative: "paper_R_named_derivable \<Omega> G S (named_paper_not (named_retract \<Omega> v A))"
    using paper_R_local_retraction_support_apply[OF second stock fk] by (simp only: paper_R_retract_primitive)
  show False by (rule paper_R_named_consistentD[OF consistent retracted_positive retracted_negative])
qed

end
