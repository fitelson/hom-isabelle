theory Bacon_Source_Relational_Identity_Representatives
  imports Bacon_Source_Relational_Identity_Classes
begin

section \<open>Choose a representative only from an actual nonempty class\<close>

text \<open>
  rep(X) chooses a member of X. Every X in an identity-domain fiber
  is a nonempty class of typed closed R terms, so this choice is
  justified on its intended domain. Its total HOL value on other sets
  has no asserted meaning. Source: the representative construction in
  Theorem 3.2, p.45 n.64. No inhabited fiber, consistency, Henkin theory
  or semantic model is assumed.
\<close>

definition paper_R_identity_rep :: "'c paper_named_term set \<Rightarrow> 'c paper_named_term" where
  "paper_R_identity_rep X = (SOME A. A \<in> X)"

lemma paper_R_identity_rep_member:
  assumes domain: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
  shows "paper_R_identity_rep X \<in> X"
proof -
  have nonempty: "X \<noteq> {}" by (rule paper_R_identity_value_nonempty[OF domain])
  have exists: "\<exists>A. A \<in> X" using nonempty by blast
  show ?thesis unfolding paper_R_identity_rep_def by (rule someI_ex[OF exists])
qed

lemma paper_R_identity_rep_closed_terms:
  assumes domain: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
  shows "paper_R_identity_rep X \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
  by (rule paper_R_identity_domain_member_closed_terms[OF domain paper_R_identity_rep_member[OF domain]])

lemma paper_R_identity_rep_language:
  assumes domain: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
  shows "paper_R_in_language \<Sigma> G (paper_R_identity_rep X) \<sigma>"
  by (rule paper_R_closed_terms_language[OF paper_R_identity_rep_closed_terms[OF domain]])

lemma paper_R_identity_rep_closed:
  assumes domain: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
  shows "named_fv (paper_R_identity_rep X) = {}"
  by (rule paper_R_closed_terms_closed[OF paper_R_identity_rep_closed_terms[OF domain]])

lemma paper_R_identity_member_class:
  assumes rich: "paper_R_rich G" and domain: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
    and member: "A \<in> X"
  shows "paper_R_identity_class \<Sigma> G S \<sigma> A = X"
proof -
  obtain B where bm: "B \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
    and shape: "X = paper_R_identity_class \<Sigma> G S \<sigma> B"
    by (rule paper_R_identity_domainE[OF domain])
  have in_class: "A \<in> paper_R_identity_class \<Sigma> G S \<sigma> B" using member by (simp only: shape)
  have am: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>" by (rule paper_R_identity_class_member_closed_terms[OF in_class])
  have equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> B A)"
    by (rule paper_R_identity_class_member_derivation[OF in_class])
  have classes: "paper_R_identity_class \<Sigma> G S \<sigma> B = paper_R_identity_class \<Sigma> G S \<sigma> A"
    by (rule iffD2[OF paper_R_identity_class_eq_iff[OF rich bm am] equality])
  show ?thesis by (simp only: shape; rule classes[symmetric])
qed

theorem paper_R_identity_class_rep:
  assumes rich: "paper_R_rich G" and domain: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
  shows "paper_R_identity_class \<Sigma> G S \<sigma> (paper_R_identity_rep X) = X"
  by (rule paper_R_identity_member_class[OF rich domain paper_R_identity_rep_member[OF domain]])

end
