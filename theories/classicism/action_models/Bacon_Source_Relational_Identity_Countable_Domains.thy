theory Bacon_Source_Relational_Identity_Countable_Domains
  imports Bacon_Source_Relational_Admitted_Terms_Countable Bacon_Source_Relational_Identity_Classes
begin

section \<open>Count the actual identity-domain values, not their ambient powerset carrier\<close>

lemma paper_R_closed_terms_countable:
  assumes names: "countable (\<Union>\<rho>. \<Omega> \<rho>)"
  shows "countable (paper_R_closed_terms \<Omega> G \<sigma>)"
proof -
  have subset: "paper_R_closed_terms \<Omega> G \<sigma> \<subseteq> {A. named_in_signature \<Omega> A}"
    unfolding paper_R_closed_terms_def paper_R_in_language_def by blast
  show ?thesis by (rule countable_subset[OF subset paper_R_admitted_terms_countable[OF names]])
qed

theorem paper_R_identity_domain_countable:
  assumes names: "countable (\<Union>\<rho>. \<Omega> \<rho>)"
  shows "countable (paper_R_identity_domain \<Omega> G S \<sigma>)"
  unfolding paper_R_identity_domain_def by (rule countable_image[OF paper_R_closed_terms_countable[OF names]])

theorem paper_R_identity_domains_countable:
  assumes names: "countable (\<Union>\<rho>. \<Omega> \<rho>)"
  shows "countable (\<Union>\<sigma>. paper_R_identity_domain \<Omega> G S \<sigma>)"
  by (rule countable_UN[OF pHct_otypes_countable]; rule paper_R_identity_domain_countable[OF names])

text \<open>
  Each fiber is an image of its admitted closed terms, and there are
  countably many type indices. This uses neither consistency, richness,
  a Henkin property nor a semantic model. It does not assert countability
  of the whole type 'c paper_named_term set. Only the actual union of
  represented class values is countable. Source: Theorem 3.2, p.45 n.64.
\<close>

end
