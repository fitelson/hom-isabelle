theory Bacon_Source_Relational_Identity_Cardinal_Domains
  imports Bacon_Source_Relational_Admitted_Syntax_Cardinal
    Bacon_Source_Relational_Identity_Classes Bacon_Source_Relational_Term_Type
begin

section \<open>The actual domain union is bounded by admitted syntax\<close>

text \<open>
  Map an admitted term A to its identity class at its selected R type.
  Every actual domain value is in this image: it has a closed typed
  representative, and that typing justifies the selected type. No
  meaning is assigned to the selector on ill-typed terms. Extra image
  values do not affect the upper bound.

  Source role: the carrier bound in p.51 n.73. We bound actual class
  values, not their ambient powerset type. Neither consistency, Henkin
  witnesses, richness nor a semantic model is assumed.
\<close>

lemma paper_R_identity_domains_syntax_bound:
  fixes \<Omega> :: "'c ssignature"
  shows
  "card_of (\<Union>\<sigma>. paper_R_identity_domain \<Omega> G S \<sigma>) \<le>o
    card_of {A :: 'c paper_named_term. named_in_signature \<Omega> A}"
proof -
  let ?T = "{A :: 'c paper_named_term. named_in_signature \<Omega> A}"
  let ?f = "\<lambda>A. paper_R_identity_class \<Omega> G S (paper_R_term_type G A) A"
  have subset: "(\<Union>\<sigma>. paper_R_identity_domain \<Omega> G S \<sigma>) \<subseteq> ?f ` ?T"
  proof
    fix X
    assume member: "X \<in> (\<Union>\<sigma>. paper_R_identity_domain \<Omega> G S \<sigma>)"
    obtain \<sigma> where xm: "X \<in> paper_R_identity_domain \<Omega> G S \<sigma>" using member by blast
    obtain A where closed: "A \<in> paper_R_closed_terms \<Omega> G \<sigma>"
      and shape: "X = paper_R_identity_class \<Omega> G S \<sigma> A"
      by (rule paper_R_identity_domainE[OF xm])
    have language: "paper_R_in_language \<Omega> G A \<sigma>"
      by (rule paper_R_closed_terms_language[OF closed])
    have admitted: "A \<in> ?T" using language unfolding paper_R_in_language_def by blast
    have index: "paper_R_term_type G A = \<sigma>" by (rule paper_R_term_type_language[OF language])
    have image: "?f A \<in> ?f ` ?T" by (rule imageI[OF admitted])
    show "X \<in> ?f ` ?T" using image by (simp only: index shape)
  qed
  show ?thesis by (rule ordLeq_transitive[OF card_of_mono1[OF subset] card_of_image])
qed

theorem paper_R_identity_domains_cardinal_bound:
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Omega> \<sigma>) \<le>o card_of U"
  shows "card_of (\<Union>\<sigma>. paper_R_identity_domain \<Omega> G S \<sigma>) \<le>o card_of U"
  by (rule ordLeq_transitive[OF paper_R_identity_domains_syntax_bound
    paper_R_admitted_syntax_cardinal_bound[OF infinite names]])

end
