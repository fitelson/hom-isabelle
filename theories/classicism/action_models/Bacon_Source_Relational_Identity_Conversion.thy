theory Bacon_Source_Relational_Identity_Conversion
  imports Bacon_Source_Relational_Identity_Interpretation Bacon_Source_Relational_Environment_Conversion
    Bacon_Source_Relational_Conversion_Identity
begin

section \<open>Raw βη conversion gives equal canonical denotations\<close>

text \<open>
  Substitute the chosen closed representatives into both endpoints.
  The partial-environment syntax theorem preserves the complete raw
  R conversion. Adequacy closes the two endpoints, while their language
  guards and assigned representative types preserve Σ membership.
  Native H then proves identity of these closed terms; the identity-class
  equality theorem finishes the argument. Source: Definition 3.1(ii.d),
  p.44, and the canonical construction in Theorem 3.2, p.45 n.64.

  The domain premise concerns only the supplied partial class assignment.
  No Henkin property, consistency, semantic model, full completion, or
  denotation-conversion law is assumed. This proof uses the fixed chosen
  representatives; independence of arbitrary closed replacements is a
  separate obligation and is not asserted here.
\<close>

theorem paper_R_identity_denote_beta_eta:
  assumes rich: "paper_R_rich G" and conversion: "paper_R_raw_beta_eta G \<tau> A B"
    and left: "paper_R_in_language \<Sigma> G A \<tau>" and right: "paper_R_in_language \<Sigma> G B \<tau>"
    and typed: "named_env_typed (paper_R_identity_domain \<Sigma> G S) G g"
    and adequate_left: "named_adequate g A" and adequate_right: "named_adequate g B"
  shows "paper_R_identity_denote \<Sigma> G S g A = paper_R_identity_denote \<Sigma> G S g B"
proof -
  let ?r = "paper_R_representative_assignment g"
  let ?A = "paper_R_environment_subst ?r A"
  let ?B = "paper_R_environment_subst ?r B"
  have assigned: "paper_R_closed_term_assignment \<Sigma> G ?r"
    by (rule paper_R_representative_assignment_typed[OF typed])
  have converted: "paper_R_raw_beta_eta G \<tau> ?A ?B"
    by (rule paper_R_environment_subst_raw_conversion[OF assigned conversion])
  have ac: "?A \<in> paper_R_closed_terms \<Sigma> G \<tau>"
    by (rule paper_R_representative_substitution_closed_terms[OF left typed adequate_left])
  have bc: "?B \<in> paper_R_closed_terms \<Sigma> G \<tau>"
    by (rule paper_R_representative_substitution_closed_terms[OF right typed adequate_right])
  have theorem_identity: "paper_R_named_H \<Sigma> G (named_paper_eq \<tau> ?A ?B)"
    by (rule paper_R_named_H_raw_conversion_identity[OF rich converted
      paper_R_closed_terms_language[OF ac] paper_R_closed_terms_language[OF bc]])
  have local_identity: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> ?A ?B)"
    by (rule paper_R_named_derivable.Theorem[OF theorem_identity])
  have classes: "paper_R_identity_class \<Sigma> G S \<tau> ?A = paper_R_identity_class \<Sigma> G S \<tau> ?B"
    by (rule iffD2[OF paper_R_identity_class_eq_iff[where S=S, OF rich ac bc] local_identity])
  show ?thesis by (simp only: paper_R_identity_denote_eq[OF left] paper_R_identity_denote_eq[OF right]; rule classes)
qed

end
