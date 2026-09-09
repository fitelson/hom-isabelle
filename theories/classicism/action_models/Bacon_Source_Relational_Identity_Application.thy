theory Bacon_Source_Relational_Identity_Application
  imports Bacon_Source_Relational_Identity_Representatives Bacon_Source_Relational_Application_Congruence
begin

section \<open>Application on the actual identity-class fibers\<close>

definition paper_R_identity_application ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow>
    'c paper_named_term set \<Rightarrow> 'c paper_named_term set \<Rightarrow> 'c paper_named_term set" where
  "paper_R_identity_application \<Sigma> G S \<sigma> \<tau> X Y =
    paper_R_identity_class \<Sigma> G S \<tau> (NApp (paper_R_identity_rep X) (paper_R_identity_rep Y))"

lemma paper_R_closed_terms_App:
  assumes head: "F \<in> paper_R_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    and argument: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
  shows "NApp F A \<in> paper_R_closed_terms \<Sigma> G \<tau>"
proof (rule paper_R_closed_termsI)
  show "paper_R_in_language \<Sigma> G (NApp F A) \<tau>"
    by (rule paper_R_language_App[OF paper_R_closed_terms_language[OF head] paper_R_closed_terms_language[OF argument]])
  show "named_fv (NApp F A) = {}"
    by (simp only: named_fv.simps paper_R_closed_terms_closed[OF head] paper_R_closed_terms_closed[OF argument]; simp)
qed

theorem paper_R_identity_application_domain:
  assumes head: "X \<in> paper_R_identity_domain \<Sigma> G S (Arr \<sigma> \<tau>)"
    and argument: "Y \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
  shows "paper_R_identity_application \<Sigma> G S \<sigma> \<tau> X Y \<in> paper_R_identity_domain \<Sigma> G S \<tau>"
  unfolding paper_R_identity_application_def
  by (rule paper_R_identity_domainI[OF paper_R_closed_terms_App[
    OF paper_R_identity_rep_closed_terms[OF head] paper_R_identity_rep_closed_terms[OF argument]]])

section \<open>Native application congruence removes the representative choice\<close>

text \<open>
  appσ,τ([F],[A])=[FA]. Replacing either chosen representative by
  another member of its class preserves this result by the proved
  native R application-congruence theorem. Source: the canonical
  interpretation in Theorem 3.2, p.45 n.64.

  The premises are only R-richness and actual typed closed terms or
  class-fiber memberships. S can be arbitrary, even inconsistent.
  No Henkin property, valuation, Functionality, interpretation or BBK
  model certificate is used or asserted. Off-domain operation values
  are not assigned an intended semantic meaning.
\<close>

theorem paper_R_identity_application_classes:
  assumes rich: "paper_R_rich G" and head: "F \<in> paper_R_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    and argument: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
  shows "paper_R_identity_application \<Sigma> G S \<sigma> \<tau>
      (paper_R_identity_class \<Sigma> G S (Arr \<sigma> \<tau>) F) (paper_R_identity_class \<Sigma> G S \<sigma> A) =
    paper_R_identity_class \<Sigma> G S \<tau> (NApp F A)"
proof -
  let ?X = "paper_R_identity_class \<Sigma> G S (Arr \<sigma> \<tau>) F"
  let ?Y = "paper_R_identity_class \<Sigma> G S \<sigma> A"
  let ?F = "paper_R_identity_rep ?X"
  let ?A = "paper_R_identity_rep ?Y"
  have xd: "?X \<in> paper_R_identity_domain \<Sigma> G S (Arr \<sigma> \<tau>)" by (rule paper_R_identity_domainI[OF head])
  have yd: "?Y \<in> paper_R_identity_domain \<Sigma> G S \<sigma>" by (rule paper_R_identity_domainI[OF argument])
  have fc: "?F \<in> paper_R_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)" by (rule paper_R_identity_rep_closed_terms[OF xd])
  have ac: "?A \<in> paper_R_closed_terms \<Sigma> G \<sigma>" by (rule paper_R_identity_rep_closed_terms[OF yd])
  have fe: "paper_R_named_derivable \<Sigma> G S (named_paper_eq (Arr \<sigma> \<tau>) ?F F)"
    by (rule iffD1[OF paper_R_identity_class_eq_iff[OF rich fc head] paper_R_identity_class_rep[OF rich xd]])
  have ae: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> ?A A)"
    by (rule iffD1[OF paper_R_identity_class_eq_iff[OF rich ac argument] paper_R_identity_class_rep[OF rich yd]])
  have equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> (NApp ?F ?A) (NApp F A))"
    by (rule paper_R_named_identity_App[OF rich paper_R_closed_terms_language[OF fc]
      paper_R_closed_terms_language[OF head] paper_R_closed_terms_language[OF ac]
      paper_R_closed_terms_language[OF argument] fe ae])
  have classes: "paper_R_identity_class \<Sigma> G S \<tau> (NApp ?F ?A) = paper_R_identity_class \<Sigma> G S \<tau> (NApp F A)"
    by (rule iffD2[OF paper_R_identity_class_eq_iff[OF rich
      paper_R_closed_terms_App[OF fc ac] paper_R_closed_terms_App[OF head argument]] equality])
  show ?thesis unfolding paper_R_identity_application_def by (rule classes)
qed

theorem paper_R_identity_application_representatives:
  assumes rich: "paper_R_rich G" and head: "X \<in> paper_R_identity_domain \<Sigma> G S (Arr \<sigma> \<tau>)"
    and argument: "Y \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
    and fm: "F \<in> X" and am: "A \<in> Y"
  shows "paper_R_identity_application \<Sigma> G S \<sigma> \<tau> X Y = paper_R_identity_class \<Sigma> G S \<tau> (NApp F A)"
proof -
  have fc: "F \<in> paper_R_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    by (rule paper_R_identity_domain_member_closed_terms[OF head fm])
  have ac: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
    by (rule paper_R_identity_domain_member_closed_terms[OF argument am])
  have xs: "paper_R_identity_class \<Sigma> G S (Arr \<sigma> \<tau>) F = X"
    by (rule paper_R_identity_member_class[OF rich head fm])
  have ys: "paper_R_identity_class \<Sigma> G S \<sigma> A = Y"
    by (rule paper_R_identity_member_class[OF rich argument am])
  show ?thesis using paper_R_identity_application_classes[where S=S, OF rich fc ac] by (simp only: xs ys)
qed

end
