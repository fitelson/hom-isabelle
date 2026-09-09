theory Bacon_Source_Relational_Identity_Identity_Truth
  imports Bacon_Source_Relational_Identity_Propositional_Truth
begin

section \<open>Identity truth is equality of the actual classes\<close>

lemma paper_R_closed_terms_identity:
  assumes first: "A \<in> paper_R_closed_terms \<Omega> G \<sigma>"
    and second: "B \<in> paper_R_closed_terms \<Omega> G \<sigma>"
  shows "named_paper_eq \<sigma> A B \<in> paper_R_closed_terms \<Omega> G Prop"
proof (rule paper_R_closed_termsI)
  show "paper_R_in_language \<Omega> G (named_paper_eq \<sigma> A B) Prop"
    by (rule paper_R_named_identity_language[OF paper_R_closed_terms_language[OF first]
      paper_R_closed_terms_language[OF second]])
  show "named_fv (named_paper_eq \<sigma> A B) = {}"
    by (simp only: named_paper_primitive_fv paper_R_closed_terms_closed[OF first]
      paper_R_closed_terms_closed[OF second]; simp)
qed

theorem paper_R_identity_valuation_identity:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and first: "A \<in> paper_R_closed_terms \<Omega> G \<sigma>"
    and second: "B \<in> paper_R_closed_terms \<Omega> G \<sigma>"
  shows "paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop (named_paper_eq \<sigma> A B)) =
    (paper_R_identity_class \<Omega> G M \<sigma> A = paper_R_identity_class \<Omega> G M \<sigma> B)"
proof -
  have closed: "named_paper_eq \<sigma> A B \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_closed_terms_identity[OF first second])
  have membership: "named_paper_eq \<sigma> A B \<in> M \<longleftrightarrow>
    paper_R_named_derivable \<Omega> G M (named_paper_eq \<sigma> A B)"
  proof
    assume member: "named_paper_eq \<sigma> A B \<in> M"
    show "paper_R_named_derivable \<Omega> G M (named_paper_eq \<sigma> A B)"
      by (rule paper_R_closed_Henkin_member_derivable[OF Henkin member])
  next
    assume derivation: "paper_R_named_derivable \<Omega> G M (named_paper_eq \<sigma> A B)"
    show "named_paper_eq \<sigma> A B \<in> M"
      by (rule paper_R_closed_Henkin_consequence[OF Henkin derivation paper_R_closed_terms_closed[OF closed]])
  qed
  show ?thesis by (simp only: paper_R_identity_valuation_class[OF rich Henkin closed] membership
    paper_R_identity_class_eq_iff[OF rich first second])
qed

text \<open>
  Definition 3.1(iii.f), p.44, holds at every R type, not just t.
  The class equivalence is DEFINED by derivable identity; Henkin
  closed-consequence closure turns that derivability into membership,
  and the valuation then yields actual equality of the two classes.
  The following typed-assignment theorem applies this argument to the
  closed substituted representatives. No equality-of-truth-values
  principle or semantic model certificate is assumed.
\<close>

theorem paper_R_identity_denote_identity_truth:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and left: "paper_R_in_language \<Omega> G A \<sigma>" and right: "paper_R_in_language \<Omega> G B \<sigma>"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g (named_paper_eq \<sigma> A B)) =
    (paper_R_identity_denote \<Omega> G M g A = paper_R_identity_denote \<Omega> G M g B)"
proof -
  let ?r = "paper_R_representative_assignment g"
  have ac: "paper_R_environment_subst ?r A \<in> paper_R_closed_terms \<Omega> G \<sigma>"
    by (rule paper_R_representative_substitution_closed_terms[OF left typed aa])
  have bc: "paper_R_environment_subst ?r B \<in> paper_R_closed_terms \<Omega> G \<sigma>"
    by (rule paper_R_representative_substitution_closed_terms[OF right typed ba])
  have whole: "paper_R_in_language \<Omega> G (named_paper_eq \<sigma> A B) Prop"
    by (rule paper_R_named_identity_language[OF left right])
  have shape: "paper_R_identity_denote \<Omega> G M g (named_paper_eq \<sigma> A B) =
    paper_R_identity_class \<Omega> G M Prop (named_paper_eq \<sigma> (paper_R_environment_subst ?r A) (paper_R_environment_subst ?r B))"
    by (rule trans[OF paper_R_identity_denote_eq[where S=M and g=g, OF whole]];
      simp only: named_paper_eq_def paper_R_environment_subst.simps)
  show ?thesis by (simp only: shape paper_R_identity_denote_eq[OF left] paper_R_identity_denote_eq[OF right];
    rule paper_R_identity_valuation_identity[OF rich Henkin ac bc])
qed

end
