theory Bacon_Source_Relational_Identity_Propositional_Truth
  imports Bacon_Source_Relational_Identity_Interpretation Bacon_Source_Relational_Identity_Boolean_Valuation
begin

section \<open>Boolean truth at typed adequate partial assignments\<close>

text \<open>
  Closed representative substitution commutes literally with ¬, ∧ and ∨.
  Their class valuations have already been proved from native R-PC and
  the syntactic Henkin properties. These facts give Definition 3.1(iii.a–c),
  p.44, for the candidate J. No BBK-model predicate or truth-equivalence
  to identity principle is assumed. Unassigned variables remain unassigned;
  adequacy supplies exactly the free variables of each operand.
\<close>

theorem paper_R_identity_denote_neg_truth:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and language: "paper_R_in_language \<Omega> G A Prop"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g"
    and adequate: "named_adequate g A"
  shows "paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g (named_paper_not A)) =
    (\<not> paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g A))"
proof -
  let ?P = "paper_R_environment_subst (paper_R_representative_assignment g) A"
  have closed: "?P \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_representative_substitution_closed_terms[OF language typed adequate])
  have whole: "paper_R_in_language \<Omega> G (named_paper_not A) Prop"
    by (rule paper_R_named_not_language[OF language])
  have shape: "paper_R_identity_denote \<Omega> G M g (named_paper_not A) =
    paper_R_identity_class \<Omega> G M Prop (named_paper_not ?P)"
    by (rule trans[OF paper_R_identity_denote_eq[where S=M and g=g, OF whole]];
      simp only: named_paper_not_def paper_R_environment_subst.simps)
  show ?thesis by (simp only: shape paper_R_identity_denote_eq[OF language];
    rule paper_R_identity_valuation_not[OF rich Henkin closed])
qed

theorem paper_R_identity_denote_conj_truth:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and left: "paper_R_in_language \<Omega> G A Prop" and right: "paper_R_in_language \<Omega> G B Prop"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g (named_paper_and A B)) =
    (paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g A) \<and>
      paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g B))"
proof -
  let ?r = "paper_R_representative_assignment g"
  have ac: "paper_R_environment_subst ?r A \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_representative_substitution_closed_terms[OF left typed aa])
  have bc: "paper_R_environment_subst ?r B \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_representative_substitution_closed_terms[OF right typed ba])
  have whole: "paper_R_in_language \<Omega> G (named_paper_and A B) Prop"
    by (rule paper_R_named_and_language[OF left right])
  have shape: "paper_R_identity_denote \<Omega> G M g (named_paper_and A B) =
    paper_R_identity_class \<Omega> G M Prop (named_paper_and (paper_R_environment_subst ?r A) (paper_R_environment_subst ?r B))"
    by (rule trans[OF paper_R_identity_denote_eq[where S=M and g=g, OF whole]];
      simp only: named_paper_and_def paper_R_environment_subst.simps)
  show ?thesis by (simp only: shape paper_R_identity_denote_eq[OF left] paper_R_identity_denote_eq[OF right];
    rule paper_R_identity_valuation_and[OF rich Henkin ac bc])
qed

theorem paper_R_identity_denote_disj_truth:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and left: "paper_R_in_language \<Omega> G A Prop" and right: "paper_R_in_language \<Omega> G B Prop"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g (named_paper_or A B)) =
    (paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g A) \<or>
      paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g B))"
proof -
  let ?r = "paper_R_representative_assignment g"
  have ac: "paper_R_environment_subst ?r A \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_representative_substitution_closed_terms[OF left typed aa])
  have bc: "paper_R_environment_subst ?r B \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_representative_substitution_closed_terms[OF right typed ba])
  have whole: "paper_R_in_language \<Omega> G (named_paper_or A B) Prop"
    by (rule paper_R_named_or_language[OF left right])
  have shape: "paper_R_identity_denote \<Omega> G M g (named_paper_or A B) =
    paper_R_identity_class \<Omega> G M Prop (named_paper_or (paper_R_environment_subst ?r A) (paper_R_environment_subst ?r B))"
    by (rule trans[OF paper_R_identity_denote_eq[where S=M and g=g, OF whole]];
      simp only: named_paper_or_def paper_R_environment_subst.simps)
  show ?thesis by (simp only: shape paper_R_identity_denote_eq[OF left] paper_R_identity_denote_eq[OF right];
    rule paper_R_identity_valuation_or[OF rich Henkin ac bc])
qed

end
