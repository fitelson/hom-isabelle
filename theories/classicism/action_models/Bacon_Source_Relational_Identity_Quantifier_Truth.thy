theory Bacon_Source_Relational_Identity_Quantifier_Truth
  imports Bacon_Source_Relational_Identity_Fresh_Application Bacon_Source_Relational_Identity_Quantifier_Valuation
begin

section \<open>Quantifier truth for the canonical interpretation J\<close>

text \<open>
  Adequacy makes F[r] a typed closed predicate. Its class quantifier
  laws range over EVERY X∈Dσ. For each such X, the fresh-variable
  application theorem identifies app(JgF,X) with J(g[n↦X])(Fn).
  Source: Definition 3.1(iii.d–e), p.44, and Theorem 3.2, p.45 n.64.

  The input is the syntactic closed Henkin theory, not a BBK model
  or an assumed quantifier valuation law for J. Assignments remain
  partial; no domain-surjectivity or constant-denotability condition
  is imposed on X. All representative and application facts invoked
  below have already been derived independently.
\<close>

theorem paper_R_identity_denote_forall_truth:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g"
    and adequate: "named_adequate g F" and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g (NApp (NLogical (SAll \<sigma>)) F)) =
    (\<forall>X\<in>paper_R_identity_domain \<Omega> G M \<sigma>.
      paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M (g(n := Some X)) (NApp F (NVar n))))"
proof -
  let ?F = "paper_R_environment_subst (paper_R_representative_assignment g) F"
  let ?D = "paper_R_identity_domain \<Omega> G M \<sigma>"
  let ?J = "paper_R_identity_denote \<Omega> G M"
  let ?V = "paper_R_identity_valuation M"
  have closed_predicate: "?F \<in> paper_R_closed_terms \<Omega> G (Arr \<sigma> Prop)"
    by (rule paper_R_representative_substitution_closed_terms[OF predicate typed adequate])
  have language: "paper_R_in_language \<Omega> G (named_paper_all \<sigma> F) Prop"
    by (rule paper_R_predicate_all_language[OF predicate])
  have quantified: "?J g (named_paper_all \<sigma> F) = paper_R_identity_class \<Omega> G M Prop (named_paper_all \<sigma> ?F)"
    by (rule trans[OF paper_R_identity_denote_eq[where S=M and g=g, OF language]];
      simp only: named_paper_all_def paper_R_environment_subst.simps)
  have head: "?J g F = paper_R_identity_class \<Omega> G M (Arr \<sigma> Prop) ?F"
    by (rule paper_R_identity_denote_eq[OF predicate])
  have class_truth: "?V (?J g (named_paper_all \<sigma> F)) =
      (\<forall>X\<in>?D. ?V (paper_R_identity_application \<Omega> G M \<sigma> Prop (?J g F) X))"
    by (simp only: quantified head; rule paper_R_identity_valuation_forall_class[OF rich Henkin closed_predicate])
  have tests: "(\<forall>X\<in>?D. ?V (paper_R_identity_application \<Omega> G M \<sigma> Prop (?J g F) X)) =
      (\<forall>X\<in>?D. ?V (?J (g(n := Some X)) (NApp F (NVar n))))"
  proof (rule ball_cong[OF refl])
    fix X
    assume member: "X \<in> ?D"
    have application: "?J (g(n := Some X)) (NApp F (NVar n)) =
        paper_R_identity_application \<Omega> G M \<sigma> Prop (?J g F) X"
      by (rule paper_R_identity_denote_fresh_application[OF rich predicate typed adequate nt fresh member])
    show "?V (paper_R_identity_application \<Omega> G M \<sigma> Prop (?J g F) X) =
      ?V (?J (g(n := Some X)) (NApp F (NVar n)))" by (simp only: application)
  qed
  have result: "?V (?J g (named_paper_all \<sigma> F)) =
      (\<forall>X\<in>?D. ?V (?J (g(n := Some X)) (NApp F (NVar n))))"
    by (simp only: class_truth tests)
  show ?thesis using result by (simp only: named_paper_all_def)
qed

theorem paper_R_identity_denote_exists_truth:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g"
    and adequate: "named_adequate g F" and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g (NApp (NLogical (SEx \<sigma>)) F)) =
    (\<exists>X\<in>paper_R_identity_domain \<Omega> G M \<sigma>.
      paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M (g(n := Some X)) (NApp F (NVar n))))"
proof -
  let ?F = "paper_R_environment_subst (paper_R_representative_assignment g) F"
  let ?D = "paper_R_identity_domain \<Omega> G M \<sigma>"
  let ?J = "paper_R_identity_denote \<Omega> G M"
  let ?V = "paper_R_identity_valuation M"
  have closed_predicate: "?F \<in> paper_R_closed_terms \<Omega> G (Arr \<sigma> Prop)"
    by (rule paper_R_representative_substitution_closed_terms[OF predicate typed adequate])
  have language: "paper_R_in_language \<Omega> G (named_paper_ex \<sigma> F) Prop"
    by (rule paper_R_predicate_exists_language[OF predicate])
  have quantified: "?J g (named_paper_ex \<sigma> F) = paper_R_identity_class \<Omega> G M Prop (named_paper_ex \<sigma> ?F)"
    by (rule trans[OF paper_R_identity_denote_eq[where S=M and g=g, OF language]];
      simp only: named_paper_ex_def paper_R_environment_subst.simps)
  have head: "?J g F = paper_R_identity_class \<Omega> G M (Arr \<sigma> Prop) ?F"
    by (rule paper_R_identity_denote_eq[OF predicate])
  have class_truth: "?V (?J g (named_paper_ex \<sigma> F)) =
      (\<exists>X\<in>?D. ?V (paper_R_identity_application \<Omega> G M \<sigma> Prop (?J g F) X))"
    by (simp only: quantified head; rule paper_R_identity_valuation_exists_class[OF rich Henkin closed_predicate])
  have tests: "(\<exists>X\<in>?D. ?V (paper_R_identity_application \<Omega> G M \<sigma> Prop (?J g F) X)) =
      (\<exists>X\<in>?D. ?V (?J (g(n := Some X)) (NApp F (NVar n))))"
  proof (rule bex_cong[OF refl])
    fix X
    assume member: "X \<in> ?D"
    have application: "?J (g(n := Some X)) (NApp F (NVar n)) =
        paper_R_identity_application \<Omega> G M \<sigma> Prop (?J g F) X"
      by (rule paper_R_identity_denote_fresh_application[OF rich predicate typed adequate nt fresh member])
    show "?V (paper_R_identity_application \<Omega> G M \<sigma> Prop (?J g F) X) =
      ?V (?J (g(n := Some X)) (NApp F (NVar n)))" by (simp only: application)
  qed
  have result: "?V (?J g (named_paper_ex \<sigma> F)) =
      (\<exists>X\<in>?D. ?V (?J (g(n := Some X)) (NApp F (NVar n))))"
    by (simp only: class_truth tests)
  show ?thesis using result by (simp only: named_paper_ex_def)
qed

end
