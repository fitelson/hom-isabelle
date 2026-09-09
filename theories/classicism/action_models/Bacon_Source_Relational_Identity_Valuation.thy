theory Bacon_Source_Relational_Identity_Valuation
  imports Bacon_Source_Relational_Propositional_Identity_Derivations
    Bacon_Source_Relational_Closed_Henkin_Theory Bacon_Source_Relational_Identity_Representatives
begin

section \<open>The canonical valuation tests membership of a representative in M\<close>

definition paper_R_identity_valuation :: "'c paper_named_term set \<Rightarrow> 'c paper_named_term set \<Rightarrow> bool" where
  "paper_R_identity_valuation M X \<longleftrightarrow> (\<exists>P\<in>X. P \<in> M)"

text \<open>
  V_M(X) holds when some proposition representative belongs to M.
  On a closed proposition class [A], the result is exactly A∈M;
  consequently every representative gives the same answer.
  Source: Theorem 3.2's valuation construction, footnote 64, p.45.

  Classes are native theorem-identity classes, not βη classes.
  Representative independence follows from LL and closed-consequence
  closure. This defines no collapse of all true propositions to one
  object and asserts no Boolean/quantifier truth law or BBK model.
  Outside proposition-class inputs the displayed HOL definition still
  has a Boolean value, but no semantic interpretation is claimed.
\<close>

theorem paper_R_identity_valuation_class:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and representative: "A \<in> paper_R_closed_terms \<Omega> G Prop"
  shows "paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop A) \<longleftrightarrow> A \<in> M"
proof
  assume value_true: "paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop A)"
  obtain B where in_class: "B \<in> paper_R_identity_class \<Omega> G M Prop A" and in_theory: "B \<in> M"
    using value_true unfolding paper_R_identity_valuation_def by blast
  have closed_B: "B \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_identity_class_member_closed_terms[OF in_class])
  have equality: "paper_R_named_derivable \<Omega> G M (named_paper_eq Prop A B)"
    by (rule paper_R_identity_class_member_derivation[OF in_class])
  have equivalent: "A \<in> M \<longleftrightarrow> B \<in> M"
    by (rule paper_R_closed_propositional_identity_membership[
      OF rich paper_R_closed_Henkin_consequence[OF Henkin] representative closed_B equality])
  show "A \<in> M" by (rule iffD2[OF equivalent in_theory])
next
  assume member: "A \<in> M"
  have self: "A \<in> paper_R_identity_class \<Omega> G M Prop A"
    by (rule paper_R_identity_class_self[OF representative])
  show "paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop A)"
    unfolding paper_R_identity_valuation_def by (rule bexI[where x=A], rule member, rule self)
qed

theorem paper_R_identity_valuation_member:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and domain: "X \<in> paper_R_identity_domain \<Omega> G M Prop" and member: "A \<in> X"
  shows "paper_R_identity_valuation M X \<longleftrightarrow> A \<in> M"
proof -
  have representative: "A \<in> paper_R_closed_terms \<Omega> G Prop"
    by (rule paper_R_identity_domain_member_closed_terms[OF domain member])
  have reconstructed: "paper_R_identity_class \<Omega> G M Prop A = X"
    by (rule paper_R_identity_member_class[OF rich domain member])
  show ?thesis using paper_R_identity_valuation_class[OF rich Henkin representative]
    by (simp only: reconstructed)
qed

corollary paper_R_identity_valuation_rep:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and domain: "X \<in> paper_R_identity_domain \<Omega> G M Prop"
  shows "paper_R_identity_valuation M X \<longleftrightarrow> paper_R_identity_rep X \<in> M"
  by (rule paper_R_identity_valuation_member[OF rich Henkin domain paper_R_identity_rep_member[OF domain]])

end
