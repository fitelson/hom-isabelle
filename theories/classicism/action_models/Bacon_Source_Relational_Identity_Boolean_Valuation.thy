theory Bacon_Source_Relational_Identity_Boolean_Valuation
  imports Bacon_Source_Relational_Henkin_Boolean_Membership Bacon_Source_Relational_Identity_Valuation
begin

section \<open>The class valuation respects the literal Boolean connectives\<close>

text \<open>
  V([¬A])=¬V([A]), V([A∧B])=V([A])∧V([B]), and
  V([A∨B])=V([A])∨V([B]) for closed R propositions.
  Source: Theorem 3.2, footnote 64, p.45.

  Each compound has an actual closed representative. Its valuation
  is membership of that representative in M, and the preceding
  syntactic membership theorems provide the Boolean calculation.
  This is not yet a theorem about a canonical interpretation J.
  No semantic BBK model, quantifier law or collapse of equally true
  proposition classes is assumed or concluded.
\<close>

theorem paper_R_identity_valuation_not:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and first: "A \<in> paper_R_closed_terms \<Omega> G Prop"
  shows "paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop (named_paper_not A)) =
    (\<not> paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop A))"
  by (simp only: paper_R_identity_valuation_class[OF rich Henkin paper_R_closed_terms_not[OF first]]
    paper_R_identity_valuation_class[OF rich Henkin first] paper_R_closed_Henkin_not_member[OF Henkin first])

theorem paper_R_identity_valuation_and:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and first: "A \<in> paper_R_closed_terms \<Omega> G Prop" and second: "B \<in> paper_R_closed_terms \<Omega> G Prop"
  shows "paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop (named_paper_and A B)) =
    (paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop A) \<and>
      paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop B))"
  by (simp only: paper_R_identity_valuation_class[OF rich Henkin paper_R_closed_terms_and[OF first second]]
    paper_R_identity_valuation_class[OF rich Henkin first] paper_R_identity_valuation_class[OF rich Henkin second]
    paper_R_closed_Henkin_and_member[OF rich Henkin first second])

theorem paper_R_identity_valuation_or:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and first: "A \<in> paper_R_closed_terms \<Omega> G Prop" and second: "B \<in> paper_R_closed_terms \<Omega> G Prop"
  shows "paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop (named_paper_or A B)) =
    (paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop A) \<or>
      paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop B))"
  by (simp only: paper_R_identity_valuation_class[OF rich Henkin paper_R_closed_terms_or[OF first second]]
    paper_R_identity_valuation_class[OF rich Henkin first] paper_R_identity_valuation_class[OF rich Henkin second]
    paper_R_closed_Henkin_or_member[OF rich Henkin first second])

end
