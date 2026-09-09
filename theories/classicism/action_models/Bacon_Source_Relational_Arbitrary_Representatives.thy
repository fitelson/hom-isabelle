theory Bacon_Source_Relational_Arbitrary_Representatives
  imports Bacon_Source_Relational_Environment_Finite_Identity Bacon_Source_Relational_Identity_Interpretation
begin

section \<open>Arbitrary choices of one representative for each assigned class\<close>

definition paper_R_represents_class_assignment ::
  "('c paper_named_term set) named_assignment \<Rightarrow> ('c paper_named_term) named_assignment \<Rightarrow> bool" where
  "paper_R_represents_class_assignment g r \<longleftrightarrow>
    dom r = dom g \<and> (\<forall>n X B. g n = Some X \<longrightarrow> r n = Some B \<longrightarrow> B \<in> X)"

lemma paper_R_represents_class_assignment_domain:
  "paper_R_represents_class_assignment g r \<Longrightarrow> dom r = dom g"
  unfolding paper_R_represents_class_assignment_def by (rule conjunct1)

lemma paper_R_represents_class_assignment_member:
  assumes represents: "paper_R_represents_class_assignment g r"
    and class_value: "g n = Some X" and representative: "r n = Some B"
  shows "B \<in> X"
  using assms unfolding paper_R_represents_class_assignment_def by blast

lemma paper_R_represents_class_assignment_typed:
  assumes typed: "named_env_typed (paper_R_identity_domain \<Omega> G S) G g"
    and represents: "paper_R_represents_class_assignment g r"
  shows "paper_R_closed_term_assignment \<Omega> G r"
proof (unfold paper_R_closed_term_assignment_def, intro allI impI)
  fix n B
  assume assigned: "r n = Some B"
  have in_r: "n \<in> dom r" using assigned by (simp add: dom_def)
  have in_g: "n \<in> dom g" using in_r by (simp only: paper_R_represents_class_assignment_domain[OF represents])
  obtain X where class_value: "g n = Some X" using in_g by (auto simp: dom_def)
  have domain: "X \<in> paper_R_identity_domain \<Omega> G S (G n)" by (rule named_env_value[OF typed class_value])
  have member: "B \<in> X" by (rule paper_R_represents_class_assignment_member[OF represents class_value assigned])
  show "B \<in> paper_R_closed_terms \<Omega> G (G n)"
    by (rule paper_R_identity_domain_member_closed_terms[OF domain member])
qed

lemma paper_R_arbitrary_representatives_coordinate:
  assumes rich: "paper_R_rich G"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G S) G g"
    and represents: "paper_R_represents_class_assignment g r"
    and selected: "paper_R_representative_assignment g n = Some B"
    and chosen: "r n = Some C"
  shows "paper_R_named_derivable \<Omega> G S (named_paper_eq (G n) B C)"
proof -
  obtain X where class_value: "g n = Some X" and shape: "B = paper_R_identity_rep X"
    using selected by (cases "g n") (auto simp: paper_R_representative_assignment_def)
  have domain: "X \<in> paper_R_identity_domain \<Omega> G S (G n)" by (rule named_env_value[OF typed class_value])
  have member: "C \<in> X" by (rule paper_R_represents_class_assignment_member[OF represents class_value chosen])
  have in_class: "C \<in> paper_R_identity_class \<Omega> G S (G n) (paper_R_identity_rep X)"
    by (simp only: paper_R_identity_class_rep[OF rich domain]; rule member)
  show ?thesis by (simp only: shape; rule paper_R_identity_class_member_derivation[OF in_class])
qed

theorem paper_R_arbitrary_representatives_identity:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Omega> G A \<rho>"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G S) G g"
    and represents: "paper_R_represents_class_assignment g r"
  shows "paper_R_named_derivable \<Omega> G S (named_paper_eq \<rho>
    (paper_R_environment_subst (paper_R_representative_assignment g) A) (paper_R_environment_subst r A))"
proof -
  have first: "paper_R_closed_term_assignment \<Omega> G (paper_R_representative_assignment g)"
    by (rule paper_R_representative_assignment_typed[OF typed])
  have second: "paper_R_closed_term_assignment \<Omega> G r"
    by (rule paper_R_represents_class_assignment_typed[OF typed represents])
  have domains: "dom (paper_R_representative_assignment g) = dom r"
    by (simp only: paper_R_representative_assignment_domain;
      rule sym[OF paper_R_represents_class_assignment_domain[OF represents]])
  show ?thesis by (rule paper_R_environment_subst_assignment_identity[OF rich language first second domains];
    rule paper_R_arbitrary_representatives_coordinate[OF rich typed represents]; assumption)
qed

section \<open>The canonical interpretation is independent of the fixed selector\<close>

text \<open>
  Any partial term assignment r with the same defined coordinates as g
  and r(n)∈g(n) gives the same class [Env(r,A)] as the fixed selector.
  Adequacy makes both substituted terms closed; the preceding finite
  coordinate proof gives their native derivable identity.
  Source: Theorem 3.2's arbitrary representative convention, footnote 64,
  p.45. Choices are simultaneous and one-per-variable. No semantic
  model, consistency, Henkin property or representative-independence
  assumption is used. This equates classes, not raw substituted terms.
\<close>

theorem paper_R_identity_denote_arbitrary_representatives:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Omega> G A \<rho>"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G S) G g"
    and adequate: "named_adequate g A"
    and represents: "paper_R_represents_class_assignment g r"
  shows "paper_R_identity_denote \<Omega> G S g A =
    paper_R_identity_class \<Omega> G S \<rho> (paper_R_environment_subst r A)"
proof -
  have fixed_closed: "paper_R_environment_subst (paper_R_representative_assignment g) A \<in> paper_R_closed_terms \<Omega> G \<rho>"
    by (rule paper_R_representative_substitution_closed_terms[OF language typed adequate])
  have assigned: "paper_R_closed_term_assignment \<Omega> G r"
    by (rule paper_R_represents_class_assignment_typed[OF typed represents])
  have payloads: "named_fv B = {}" if "r n = Some B" for n B
    by (rule paper_R_closed_terms_closed[OF paper_R_closed_term_assignmentD[OF assigned that]])
  have covering: "named_adequate r A"
    using adequate by (simp only: named_adequate_def paper_R_represents_class_assignment_domain[OF represents])
  have result_closed: "named_fv (paper_R_environment_subst r A) = {}"
    by (rule paper_R_environment_subst_adequate_closed[OF payloads covering])
  have arbitrary_closed: "paper_R_environment_subst r A \<in> paper_R_closed_terms \<Omega> G \<rho>"
    by (rule paper_R_closed_termsI[OF paper_R_environment_subst_language[OF language assigned] result_closed])
  have equality: "paper_R_named_derivable \<Omega> G S (named_paper_eq \<rho>
    (paper_R_environment_subst (paper_R_representative_assignment g) A) (paper_R_environment_subst r A))"
    by (rule paper_R_arbitrary_representatives_identity[OF rich language typed represents])
  have classes: "paper_R_identity_class \<Omega> G S \<rho> (paper_R_environment_subst (paper_R_representative_assignment g) A) =
    paper_R_identity_class \<Omega> G S \<rho> (paper_R_environment_subst r A)"
    by (rule iffD2[OF paper_R_identity_class_eq_iff[OF rich fixed_closed arbitrary_closed] equality])
  show ?thesis by (simp only: paper_R_identity_denote_eq[OF language]; rule classes)
qed

end
