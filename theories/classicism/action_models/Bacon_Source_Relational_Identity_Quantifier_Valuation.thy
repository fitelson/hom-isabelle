theory Bacon_Source_Relational_Identity_Quantifier_Valuation
  imports Bacon_Source_Relational_Henkin_Universal_Membership Bacon_Source_Relational_Identity_Valuation
begin

section \<open>Every closed argument class has the expected application truth value\<close>

lemma paper_R_identity_valuation_application_classes:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and predicate: "F \<in> paper_R_closed_terms \<Omega> G (Arr \<sigma> Prop)"
    and argument: "A \<in> paper_R_closed_terms \<Omega> G \<sigma>"
  shows "paper_R_identity_valuation M (paper_R_identity_application \<Omega> G M \<sigma> Prop
    (paper_R_identity_class \<Omega> G M (Arr \<sigma> Prop) F) (paper_R_identity_class \<Omega> G M \<sigma> A))
    \<longleftrightarrow> NApp F A \<in> M"
  by (simp only: paper_R_identity_application_classes[where S=M, OF rich predicate argument]
    paper_R_identity_valuation_class[OF rich Henkin paper_R_closed_terms_App[OF predicate argument]])

section \<open>The quantifier laws range over all identity-domain values\<close>

text \<open>
  V([∃σF]) iff some X∈Dσ satisfies V(app([F],X));
  V([∀σF]) iff every X∈Dσ satisfies V(app([F],X)).
  Source: Theorem 3.2, footnote 64, p.45.

  Dσ is the image of ALL closed terms under theorem-identity classes.
  Consequently an arbitrary domain value is handled by its proved
  representative, not assumed to have a constant representative.
  Constants are used only where the Henkin witness property supplies
  a counterexample or existential witness. No canonical interpretation
  J or semantic BBK quantifier law is assumed here.
\<close>

theorem paper_R_identity_valuation_exists_class:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and predicate: "F \<in> paper_R_closed_terms \<Omega> G (Arr \<sigma> Prop)"
  shows "paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop (named_paper_ex \<sigma> F)) \<longleftrightarrow>
    (\<exists>X\<in>paper_R_identity_domain \<Omega> G M \<sigma>. paper_R_identity_valuation M
      (paper_R_identity_application \<Omega> G M \<sigma> Prop (paper_R_identity_class \<Omega> G M (Arr \<sigma> Prop) F) X))"
proof -
  let ?V = "\<lambda>X. paper_R_identity_valuation M
    (paper_R_identity_application \<Omega> G M \<sigma> Prop (paper_R_identity_class \<Omega> G M (Arr \<sigma> Prop) F) X)"
  have arguments: "(\<exists>A\<in>paper_R_closed_terms \<Omega> G \<sigma>. NApp F A \<in> M) \<longleftrightarrow>
    (\<exists>X\<in>paper_R_identity_domain \<Omega> G M \<sigma>. ?V X)"
  proof
    assume some: "\<exists>A\<in>paper_R_closed_terms \<Omega> G \<sigma>. NApp F A \<in> M"
    obtain A where ac: "A \<in> paper_R_closed_terms \<Omega> G \<sigma>" and member: "NApp F A \<in> M" using some by blast
    have truth: "?V (paper_R_identity_class \<Omega> G M \<sigma> A)"
      by (rule iffD2[OF paper_R_identity_valuation_application_classes[OF rich Henkin predicate ac] member])
    show "\<exists>X\<in>paper_R_identity_domain \<Omega> G M \<sigma>. ?V X"
      by (rule bexI[where x="paper_R_identity_class \<Omega> G M \<sigma> A"], rule truth,
        rule paper_R_identity_domainI[OF ac])
  next
    assume some: "\<exists>X\<in>paper_R_identity_domain \<Omega> G M \<sigma>. ?V X"
    obtain X where xd: "X \<in> paper_R_identity_domain \<Omega> G M \<sigma>" and truth: "?V X" using some by blast
    have ac: "paper_R_identity_rep X \<in> paper_R_closed_terms \<Omega> G \<sigma>"
      by (rule paper_R_identity_rep_closed_terms[OF xd])
    have membership: "NApp F (paper_R_identity_rep X) \<in> M"
      using paper_R_identity_valuation_application_classes[OF rich Henkin predicate ac] truth
      by (simp only: paper_R_identity_class_rep[OF rich xd]; blast)
    show "\<exists>A\<in>paper_R_closed_terms \<Omega> G \<sigma>. NApp F A \<in> M"
      by (rule bexI[where x="paper_R_identity_rep X"], rule membership, rule ac)
  qed
  show ?thesis by (simp only: paper_R_identity_valuation_class[OF rich Henkin paper_R_closed_terms_Ex[OF predicate]]
    paper_R_closed_Henkin_exists_member[OF rich Henkin predicate]; rule arguments)
qed

theorem paper_R_identity_valuation_forall_class:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
    and predicate: "F \<in> paper_R_closed_terms \<Omega> G (Arr \<sigma> Prop)"
  shows "paper_R_identity_valuation M (paper_R_identity_class \<Omega> G M Prop (named_paper_all \<sigma> F)) \<longleftrightarrow>
    (\<forall>X\<in>paper_R_identity_domain \<Omega> G M \<sigma>. paper_R_identity_valuation M
      (paper_R_identity_application \<Omega> G M \<sigma> Prop (paper_R_identity_class \<Omega> G M (Arr \<sigma> Prop) F) X))"
proof -
  let ?V = "\<lambda>X. paper_R_identity_valuation M
    (paper_R_identity_application \<Omega> G M \<sigma> Prop (paper_R_identity_class \<Omega> G M (Arr \<sigma> Prop) F) X)"
  have arguments: "(\<forall>A\<in>paper_R_closed_terms \<Omega> G \<sigma>. NApp F A \<in> M) \<longleftrightarrow>
    (\<forall>X\<in>paper_R_identity_domain \<Omega> G M \<sigma>. ?V X)"
  proof
    assume every: "\<forall>A\<in>paper_R_closed_terms \<Omega> G \<sigma>. NApp F A \<in> M"
    show "\<forall>X\<in>paper_R_identity_domain \<Omega> G M \<sigma>. ?V X"
    proof (intro ballI)
      fix X
      assume xd: "X \<in> paper_R_identity_domain \<Omega> G M \<sigma>"
      have ac: "paper_R_identity_rep X \<in> paper_R_closed_terms \<Omega> G \<sigma>"
        by (rule paper_R_identity_rep_closed_terms[OF xd])
      have membership: "NApp F (paper_R_identity_rep X) \<in> M" using every ac by blast
      have truth: "?V (paper_R_identity_class \<Omega> G M \<sigma> (paper_R_identity_rep X))"
        by (rule iffD2[OF paper_R_identity_valuation_application_classes[OF rich Henkin predicate ac] membership])
      show "?V X" using truth by (simp only: paper_R_identity_class_rep[OF rich xd])
    qed
  next
    assume every: "\<forall>X\<in>paper_R_identity_domain \<Omega> G M \<sigma>. ?V X"
    show "\<forall>A\<in>paper_R_closed_terms \<Omega> G \<sigma>. NApp F A \<in> M"
    proof (intro ballI)
      fix A
      assume ac: "A \<in> paper_R_closed_terms \<Omega> G \<sigma>"
      have xd: "paper_R_identity_class \<Omega> G M \<sigma> A \<in> paper_R_identity_domain \<Omega> G M \<sigma>"
        by (rule paper_R_identity_domainI[OF ac])
      have truth: "?V (paper_R_identity_class \<Omega> G M \<sigma> A)" using every xd by blast
      show "NApp F A \<in> M"
        by (rule iffD1[OF paper_R_identity_valuation_application_classes[OF rich Henkin predicate ac] truth])
    qed
  qed
  show ?thesis by (simp only: paper_R_identity_valuation_class[OF rich Henkin paper_R_closed_terms_All[OF predicate]]
    paper_R_closed_Henkin_forall_member[OF rich Henkin predicate]; rule arguments)
qed

end
