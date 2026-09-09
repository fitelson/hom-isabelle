theory Bacon_Book_Classicism_Retraction
  imports Bacon_Book_Classicism_Retraction_Syntax
begin

section \<open>Finite fresh-variable support for the entire C proof\<close>

definition book_C_retraction_support where
  "book_C_retraction_support \<Omega> G A N \<longleftrightarrow> finite N \<and> named_vars A \<subseteq> N \<and>
    (\<forall>v. (\<forall>\<tau>. G (v \<tau>) = \<tau>) \<longrightarrow> (\<forall>\<tau>. v \<tau> \<notin> N) \<longrightarrow>
      book_C_proves \<Omega> G (named_retract \<Omega> v A))"

lemma book_C_retraction_supportI:
  assumes finite: "finite N" and names: "named_vars A \<subseteq> N"
    and transform: "\<And>v. (\<And>\<tau>. G (v \<tau>) = \<tau>) \<Longrightarrow> (\<And>\<tau>. v \<tau> \<notin> N) \<Longrightarrow>
      book_C_proves \<Omega> G (named_retract \<Omega> v A)"
  shows "book_C_retraction_support \<Omega> G A N"
  using finite names transform unfolding book_C_retraction_support_def by blast

lemma book_C_retraction_apply:
  assumes support: "book_C_retraction_support \<Omega> G A N"
    and stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> N"
  shows "book_C_proves \<Omega> G (named_retract \<Omega> v A)"
  using support stock fresh unfolding book_C_retraction_support_def by blast

theorem book_C_retraction_support_exists:
  assumes rich: "sg_rich G" and derivation: "book_C_proves \<Sigma> G A"
  shows "\<exists>N. book_C_retraction_support \<Omega> G A N"
  using derivation
proof (induction rule: book_C_proves.induct)
  case (H A)
  have base: "book_theory_derivable \<Sigma> G {} A" using H.hyps by (simp only: book_H_iff_theory[OF rich])
  obtain N where support: "book_theory_retraction_support \<Omega> G {} A N"
    using book_theory_derivable_retraction_support[where \<Omega>=\<Omega>, OF base] by blast
  have finite: "finite N" and names: "named_vars A \<subseteq> N"
    using support unfolding book_theory_retraction_support_def by blast+
  show ?case
  proof (rule exI[where x=N], rule book_C_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> N"
    have retracted: "book_theory_derivable \<Omega> G {} (named_retract \<Omega> v A)"
      using book_theory_retraction_support_apply[OF support stock fresh] by simp
    show "book_C_proves \<Omega> G (named_retract \<Omega> v A)" by (rule book_C_from_empty_theory[OF rich retracted])
  qed
next
  case (MP A B)
  obtain N where first: "book_C_retraction_support \<Omega> G A N" using MP.IH(1) by blast
  obtain K where second: "book_C_retraction_support \<Omega> G (book_imp A B) K" using MP.IH(2) by blast
  let ?U = "N \<union> K \<union> named_vars B"
  have finite: "finite ?U" using first second unfolding book_C_retraction_support_def by (auto intro: named_vars_finite)
  show ?case
  proof (rule exI[where x="?U"], rule book_C_retraction_supportI[OF finite Un_upper2])
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> ?U"
    have fn: "\<And>\<tau>. v \<tau> \<notin> N" and fk: "\<And>\<tau>. v \<tau> \<notin> K" using fresh by blast+
    have pa: "book_C_proves \<Omega> G (named_retract \<Omega> v A)" by (rule book_C_retraction_apply[OF first stock fn])
    have pi: "book_C_proves \<Omega> G (book_imp (named_retract \<Omega> v A) (named_retract \<Omega> v B))"
      using book_C_retraction_apply[OF second stock fk] by (simp only: book_retract_imp)
    show "book_C_proves \<Omega> G (named_retract \<Omega> v B)"
      by (rule book_C_proves.MP[OF pa pi book_retract_language[OF MP.hyps(3) stock]])
  qed
next
  case (Gen A B n)
  obtain N where support: "book_C_retraction_support \<Omega> G (book_imp A B) N" using Gen.IH by blast
  let ?C = "book_imp A (book_all G n B)"
  let ?U = "insert n (N \<union> named_vars ?C)"
  have finite: "finite ?U" using support unfolding book_C_retraction_support_def by (auto intro: named_vars_finite)
  have names: "named_vars ?C \<subseteq> ?U" by blast
  show ?case
  proof (rule exI[where x="?U"], rule book_C_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> ?U"
    have fn: "\<And>\<tau>. v \<tau> \<notin> N" and avoid: "\<And>\<tau>. v \<tau> \<noteq> n" using fresh by blast+
    have antecedent: "n \<notin> named_fv (named_retract \<Omega> v A)" by (rule named_retract_fresh[OF Gen.hyps(4) avoid])
    have premise: "book_C_proves \<Omega> G (book_imp (named_retract \<Omega> v A) (named_retract \<Omega> v B))"
      using book_C_retraction_apply[OF support stock fn] by (simp only: book_retract_imp)
    show "book_C_proves \<Omega> G (named_retract \<Omega> v ?C)"
      by (simp only: book_retract_imp book_retract_all; rule book_C_proves.Gen[OF premise
        book_retract_language[OF Gen.hyps(2) stock] book_retract_language[OF Gen.hyps(3) stock] antecedent])
  qed
next
  case (Equivalence R ns S)
  let ?P = "book_iff G (book_vector_application R ns) (book_vector_application S ns)"
  let ?C = "book_leibniz G (foldr Arr (map G ns) Prop) R S"
  obtain N where support: "book_C_retraction_support \<Omega> G ?P N" using Equivalence.IH by blast
  let ?U = "N \<union> set ns \<union> named_vars ?C"
  have finite: "finite ?U" using support unfolding book_C_retraction_support_def by (auto intro: named_vars_finite)
  show ?case
  proof (rule exI[where x="?U"], rule book_C_retraction_supportI[OF finite Un_upper2])
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> ?U"
    have fn: "\<And>\<tau>. v \<tau> \<notin> N" and avoid: "\<And>\<tau>. v \<tau> \<notin> set ns" using fresh by blast+
    have premise: "book_C_proves \<Omega> G (book_iff G (book_vector_application (named_retract \<Omega> v R) ns)
        (book_vector_application (named_retract \<Omega> v S) ns))"
      using book_C_retraction_apply[OF support stock fn] by (simp only: book_C_retract_iff book_C_retract_vector)
    have instance_ok: "book_equivalence_rule_instance \<Omega> G ns (named_retract \<Omega> v R) (named_retract \<Omega> v S)"
      by (rule book_C_retract_equivalence_instance[OF Equivalence.hyps(2) stock avoid])
    show "book_C_proves \<Omega> G (named_retract \<Omega> v ?C)"
      by (simp only: book_C_retract_leibniz; rule book_C_proves.Equivalence[OF premise instance_ok])
  qed
qed

text \<open>
  The finite support follows the complete C proof. The H case uses
  the checked H proof retraction; MP unions supports; Gen protects its
  eigenvariable; Equivalence protects every fresh argument variable.
  No model, C completeness or inhabited target signature is assumed.
  This is the proof transport needed before a fresh-witness extension
  can legitimately retain the C background in its enlarged language.
\<close>

end
