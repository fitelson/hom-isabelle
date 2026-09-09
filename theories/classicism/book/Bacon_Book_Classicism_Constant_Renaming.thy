theory Bacon_Book_Classicism_Constant_Renaming
  imports Bacon_Book_Classicism_Least_Theory
    Bacon_Book_Environment_Development.Bacon_Book_Theory_Constant_Renaming
begin

section \<open>Changing the name carrier preserves the book's C proofs\<close>

lemma book_C_rename_and_const:
  "book_constant_rename f (book_and_const G) = book_and_const G"
  by (simp only: book_and_const_def book_constant_rename_simps book_constant_rename_not book_constant_rename_imp)

lemma book_C_rename_and:
  "book_constant_rename f (book_and G A B) = book_and G (book_constant_rename f A) (book_constant_rename f B)"
  by (simp only: book_and_def book_constant_rename_simps book_C_rename_and_const)

lemma book_C_rename_iff_const:
  "book_constant_rename f (book_iff_const G) = book_iff_const G"
  by (simp only: book_iff_const_def book_constant_rename_simps book_C_rename_and book_constant_rename_imp)

lemma book_C_rename_iff:
  "book_constant_rename f (book_iff G A B) = book_iff G (book_constant_rename f A) (book_constant_rename f B)"
  by (simp only: book_iff_def book_constant_rename_simps book_C_rename_iff_const)

lemma book_C_rename_leibniz_const:
  "book_constant_rename f (book_leibniz_const G \<sigma>) = book_leibniz_const G \<sigma>"
  by (simp only: book_leibniz_const_def book_leibniz_body_def book_leibniz_matrix_def
    book_constant_rename_simps book_constant_rename_all book_C_rename_iff)

lemma book_C_rename_leibniz:
  "book_constant_rename f (book_leibniz G \<sigma> R S) =
    book_leibniz G \<sigma> (book_constant_rename f R) (book_constant_rename f S)"
  by (simp only: book_leibniz_def book_constant_rename_simps book_C_rename_leibniz_const)

lemma book_C_rename_vector:
  "book_constant_rename f (book_vector_application R ns) = book_vector_application (book_constant_rename f R) ns"
  by (induction ns arbitrary: R) (simp_all add: book_vector_application_def)

lemma book_C_rename_equivalence_instance:
  assumes original: "book_equivalence_rule_instance \<Sigma> G ns R S"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> f c \<in> \<Omega> \<tau>"
  shows "book_equivalence_rule_instance \<Omega> G ns (book_constant_rename f R) (book_constant_rename f S)"
proof -
  have distinct: "distinct ns" and fresh: "set ns \<inter> (named_fv R \<union> named_fv S) = {}"
    and rl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G R (foldr Arr (map G ns) Prop)"
    and sl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G S (foldr Arr (map G ns) Prop)"
    using original unfolding book_equivalence_rule_instance_def by blast+
  show ?thesis unfolding book_equivalence_rule_instance_def
    by (simp only: book_constant_rename_fv; rule conjI[OF distinct], rule conjI[OF fresh],
      rule conjI[OF book_constant_rename_language[OF rl maps] book_constant_rename_language[OF sl maps]])
qed

theorem book_C_constant_rename:
  assumes rich: "sg_rich G" and derivation: "book_C_proves \<Sigma> G A"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> f c \<in> \<Omega> \<tau>"
  shows "book_C_proves \<Omega> G (book_constant_rename f A)"
  using derivation
proof (induction rule: book_C_proves.induct)
  case (H A)
  have base: "book_theory_derivable \<Sigma> G {} A" using H.hyps by (simp only: book_H_iff_theory[OF rich])
  have mapped: "book_theory_derivable \<Omega> G {} (book_constant_rename f A)"
    by (rule book_theory_constant_rename_empty[OF base maps])
  show ?case by (rule book_C_from_empty_theory[OF rich mapped])
next
  case (MP A B)
  have implication: "book_C_proves \<Omega> G (book_imp (book_constant_rename f A) (book_constant_rename f B))"
    using MP.IH(2) by (simp only: book_constant_rename_imp)
  show ?case by (rule book_C_proves.MP[OF MP.IH(1) implication book_constant_rename_language[OF MP.hyps(3) maps]])
next
  case (Gen A B n)
  have implication: "book_C_proves \<Omega> G (book_imp (book_constant_rename f A) (book_constant_rename f B))"
    using Gen.IH by (simp only: book_constant_rename_imp)
  have fresh: "n \<notin> named_fv (book_constant_rename f A)"
    by (simp only: book_constant_rename_fv; rule Gen.hyps(4))
  show ?case
    by (simp only: book_constant_rename_imp book_constant_rename_all;
      rule book_C_proves.Gen[OF implication book_constant_rename_language[OF Gen.hyps(2) maps]
        book_constant_rename_language[OF Gen.hyps(3) maps] fresh])
next
  case (Equivalence R ns S)
  have premise: "book_C_proves \<Omega> G (book_iff G (book_vector_application (book_constant_rename f R) ns)
    (book_vector_application (book_constant_rename f S) ns))"
    using Equivalence.IH by (simp only: book_C_rename_iff book_C_rename_vector)
  show ?case
    by (simp only: book_C_rename_leibniz; rule book_C_proves.Equivalence[OF premise
      book_C_rename_equivalence_instance[OF Equivalence.hyps(2) maps]])
qed

text \<open>
  The source and target name carriers may differ. This forward proof
  needs only declared-name preservation, not injectivity. It leaves all
  variable names, logical symbols and Equivalence freshness conditions
  unchanged. Injective reflection is a separate theorem.
\<close>

end
