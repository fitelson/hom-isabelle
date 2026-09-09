theory Bacon_Book_C_Typed_Name_Map
  imports Bacon_Book_H_Typed_Name_Map Bacon_Book_Classicism_Least_Theory
begin

section \<open>The complete book C calculus preserves type-indexed name maps\<close>

lemma book_C_typed_rename_and_const:
  "book_typed_name_map \<rho> (book_and_const G) = book_and_const G"
  by (simp only: book_and_const_def book_typed_name_map.simps book_typed_name_map_not book_typed_name_map_imp)

lemma book_C_typed_rename_and:
  "book_typed_name_map \<rho> (book_and G A B) = book_and G (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B)"
  by (simp only: book_and_def book_typed_name_map.simps book_C_typed_rename_and_const)

lemma book_C_typed_rename_iff_const:
  "book_typed_name_map \<rho> (book_iff_const G) = book_iff_const G"
  by (simp only: book_iff_const_def book_typed_name_map.simps book_C_typed_rename_and book_typed_name_map_imp)

lemma book_C_typed_rename_iff:
  "book_typed_name_map \<rho> (book_iff G A B) = book_iff G (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B)"
  by (simp only: book_iff_def book_typed_name_map.simps book_C_typed_rename_iff_const)

lemma book_C_typed_rename_leibniz_const:
  "book_typed_name_map \<rho> (book_leibniz_const G \<sigma>) = book_leibniz_const G \<sigma>"
  by (simp only: book_leibniz_const_def book_leibniz_body_def book_leibniz_matrix_def
    book_typed_name_map.simps book_typed_name_map_all book_C_typed_rename_iff)

lemma book_C_typed_rename_leibniz:
  "book_typed_name_map \<rho> (book_leibniz G \<sigma> R S) =
    book_leibniz G \<sigma> (book_typed_name_map \<rho> R) (book_typed_name_map \<rho> S)"
  by (simp only: book_leibniz_def book_typed_name_map.simps book_C_typed_rename_leibniz_const)

lemma book_C_typed_rename_vector:
  "book_typed_name_map \<rho> (book_vector_application R ns) = book_vector_application (book_typed_name_map \<rho> R) ns"
  by (induction ns arbitrary: R) (simp_all add: book_vector_application_def)

lemma book_C_typed_rename_equivalence_instance:
  assumes original: "book_equivalence_rule_instance \<Sigma> G ns R S"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> \<rho> \<tau> c \<in> \<Omega> \<tau>"
  shows "book_equivalence_rule_instance \<Omega> G ns (book_typed_name_map \<rho> R) (book_typed_name_map \<rho> S)"
proof -
  have distinct: "distinct ns" and fresh: "set ns \<inter> (named_fv R \<union> named_fv S) = {}"
    and rl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G R (foldr Arr (map G ns) Prop)"
    and sl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G S (foldr Arr (map G ns) Prop)"
    using original unfolding book_equivalence_rule_instance_def by blast+
  show ?thesis unfolding book_equivalence_rule_instance_def
    by (simp only: book_typed_name_map_fv; rule conjI[OF distinct], rule conjI[OF fresh],
      rule conjI[OF book_typed_name_map_language[OF rl maps] book_typed_name_map_language[OF sl maps]])
qed

theorem book_C_typed_name_map:
  assumes rich: "sg_rich G" and derivation: "book_C_proves \<Sigma> G A"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> \<rho> \<tau> c \<in> \<Omega> \<tau>"
  shows "book_C_proves \<Omega> G (book_typed_name_map \<rho> A)"
  using derivation
proof (induction rule: book_C_proves.induct)
  case (H A)
  have base: "book_theory_derivable \<Sigma> G {} A" using H.hyps by (simp only: book_H_iff_theory[OF rich])
  have mapped: "book_theory_derivable \<Omega> G {} (book_typed_name_map \<rho> A)"
    using book_theory_typed_name_map[OF base maps] by (simp only: image_empty)
  show ?case by (rule book_C_from_empty_theory[OF rich mapped])
next
  case (MP A B)
  have implication: "book_C_proves \<Omega> G (book_imp (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B))"
    using MP.IH(2) by (simp only: book_typed_name_map_imp)
  show ?case by (rule book_C_proves.MP[OF MP.IH(1) implication book_typed_name_map_language[OF MP.hyps(3) maps]])
next
  case (Gen A B n)
  have implication: "book_C_proves \<Omega> G (book_imp (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B))"
    using Gen.IH by (simp only: book_typed_name_map_imp)
  have fresh: "n \<notin> named_fv (book_typed_name_map \<rho> A)"
    by (simp only: book_typed_name_map_fv; rule Gen.hyps(4))
  show ?case
    by (simp only: book_typed_name_map_imp book_typed_name_map_all;
      rule book_C_proves.Gen[OF implication book_typed_name_map_language[OF Gen.hyps(2) maps]
        book_typed_name_map_language[OF Gen.hyps(3) maps] fresh])
next
  case (Equivalence R ns S)
  have premise: "book_C_proves \<Omega> G (book_iff G (book_vector_application (book_typed_name_map \<rho> R) ns)
    (book_vector_application (book_typed_name_map \<rho> S) ns))"
    using Equivalence.IH by (simp only: book_C_typed_rename_iff book_C_typed_rename_vector)
  show ?case
    by (simp only: book_C_typed_rename_leibniz; rule book_C_proves.Equivalence[OF premise
      book_C_typed_rename_equivalence_instance[OF Equivalence.hyps(2) maps]])
qed

text \<open>
  Only nonlogical names change. The same variable stock, full-F types,
  literal logical operators and fresh Equivalence arguments are retained.
  The H case invokes the separately proved nine-constructor transport;
  no paper/R calculus or semantic completeness is used.
\<close>

end

