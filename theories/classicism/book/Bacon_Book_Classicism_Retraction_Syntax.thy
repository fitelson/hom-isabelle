theory Bacon_Book_Classicism_Retraction_Syntax
  imports Bacon_Book_Classicism_Least_Theory
    Bacon_Book_Environment_Development.Bacon_Book_Theory_Retraction
begin

lemma book_C_retract_and_const:
  "named_retract \<Omega> v (book_and_const G) = book_and_const G"
  by (simp only: book_and_const_def named_retract.simps book_retract_not book_retract_imp)

lemma book_C_retract_and:
  "named_retract \<Omega> v (book_and G A B) = book_and G (named_retract \<Omega> v A) (named_retract \<Omega> v B)"
  by (simp only: book_and_def named_retract.simps book_C_retract_and_const)

lemma book_C_retract_iff_const:
  "named_retract \<Omega> v (book_iff_const G) = book_iff_const G"
  by (simp only: book_iff_const_def named_retract.simps book_C_retract_and book_retract_imp)

lemma book_C_retract_iff:
  "named_retract \<Omega> v (book_iff G A B) = book_iff G (named_retract \<Omega> v A) (named_retract \<Omega> v B)"
  by (simp only: book_iff_def named_retract.simps book_C_retract_iff_const)

lemma book_C_retract_leibniz_const:
  "named_retract \<Omega> v (book_leibniz_const G \<sigma>) = book_leibniz_const G \<sigma>"
  by (simp only: book_leibniz_const_def book_leibniz_body_def book_leibniz_matrix_def
    named_retract.simps book_retract_all book_C_retract_iff)

lemma book_C_retract_leibniz:
  "named_retract \<Omega> v (book_leibniz G \<sigma> R S) =
    book_leibniz G \<sigma> (named_retract \<Omega> v R) (named_retract \<Omega> v S)"
  by (simp only: book_leibniz_def named_retract.simps book_C_retract_leibniz_const)

lemma book_C_retract_vector:
  "named_retract \<Omega> v (book_vector_application R ns) = book_vector_application (named_retract \<Omega> v R) ns"
  by (induction ns arbitrary: R) (simp_all add: book_vector_application_def)

theorem book_C_retract_equivalence_instance:
  assumes original: "book_equivalence_rule_instance \<Sigma> G ns R S"
    and stock: "\<And>\<tau>. G (v \<tau>) = \<tau>"
    and avoid: "\<And>\<tau>. v \<tau> \<notin> set ns"
  shows "book_equivalence_rule_instance \<Omega> G ns (named_retract \<Omega> v R) (named_retract \<Omega> v S)"
proof -
  have distinct: "distinct ns" and fresh: "set ns \<inter> (named_fv R \<union> named_fv S) = {}"
    and rl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G R (foldr Arr (map G ns) Prop)"
    and sl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G S (foldr Arr (map G ns) Prop)"
    using original unfolding book_equivalence_rule_instance_def by blast+
  have new_fresh: "set ns \<inter> (named_fv (named_retract \<Omega> v R) \<union> named_fv (named_retract \<Omega> v S)) = {}"
  proof -
    have avoids_range: "set ns \<inter> range v = {}" using avoid by auto
    show ?thesis using fresh avoids_range named_retract_fv_bound[where \<Sigma>=\<Omega> and v=v and A=R]
      named_retract_fv_bound[where \<Sigma>=\<Omega> and v=v and A=S] by blast
  qed
  show ?thesis unfolding book_equivalence_rule_instance_def
    by (rule conjI[OF distinct], rule conjI[OF new_fresh],
      rule conjI[OF book_retract_language[OF rl stock] book_retract_language[OF sl stock]])
qed

text \<open>
  Foreign constants become typed variables. The literal closed logical
  operators remain fixed. Equivalence retains its original argument
  variables; the retraction variables avoid that finite list so its
  freshness condition survives. No proof-calculus preservation or model
  assumption is used in these syntax lemmas.
\<close>

end
