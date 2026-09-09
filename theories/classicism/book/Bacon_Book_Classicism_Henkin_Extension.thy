theory Bacon_Book_Classicism_Henkin_Extension
  imports Bacon_Book_Classicism_Henkin_Union Bacon_Book_Classicism_Universal_Closure
    Bacon_Book_Classicism_Closed_Maximal
    Bacon_Book_Environment_Development.Bacon_Book_Closed_Henkin_Extension
begin

theorem book_C_henkin_closed_premises_consistent:
  assumes rich: "sg_rich G" and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_C_theory_consistent \<Sigma> G S"
  shows "book_C_theory_consistent (book_henkin_full_signature \<Sigma> G) G (book_henkin_closed_premises \<Sigma> G S)"
proof -
  have full_language: "book_theory_formula (book_henkin_full_signature \<Sigma> G) G A"
    if "A \<in> book_henkin_full_premises \<Sigma> G S" for A
    by (rule book_henkin_full_premises_language[OF rich language that])
  have full_consistent: "book_C_theory_consistent (book_henkin_full_signature \<Sigma> G) G (book_henkin_full_premises \<Sigma> G S)"
    by (rule book_C_henkin_full_premises_consistent[OF rich language consistent])
  show ?thesis using full_consistent
    by (simp only: book_henkin_closed_premises_def book_C_consistent_universal_closures[OF rich full_language])
qed

theorem book_C_closed_henkin_extension_exists:
  assumes rich: "sg_rich G" and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_C_theory_consistent \<Sigma> G S"
  shows "\<exists>M. book_C_closed_maximal_extension (book_henkin_full_signature \<Sigma> G) G
      (book_henkin_closed_premises \<Sigma> G S) M \<and>
    book_C_theory_consistent (book_henkin_full_signature \<Sigma> G) G M \<and>
    (\<forall>A\<in>S. book_universal_closure G (book_constant_rename BookOriginal A) \<in> M) \<and>
    book_closed_constant_witness_complete (book_henkin_full_signature \<Sigma> G) G M"
proof -
  let ?\<Omega> = "book_henkin_full_signature \<Sigma> G"
  let ?P = "book_henkin_closed_premises \<Sigma> G S"
  have closed_P: "book_closed_formula_set ?\<Omega> G ?P" by (rule book_henkin_closed_premises_closed_set[OF rich language])
  have consistent_P: "book_C_theory_consistent ?\<Omega> G ?P"
    by (rule book_C_henkin_closed_premises_consistent[OF rich language consistent])
  obtain M where maximal: "book_C_closed_maximal_extension ?\<Omega> G ?P M"
    using book_C_closed_maximal_extension_exists[OF rich closed_P consistent_P] by blast
  have H_maximal: "book_closed_maximal_extension ?\<Omega> G ?P M"
    using maximal unfolding book_C_closed_maximal_extension_def book_closed_maximal_extension_def by blast
  have originals: "\<forall>A\<in>S. book_universal_closure G (book_constant_rename BookOriginal A) \<in> M"
    by (rule ballI, rule book_closed_henkin_original[OF H_maximal], assumption)
  have conditionals: "\<exists>c\<in>?\<Omega> \<sigma>. book_witness_axiom G \<sigma> F c \<in> M"
    if predicate: "book_in_language book_minimal_logical_type UNIV ?\<Omega> G F (Arr \<sigma> Prop)"
      and closed: "named_fv F = {}" for \<sigma> F
    by (rule book_closed_henkin_conditional_witness[OF H_maximal predicate closed])
  have witnesses: "book_closed_constant_witness_complete ?\<Omega> G M"
    by (rule book_closed_constant_witness_complete_from_conditionals[OF rich H_maximal conditionals])
  have consistent_M: "book_C_theory_consistent ?\<Omega> G M" by (rule book_C_closed_maximal_consistent[OF rich maximal])
  show ?thesis by (rule exI[where x=M], rule conjI[OF maximal conjI[OF consistent_M conjI[OF originals witnesses]]])
qed

text \<open>
  This is an actual witness-complete C extension in the constructed
  Henkin signature. Its C background, consistency, closed maximality,
  original universal closures and all closed-predicate witnesses are
  derived, not supplied as model fields. S may be open and infinite;
  its open formulas enter M through their universal closures.

  The name carrier has changed to book_henkin_name. A canonical
  successor theorem must still realize these extensions inside one
  fixed ambient language, preserving old names and an infinite reserve.
  No modal term interpretation or completeness theorem is asserted here.
\<close>

end
