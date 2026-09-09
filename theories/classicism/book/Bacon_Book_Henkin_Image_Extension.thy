theory Bacon_Book_Henkin_Image_Extension
  imports Bacon_Book_Henkin_Image_Premises
begin

lemma book_henkin_image_original:
  assumes member: "A \<in> S" and names: "named_in_signature \<Sigma> A"
    and fixed_names: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> (BookOriginal c) = c"
  shows "book_universal_closure G A \<in> book_henkin_image_premises \<rho> \<Sigma> G S"
proof -
  have in_full: "book_constant_rename BookOriginal A \<in> book_henkin_full_premises \<Sigma> G S"
    by (rule subsetD[OF book_henkin_original_in_full]; rule imageI[OF member])
  have in_closed: "book_universal_closure G (book_constant_rename BookOriginal A) \<in> book_henkin_closed_premises \<Sigma> G S"
    unfolding book_henkin_closed_premises_def by (rule imageI[OF in_full])
  have in_image: "book_typed_name_map \<rho> (book_universal_closure G (book_constant_rename BookOriginal A)) \<in>
    book_henkin_image_premises \<rho> \<Sigma> G S"
    unfolding book_henkin_image_premises_def by (rule imageI[OF in_closed])
  show ?thesis using in_image by (simp only: book_typed_name_map_universal_closure
    book_typed_name_map_fixes_original[where \<rho>=\<rho>, OF names fixed_names])
qed

theorem book_C_henkin_image_extension_exists:
  assumes rich: "sg_rich G" and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_C_theory_consistent \<Sigma> G S"
    and injective: "\<And>\<tau>. inj_on (\<rho> \<tau>) (book_henkin_full_signature \<Sigma> G \<tau>)"
    and fixed_names: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> (BookOriginal c) = c"
  shows "\<exists>M. book_C_closed_maximal_extension (book_typed_image_signature \<rho> (book_henkin_full_signature \<Sigma> G)) G {} M \<and>
    book_C_theory_consistent (book_typed_image_signature \<rho> (book_henkin_full_signature \<Sigma> G)) G M \<and>
    (\<forall>A\<in>S. book_universal_closure G A \<in> M) \<and>
    book_closed_constant_witness_complete (book_typed_image_signature \<rho> (book_henkin_full_signature \<Sigma> G)) G M"
proof -
  let ?\<Omega> = "book_typed_image_signature \<rho> (book_henkin_full_signature \<Sigma> G)"
  let ?P = "book_henkin_image_premises \<rho> \<Sigma> G S"
  have pc: "book_C_theory_consistent ?\<Omega> G ?P"
    by (rule book_C_henkin_image_premises_consistent[OF rich language consistent injective])
  have pl: "book_closed_formula_set ?\<Omega> G ?P" by (rule book_henkin_image_premises_closed[OF rich language])
  obtain M where maximal: "book_C_closed_maximal_extension ?\<Omega> G ?P M"
    using book_C_closed_maximal_extension_exists[OF rich pl pc] by blast
  have extends: "?P \<subseteq> M" by (rule book_C_closed_maximal_data(4)[OF maximal])
  have empty_maximal: "book_C_closed_maximal_extension ?\<Omega> G {} M"
    using maximal unfolding book_C_closed_maximal_extension_def book_closed_maximal_extension_def by blast
  have H_maximal: "book_closed_maximal_extension ?\<Omega> G ?P M"
    using maximal unfolding book_C_closed_maximal_extension_def book_closed_maximal_extension_def by blast
  have conditionals: "\<exists>c\<in>?\<Omega> \<sigma>. book_witness_axiom G \<sigma> F c \<in> M"
    if predicate: "book_in_language book_minimal_logical_type UNIV ?\<Omega> G F (Arr \<sigma> Prop)"
      and closed: "named_fv F = {}" for \<sigma> F
    using book_henkin_image_conditional_witness[where \<rho>=\<rho> and S=S, OF predicate closed] extends by blast
  have witnesses: "book_closed_constant_witness_complete ?\<Omega> G M"
    by (rule book_closed_constant_witness_complete_from_conditionals[OF rich H_maximal conditionals])
  have originals: "\<forall>A\<in>S. book_universal_closure G A \<in> M"
  proof (rule ballI)
    fix A
    assume member: "A \<in> S"
    have names: "named_in_signature \<Sigma> A" by (rule book_language_signature[OF language[OF member]])
    have in_image: "book_universal_closure G A \<in> ?P"
      by (rule book_henkin_image_original[OF member names fixed_names])
    show "book_universal_closure G A \<in> M" by (rule subsetD[OF extends in_image])
  qed
  have mc: "book_C_theory_consistent ?\<Omega> G M" by (rule book_C_closed_maximal_consistent[OF rich maximal])
  show ?thesis by (rule exI[where x=M], rule conjI[OF empty_maximal conjI[OF mc conjI[OF originals witnesses]]])
qed

text \<open>
  We take a new maximal extension of the consistent image premises.
  Thus maximality is proved in the entire target language, not inferred
  merely from injectivity of a renaming. The image-premise coverage theorem
  supplies every target closed-predicate witness. Old formulas are retained
  literally through their universal closures because their declared names
  are fixed. Existence of the required map is a separate obligation.
\<close>

end
