theory Bacon_Book_Lambda_I_Closed_Henkin_Extension
  imports Bacon_Book_Lambda_I_Henkin_Union Bacon_Book_Lambda_I_Universal_Closure_Theories Bacon_Book_Lambda_I_Closed_Witness_Completeness
begin

section \<open>Universal closures of the constructed full premises\<close>

text \<open>
  Let P∞ be the consistent union of the actual witness stages and
  C={UC(A): A∈P∞}. The set C contains only typed closed formulas
  and has the same theory consequences as P∞. Zorn's lemma therefore
  gives a maximal consistent CLOSED-formula extension M of C.
  Source role: assembling the repaired closed-decision route through
  Bacon's Proposition 15.4 and Definition 15.3, p.319.

  The original S may be open and infinite. Its preserved members in M
  are UC(Original(A)), not raw open A. No global-theory or model-existence
  conclusion is asserted.
\<close>

definition book_lambda_I_henkin_closed_premises ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow>
    ('c book_henkin_name) book_named_term set" where
  "book_lambda_I_henkin_closed_premises \<Sigma> G S =
    image (book_lambda_I_universal_closure G) (book_lambda_I_henkin_full_premises \<Sigma> G S)"

lemma book_lambda_I_henkin_closed_premises_closed_set:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
  shows "book_lambda_I_closed_formula_set (book_lambda_I_henkin_full_signature \<Sigma> G) G
    (book_lambda_I_henkin_closed_premises \<Sigma> G S)"
proof (unfold book_lambda_I_closed_formula_set_def, rule ballI)
  fix C
  assume member: "C \<in> book_lambda_I_henkin_closed_premises \<Sigma> G S"
  obtain A where original: "A \<in> book_lambda_I_henkin_full_premises \<Sigma> G S"
    and shape: "C = book_lambda_I_universal_closure G A"
    using member unfolding book_lambda_I_henkin_closed_premises_def by blast
  have al: "book_lambda_I_formula (book_lambda_I_henkin_full_signature \<Sigma> G) G A"
    by (rule book_lambda_I_henkin_full_premises_language[OF rich language original])
  have cl: "book_lambda_I_formula (book_lambda_I_henkin_full_signature \<Sigma> G) G C"
    by (simp only: shape; rule book_lambda_I_universal_closure_language[OF al])
  have closed: "named_fv C = {}" by (simp only: shape; rule book_lambda_I_universal_closure_closed)
  show "book_lambda_I_formula (book_lambda_I_henkin_full_signature \<Sigma> G) G C \<and> named_fv C = {}"
    by (rule conjI[OF cl closed])
qed

lemma book_lambda_I_henkin_closed_premises_consistent:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
    and consistent: "book_lambda_I_consistent \<Sigma> G S"
  shows "book_lambda_I_consistent (book_lambda_I_henkin_full_signature \<Sigma> G) G
    (book_lambda_I_henkin_closed_premises \<Sigma> G S)"
proof -
  let ?\<Omega> = "book_lambda_I_henkin_full_signature \<Sigma> G"
  let ?P = "book_lambda_I_henkin_full_premises \<Sigma> G S"
  have full_language: "book_lambda_I_formula ?\<Omega> G A" if "A \<in> ?P" for A
    by (rule book_lambda_I_henkin_full_premises_language[OF rich language that])
  have full_consistent: "book_lambda_I_consistent ?\<Omega> G ?P"
    by (rule book_lambda_I_henkin_full_premises_consistent[OF rich language consistent])
  have equivalence: "book_lambda_I_derivable ?\<Omega> G
      (book_lambda_I_henkin_closed_premises \<Sigma> G S) (book_bottom G) \<longleftrightarrow>
    book_lambda_I_derivable ?\<Omega> G ?P (book_bottom G)"
    unfolding book_lambda_I_henkin_closed_premises_def
    by (rule book_lambda_I_universal_closures_equivalent[OF rich full_language])
  show ?thesis using equivalence full_consistent unfolding book_lambda_I_consistent_def by blast
qed

lemma book_lambda_I_closed_henkin_maximal_exists:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
    and consistent: "book_lambda_I_consistent \<Sigma> G S"
  shows "\<exists>M. book_lambda_I_closed_maximal_extension (book_lambda_I_henkin_full_signature \<Sigma> G) G
    (book_lambda_I_henkin_closed_premises \<Sigma> G S) M"
  by (rule book_lambda_I_closed_maximal_extension_exists[
    OF book_lambda_I_henkin_closed_premises_closed_set[OF rich language]
      book_lambda_I_henkin_closed_premises_consistent[OF rich language consistent]])

section \<open>Original closures and conditional witnesses survive maximal extension\<close>

lemma book_lambda_I_closed_henkin_original:
  assumes maximal: "book_lambda_I_closed_maximal_extension (book_lambda_I_henkin_full_signature \<Sigma> G) G
      (book_lambda_I_henkin_closed_premises \<Sigma> G S) M"
    and member: "A \<in> S"
  shows "book_lambda_I_universal_closure G (book_constant_rename BookOriginal A) \<in> M"
proof -
  have original_image: "book_constant_rename BookOriginal A \<in> image (book_constant_rename BookOriginal) S"
    by (rule imageI[OF member])
  have in_full: "book_constant_rename BookOriginal A \<in> book_lambda_I_henkin_full_premises \<Sigma> G S"
    by (rule subsetD[OF book_lambda_I_henkin_original_in_full original_image])
  have in_closed: "book_lambda_I_universal_closure G (book_constant_rename BookOriginal A)
    \<in> book_lambda_I_henkin_closed_premises \<Sigma> G S"
    unfolding book_lambda_I_henkin_closed_premises_def by (rule imageI[OF in_full])
  have extends: "book_lambda_I_henkin_closed_premises \<Sigma> G S \<subseteq> M"
    using maximal unfolding book_lambda_I_closed_maximal_extension_def by blast
  show ?thesis by (rule subsetD[OF extends in_closed])
qed

lemma book_lambda_I_closed_henkin_conditional_witness:
  assumes maximal: "book_lambda_I_closed_maximal_extension (book_lambda_I_henkin_full_signature \<Sigma> G) G
      (book_lambda_I_henkin_closed_premises \<Sigma> G S) M"
    and predicate: "book_in_language book_minimal_logical_type UNIV
      (book_lambda_I_henkin_full_signature \<Sigma> G) G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}" and lambda_I: "book_lambda_I F"
  shows "\<exists>c\<in>book_lambda_I_henkin_full_signature \<Sigma> G \<sigma>. book_witness_axiom G \<sigma> F c \<in> M"
proof -
  obtain c where declared: "c \<in> book_lambda_I_henkin_full_signature \<Sigma> G \<sigma>"
    and in_full: "book_witness_axiom G \<sigma> F c \<in> book_lambda_I_henkin_full_premises \<Sigma> G S"
    using book_lambda_I_henkin_full_premises_witness[where S=S, OF predicate closed lambda_I] by blast
  have witness_closed: "named_fv (book_witness_axiom G \<sigma> F c) = {}"
    by (rule book_witness_axiom_closed[OF closed])
  have closure_fixed: "book_lambda_I_universal_closure G (book_witness_axiom G \<sigma> F c) =
    book_witness_axiom G \<sigma> F c"
    by (rule book_lambda_I_universal_closure_of_closed[OF witness_closed])
  have in_closed: "book_witness_axiom G \<sigma> F c \<in> book_lambda_I_henkin_closed_premises \<Sigma> G S"
  proof -
    have image_member: "book_lambda_I_universal_closure G (book_witness_axiom G \<sigma> F c)
      \<in> image (book_lambda_I_universal_closure G) (book_lambda_I_henkin_full_premises \<Sigma> G S)"
      by (rule imageI[OF in_full])
    show ?thesis using image_member by (simp only: closure_fixed book_lambda_I_henkin_closed_premises_def)
  qed
  have extends: "book_lambda_I_henkin_closed_premises \<Sigma> G S \<subseteq> M"
    using maximal unfolding book_lambda_I_closed_maximal_extension_def by blast
  have in_M: "book_witness_axiom G \<sigma> F c \<in> M" by (rule subsetD[OF extends in_closed])
  show ?thesis by (rule bexI[where x=c], rule in_M, rule declared)
qed

section \<open>The actual closed Henkin extension\<close>

text \<open>
  Every closed λI predicate of the full λI witness signature has a declared constant
  whose conditional witness axiom lies in M. Closed negation completeness
  turns these conditionals into the closed constant-witness property.
  This completes a syntactic extension stage, not the subsequent term
  interpretation or general-model construction.
\<close>

theorem book_lambda_I_closed_henkin_extension_exists:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
    and consistent: "book_lambda_I_consistent \<Sigma> G S"
  shows "\<exists>M. book_lambda_I_closed_maximal_extension (book_lambda_I_henkin_full_signature \<Sigma> G) G
      (book_lambda_I_henkin_closed_premises \<Sigma> G S) M \<and>
    (\<forall>A\<in>S. book_lambda_I_universal_closure G (book_constant_rename BookOriginal A) \<in> M) \<and>
    book_lambda_I_closed_constant_witness_complete (book_lambda_I_henkin_full_signature \<Sigma> G) G M"
proof -
  obtain M where maximal: "book_lambda_I_closed_maximal_extension (book_lambda_I_henkin_full_signature \<Sigma> G) G
      (book_lambda_I_henkin_closed_premises \<Sigma> G S) M"
    using book_lambda_I_closed_henkin_maximal_exists[OF rich language consistent] by blast
  have originals: "\<forall>A\<in>S. book_lambda_I_universal_closure G (book_constant_rename BookOriginal A) \<in> M"
    by (rule ballI, rule book_lambda_I_closed_henkin_original[OF maximal], assumption)
  have conditionals: "\<exists>c\<in>book_lambda_I_henkin_full_signature \<Sigma> G \<sigma>.
      book_witness_axiom G \<sigma> F c \<in> M"
    if predicate: "book_in_language book_minimal_logical_type UNIV
        (book_lambda_I_henkin_full_signature \<Sigma> G) G F (Arr \<sigma> Prop)"
      and closed: "named_fv F = {}" and lambda_I: "book_lambda_I F" for \<sigma> F
    by (rule book_lambda_I_closed_henkin_conditional_witness[OF maximal predicate closed lambda_I])
  have witnesses: "book_lambda_I_closed_constant_witness_complete (book_lambda_I_henkin_full_signature \<Sigma> G) G M"
    by (rule book_lambda_I_closed_constant_witness_complete_from_conditionals[OF rich maximal conditionals])
  show ?thesis by (rule exI[where x=M], rule conjI[OF maximal conjI[OF originals witnesses]])
qed

end
