theory Bacon_Book_Conversion_Expanded_Model_Existence
  imports Bacon_Book_Conversion_Model Bacon_Book_Conversion_Truth_Projection
    Bacon_Book_Closed_Henkin_Extension Bacon_Book_Universal_Closure_Truth
begin

section \<open>Original formulas hold in the expanded model\<close>

text \<open>
  Every A∈S holds at every typed assignment in the constructed model
  of Σ∞, with its constants embedded by BookOriginal. The completed set
  contains UC(Original(A)); closed truth is membership, and the proved
  all-assignment universal-closure equivalence recovers Original(A).
  Thus S may be open, infinite, and over an arbitrary signature.
  Source role: the arbitrary-theory conclusion sought in Theorem 15.3,
  p.320, at the expanded-signature stage. Pullback to the original name
  carrier and signature is a separate final transport, not assumed here.
\<close>

theorem book_henkin_conversion_original_valid:
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and maximal: "book_closed_maximal_extension (book_henkin_full_signature \<Sigma> G) G
      (book_henkin_closed_premises \<Sigma> G S) M"
    and witnesses: "book_closed_constant_witness_complete (book_henkin_full_signature \<Sigma> G) G M"
    and member: "A \<in> S"
  shows "book_formula_valid (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G) G
    (book_conversion_denote (book_henkin_full_signature \<Sigma> G) G)
    (book_conversion_valuation M) (book_constant_rename BookOriginal A)"
proof -
  let ?\<Omega> = "book_henkin_full_signature \<Sigma> G"
  let ?D = "book_conversion_domain ?\<Omega> G"
  let ?J = "book_conversion_denote ?\<Omega> G"
  let ?A = "book_constant_rename BookOriginal A"
  interpret Model: book_full_minimal_model ?D "book_conversion_app ?\<Omega> G" ?\<Omega> G ?J
    "book_conversion_valuation M" "book_conversion_logical_value ?\<Omega> G"
    by (rule book_henkin_conversion_model[OF rich maximal witnesses])
  have original_image: "?A \<in> image (book_constant_rename BookOriginal) S"
    by (rule imageI[OF member])
  have in_full: "?A \<in> book_henkin_full_premises \<Sigma> G S"
    by (rule subsetD[OF book_henkin_original_in_full original_image])
  have al: "book_theory_formula ?\<Omega> G ?A"
    by (rule book_henkin_full_premises_language[OF rich language in_full])
  have ul: "book_theory_formula ?\<Omega> G (book_universal_closure G ?A)"
    by (rule book_universal_closure_language[OF al])
  have uc: "named_fv (book_universal_closure G ?A) = {}"
    by (rule book_universal_closure_closed)
  have um: "book_universal_closure G ?A \<in> M"
    by (rule book_closed_henkin_original[OF maximal member])
  have uv: "book_formula_valid ?D G ?J (book_conversion_valuation M) (book_universal_closure G ?A)"
    by (rule iffD2[OF book_henkin_conversion_closed_valid_iff[OF rich maximal ul uc] um])
  show ?thesis by (rule iffD1[OF Model.book_formula_valid_universal_closure_iff[OF al] uv])
qed

theorem book_henkin_expanded_model_exists:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_theory_consistent \<Sigma> G S"
  shows "\<exists>M. book_full_minimal_model
      (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G)
      (book_conversion_app (book_henkin_full_signature \<Sigma> G) G)
      (book_henkin_full_signature \<Sigma> G) G
      (book_conversion_denote (book_henkin_full_signature \<Sigma> G) G)
      (book_conversion_valuation M)
      (book_conversion_logical_value (book_henkin_full_signature \<Sigma> G) G) \<and>
    (\<forall>A\<in>S. book_formula_valid (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G) G
      (book_conversion_denote (book_henkin_full_signature \<Sigma> G) G)
      (book_conversion_valuation M) (book_constant_rename BookOriginal A))"
proof -
  obtain M where maximal: "book_closed_maximal_extension (book_henkin_full_signature \<Sigma> G) G
      (book_henkin_closed_premises \<Sigma> G S) M"
    and witnesses: "book_closed_constant_witness_complete (book_henkin_full_signature \<Sigma> G) G M"
    using book_closed_henkin_extension_exists[OF rich language consistent] by blast
  show ?thesis
    by (rule exI[where x=M], rule conjI[OF book_henkin_conversion_model[OF rich maximal witnesses]],
        rule ballI, rule book_henkin_conversion_original_valid[OF rich language maximal witnesses], assumption)
qed

end
