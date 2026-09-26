theory Bacon_Book_Lambda_I_Canonical_Model_Existence
  imports Bacon_Book_Lambda_I_Conversion_Expanded_Model_Existence Bacon_Book_Lambda_I_Constant_Model_Pullback
begin

section \<open>A λI model of the original signature and unrenamed premises\<close>

text \<open>
  Retain the expanded term-class carrier, domains, App, v and κ, but
  interpret an original term A by J′g(A)=Jg(Original(A)). Original
  constant names embed in Σ∞ at their declared types, so the λI model
  pullback applies, and its conclusion interprets the ORIGINAL λI
  language and premises. The premise set may be open, infinite, and over
  an arbitrary nonlogical signature; every premise is a λI formula.
\<close>

theorem book_lambda_I_henkin_original_model_exists:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
    and consistent: "book_lambda_I_consistent \<Sigma> G S"
  shows "\<exists>M. book_lambda_I_model
      (book_lambda_I_conversion_domain (book_lambda_I_henkin_full_signature \<Sigma> G) G)
      (book_lambda_I_conversion_app (book_lambda_I_henkin_full_signature \<Sigma> G) G)
      \<Sigma> G
      (book_constant_pullback_denote (book_lambda_I_conversion_denote (book_lambda_I_henkin_full_signature \<Sigma> G) G) BookOriginal)
      (book_lambda_I_conversion_valuation M)
      (book_lambda_I_conversion_logical_value (book_lambda_I_henkin_full_signature \<Sigma> G) G) \<and>
    (\<forall>A\<in>S. book_formula_valid (book_lambda_I_conversion_domain (book_lambda_I_henkin_full_signature \<Sigma> G) G) G
      (book_constant_pullback_denote (book_lambda_I_conversion_denote (book_lambda_I_henkin_full_signature \<Sigma> G) G) BookOriginal)
      (book_lambda_I_conversion_valuation M) A)"
proof -
  let ?\<Omega> = "book_lambda_I_henkin_full_signature \<Sigma> G"
  let ?D = "book_lambda_I_conversion_domain ?\<Omega> G"
  let ?app = "book_lambda_I_conversion_app ?\<Omega> G"
  let ?J = "book_lambda_I_conversion_denote ?\<Omega> G"
  let ?k = "book_lambda_I_conversion_logical_value ?\<Omega> G"
  obtain M where model: "book_lambda_I_model ?D ?app ?\<Omega> G ?J (book_lambda_I_conversion_valuation M) ?k"
    and premise_truth: "\<forall>A\<in>S. book_formula_valid ?D G ?J (book_lambda_I_conversion_valuation M)
      (book_constant_rename BookOriginal A)"
    using book_lambda_I_henkin_expanded_model_exists[OF rich language consistent] by blast
  interpret Model: book_lambda_I_model ?D ?app ?\<Omega> G ?J "book_lambda_I_conversion_valuation M" ?k
    by (rule model)
  have maps: "BookOriginal c \<in> ?\<Omega> \<sigma>" if "c \<in> \<Sigma> \<sigma>" for \<sigma> c
    by (simp only: book_lambda_I_henkin_full_original_iff; rule that)
  have pulled: "book_lambda_I_model ?D ?app \<Sigma> G
    (book_constant_pullback_denote ?J BookOriginal) (book_lambda_I_conversion_valuation M) ?k"
    by (rule Model.book_lambda_I_constant_pullback_model[OF maps])
  have original_truth: "\<forall>A\<in>S. book_formula_valid ?D G
    (book_constant_pullback_denote ?J BookOriginal) (book_lambda_I_conversion_valuation M) A"
    using premise_truth by (simp only: book_formula_valid_def book_constant_pullback_denote_def)
  show ?thesis by (rule exI[where x=M], rule conjI[OF pulled original_truth])
qed

corollary book_lambda_I_canonical_model_existence:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
    and consistent: "book_lambda_I_consistent \<Sigma> G S"
  shows "\<exists>(D::otype \<Rightarrow> ('c book_henkin_name) book_named_term set set) app J V k.
    book_lambda_I_model D app \<Sigma> G J V k \<and>
    (\<forall>A\<in>S. book_formula_valid D G J V A)"
proof -
  obtain M where model: "book_lambda_I_model
      (book_lambda_I_conversion_domain (book_lambda_I_henkin_full_signature \<Sigma> G) G)
      (book_lambda_I_conversion_app (book_lambda_I_henkin_full_signature \<Sigma> G) G) \<Sigma> G
      (book_constant_pullback_denote (book_lambda_I_conversion_denote (book_lambda_I_henkin_full_signature \<Sigma> G) G) BookOriginal)
      (book_lambda_I_conversion_valuation M) (book_lambda_I_conversion_logical_value (book_lambda_I_henkin_full_signature \<Sigma> G) G)"
    and premise_truth: "\<forall>A\<in>S. book_formula_valid
      (book_lambda_I_conversion_domain (book_lambda_I_henkin_full_signature \<Sigma> G) G) G
      (book_constant_pullback_denote (book_lambda_I_conversion_denote (book_lambda_I_henkin_full_signature \<Sigma> G) G) BookOriginal)
      (book_lambda_I_conversion_valuation M) A"
    using book_lambda_I_henkin_original_model_exists[OF rich language consistent] by blast
  show ?thesis by (intro exI; rule conjI[OF model premise_truth])
qed

end
