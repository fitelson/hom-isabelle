theory Bacon_Book_Lambda_I_Conversion_Environment
  imports Bacon_Book_Lambda_I_Conversion_Denotation Bacon_Book_Lambda_I_Environment_Substitution_Conversion
begin

section \<open>The λI environment clause for the constructed denotation\<close>

text \<open>
  Internally convertible λI terms have the same closed substitution
  classes at every typed assignment: the closed λI representatives are
  substituted into every node of the chain, and equal internal classes
  are equal domain values. Together with locality this is exactly the
  environment clause of the λI model class. No model, consistency,
  Functionality or domain-nonemptiness premise is assumed.
\<close>

theorem book_lambda_I_conversion_denote_conversion:
  assumes conversion: "book_lambda_I_conv \<Sigma> G \<tau> A B"
    and typed: "book_env_typed (book_lambda_I_conversion_domain \<Sigma> G) G g"
  shows "book_lambda_I_conversion_denote \<Sigma> G g A = book_lambda_I_conversion_denote \<Sigma> G g B"
proof -
  have al: "A \<in> book_LI \<Sigma> G \<tau>" and bl: "B \<in> book_LI \<Sigma> G \<tau>"
    using book_lambda_I_conv_terms[OF conversion] by blast+
  have substituted: "book_lambda_I_conv \<Sigma> G \<tau>
      (book_environment_subst {} (book_lambda_I_conversion_representatives g) A)
      (book_environment_subst {} (book_lambda_I_conversion_representatives g) B)"
    by (rule book_lambda_I_environment_subst_conv[OF _ _ conversion];
        rule book_lambda_I_conversion_representatives_LI[OF typed]
          book_lambda_I_conversion_representatives_closed[OF typed])
  show ?thesis
    by (simp only: book_lambda_I_conversion_denote_eq[OF book_language_type[OF book_lambda_I_terms_language[OF al]]]
        book_lambda_I_conversion_denote_eq[OF book_language_type[OF book_lambda_I_terms_language[OF bl]]];
        rule book_lambda_I_conversion_class_eq[OF substituted])
qed

theorem book_lambda_I_conversion_environment:
  assumes conversion: "book_lambda_I_conv \<Sigma> G \<tau> A B"
    and gt: "book_env_typed (book_lambda_I_conversion_domain \<Sigma> G) G g"
    and ht: "book_env_typed (book_lambda_I_conversion_domain \<Sigma> G) G h"
    and agree: "\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> g n = h n"
  shows "book_lambda_I_conversion_denote \<Sigma> G g A = book_lambda_I_conversion_denote \<Sigma> G h B"
proof -
  have same_fv: "named_fv A = named_fv B" by (rule book_lambda_I_conv_fv[OF conversion])
  have local: "book_lambda_I_conversion_denote \<Sigma> G g A = book_lambda_I_conversion_denote \<Sigma> G h A"
    by (rule book_lambda_I_conversion_denote_locality; rule agree; simp add: same_fv)
  have converted: "book_lambda_I_conversion_denote \<Sigma> G h A = book_lambda_I_conversion_denote \<Sigma> G h B"
    by (rule book_lambda_I_conversion_denote_conversion[OF conversion ht])
  show ?thesis by (rule trans[OF local converted])
qed

end
