theory Bacon_Book_Lambda_I_Constant_Model_Pullback
  imports Bacon_Book_Lambda_I_Constant_Renaming_Conversion Bacon_Book_Lambda_I_Models
    Bacon_Book_Environment_Development.Bacon_Book_Constant_Model_Pullback
begin

section \<open>Pulling a λI model back along a constant renaming\<close>

text \<open>
  Given f[Σσ]⊆Ωσ, put J′g(A)=Jg(f(A)) with the existing pullback
  denotation. The domains, typed application, variable stock, valuation
  and logical values stay fixed. Renaming preserves λI membership and
  internal conversion, so every clause of the λI model class transfers.
  This is a forward model transport; no injectivity, richness or
  reflection is needed.
\<close>

context book_lambda_I_model
begin

lemma book_lambda_I_constant_pullback_type:
  assumes maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> f c \<in> signature \<sigma>"
    and member: "A \<in> book_LI \<Sigma> stock \<tau>"
    and typed: "book_env_typed domain stock g"
  shows "book_constant_pullback_denote denote f g A \<in> domain \<tau>"
  unfolding book_constant_pullback_denote_def
  by (rule denote_type[OF book_lambda_I_constant_rename_terms[OF member maps] typed])

lemma book_lambda_I_constant_pullback_var:
  assumes typed: "book_env_typed domain stock g"
  shows "book_constant_pullback_denote denote f g (NVar n) = g n"
  by (simp only: book_constant_pullback_denote_def book_constant_rename_simps; rule denote_var[OF typed])

lemma book_lambda_I_constant_pullback_app:
  assumes maps: "\<And>\<rho> c. c \<in> \<Sigma> \<rho> \<Longrightarrow> f c \<in> signature \<rho>"
    and head: "F \<in> book_LI \<Sigma> stock (Arr \<sigma> \<tau>)" and argument: "A \<in> book_LI \<Sigma> stock \<sigma>"
    and typed: "book_env_typed domain stock g"
  shows "book_constant_pullback_denote denote f g (NApp F A) =
    app \<sigma> \<tau> (book_constant_pullback_denote denote f g F) (book_constant_pullback_denote denote f g A)"
  by (simp only: book_constant_pullback_denote_def book_constant_rename_simps;
      rule denote_app[OF book_lambda_I_constant_rename_terms[OF head maps]
        book_lambda_I_constant_rename_terms[OF argument maps] typed])

lemma book_lambda_I_constant_pullback_environment:
  assumes maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> f c \<in> signature \<sigma>"
    and conversion: "book_lambda_I_conv \<Sigma> stock \<tau> A B"
    and gt: "book_env_typed domain stock g" and ht: "book_env_typed domain stock h"
    and overlap: "\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> g n = h n"
  shows "book_constant_pullback_denote denote f g A = book_constant_pullback_denote denote f h B"
  unfolding book_constant_pullback_denote_def
proof (rule environment[OF book_lambda_I_constant_rename_conv[OF maps conversion] gt ht])
  fix n
  assume shared: "n \<in> named_fv (book_constant_rename f A) \<inter> named_fv (book_constant_rename f B)"
  have original_shared: "n \<in> named_fv A \<inter> named_fv B"
    using shared by (simp only: book_constant_rename_fv)
  show "g n = h n" by (rule overlap[OF original_shared])
qed

lemma book_lambda_I_constant_pullback_logical:
  assumes typed: "book_env_typed domain stock g"
  shows "book_constant_pullback_denote denote f g (NLogical l) = \<kappa> l"
  by (simp only: book_constant_pullback_denote_def book_constant_rename_simps; rule logical_value[OF typed])

theorem book_lambda_I_constant_pullback_model:
  assumes maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> f c \<in> signature \<sigma>"
  shows "book_lambda_I_model domain app \<Sigma> stock (book_constant_pullback_denote denote f) V \<kappa>"
  by (unfold_locales;
      (rule app_type | rule book_lambda_I_constant_pullback_type[OF maps] |
       rule book_lambda_I_constant_pullback_var | rule book_lambda_I_constant_pullback_app[OF maps] |
       rule book_lambda_I_constant_pullback_environment[OF maps] |
       rule book_lambda_I_constant_pullback_logical | rule assignment_exists |
       rule implication_truth | rule forall_truth | rule false_proposition); assumption)

end

end
