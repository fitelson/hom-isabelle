theory Bacon_Book_Lambda_Application
  imports Bacon_Book_Environment
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Vectors
begin

section \<open>An interpreted abstraction has its required applicative behavior\<close>

text \<open>
  Appστ(Jg(λx.M),a) = Jg[a/x](M). This follows from application,
  variable interpretation, locality and literal β, not from Functionality
  or unique realization of applicative behavior. Source role: the
  interpretation consequences of Bacon's Definition 14.13, p.302.

  For a selected term collection the four needed terms are explicitly
  admitted. The full-grammar corollary can discharge those memberships.
  A typed total g and a value a of the binder's type are premises; no
  global domain-nonemptiness condition is assumed independently.
\<close>

context book_environment_conditions
begin

theorem book_lambda_application:
  assumes body_member: "M \<in> admitted"
    and abstraction_member: "NLam n M \<in> admitted"
    and variable_member: "NVar n \<in> admitted"
    and application_member: "NApp (NLam n M) (NVar n) \<in> admitted"
    and body_language: "book_in_language logical_type logical_signature signature stock M \<tau>"
    and typed: "book_env_typed domain stock g" and member: "a \<in> domain (stock n)"
  shows "app (stock n) \<tau> (denote g (NLam n M)) a = denote (g(n := a)) M"
proof -
  let ?h = "g(n := a)"
  let ?R = "NApp (NLam n M) (NVar n)"
  have ht: "book_env_typed domain stock ?h" by (rule book_env_update[OF typed member])
  have lambda_language: "book_in_language logical_type logical_signature signature stock
    (NLam n M) (Arr (stock n) \<tau>)" by (rule book_language_Lam[OF body_language])
  have variable_language: "book_in_language logical_type logical_signature signature stock (NVar n) (stock n)"
    by (rule book_language_Var)
  have redex_language: "book_in_language logical_type logical_signature signature stock ?R \<tau>"
    by (rule book_language_App[OF lambda_language variable_language])
  have raw: "named_raw_beta_eta logical_type stock \<tau> ?R M"
    by (rule named_conversion_to_raw, rule named_self_beta, rule book_language_named[OF body_language])
  have beta: "denote ?h ?R = denote ?h M"
    by (rule book_denote_conversion[OF application_member body_member redex_language body_language raw ht])
  have lambda_eq: "denote ?h (NLam n M) = denote g (NLam n M)"
  proof (rule book_denote_locality[OF abstraction_member lambda_language ht typed])
    fix k
    assume free: "k \<in> named_fv (NLam n M)"
    have distinct: "k \<noteq> n" using free by simp
    show "?h k = g k" by (simp add: distinct)
  qed
  have variable_eq: "denote ?h (NVar n) = a"
    using denote_var[OF variable_member ht] by simp
  have application: "denote ?h ?R = app (stock n) \<tau>
    (denote ?h (NLam n M)) (denote ?h (NVar n))"
    by (rule denote_app[OF abstraction_member variable_member application_member lambda_language variable_language ht])
  have evaluated: "denote ?h ?R = app (stock n) \<tau> (denote g (NLam n M)) a"
    using application by (simp only: lambda_eq variable_eq)
  show ?thesis by (rule trans[OF sym[OF evaluated] beta])
qed

end

end
