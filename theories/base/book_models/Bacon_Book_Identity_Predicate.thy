theory Bacon_Book_Identity_Predicate
  imports Bacon_Book_Full_Environment
begin

section \<open>The identity operation is an available testing predicate\<close>

text \<open>
  The denotation of λx:σ.x acts as the identity on Dσ. At σ = t it
  is a predicate that tests the valuation of a proposition itself.
  This is the identity-predicate step needed for valuation invariance
  under Leibniz equivalence (Bacon, Exercise 15.5, p.321).

  We work in the full typed λ-language and retain a typed assignment g
  as an explicit premise. Richness supplies a variable of the desired
  type, not an assignment or a logical valuation. The result concerns
  application behavior; it does not assert a unique identity denotation
  or Functionality, and it uses no logical truth clauses.
\<close>

context book_full_environment
begin

lemma book_identity_denotation_type:
  assumes typed: "book_env_typed domain stock g"
  shows "denote g (NLam n (NVar n)) \<in> domain (Arr (stock n) (stock n))"
  by (rule denote_type[OF UNIV_I book_language_Lam[OF book_language_Var] typed])

lemma book_identity_denotation_application:
  assumes typed: "book_env_typed domain stock g" and member: "a \<in> domain (stock n)"
  shows "app (stock n) (stock n) (denote g (NLam n (NVar n))) a = a"
proof -
  have ht: "book_env_typed domain stock (g(n := a))"
    by (rule book_env_update[OF typed member])
  have application: "app (stock n) (stock n) (denote g (NLam n (NVar n))) a =
    denote (g(n := a)) (NVar n)"
    by (rule book_full_lambda_application[OF book_language_Var typed member])
  have variable_eq: "denote (g(n := a)) (NVar n) = a"
    using denote_var[where n=n, OF UNIV_I ht] by simp
  show ?thesis by (rule trans[OF application variable_eq])
qed

theorem book_identity_operation_exists:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
  shows "\<exists>i \<in> domain (Arr \<sigma> \<sigma>). \<forall>a \<in> domain \<sigma>. app \<sigma> \<sigma> i a = a"
proof -
  obtain n where nt: "stock n = \<sigma>" by (rule sg_rich_variable[OF rich])
  let ?i = "denote g (NLam n (NVar n))"
  have member: "?i \<in> domain (Arr \<sigma> \<sigma>)"
    using book_identity_denotation_type[where n=n, OF typed] by (simp only: nt)
  have behavior: "\<forall>a \<in> domain \<sigma>. app \<sigma> \<sigma> ?i a = a"
  proof (intro ballI)
    fix a
    assume am: "a \<in> domain \<sigma>"
    have an: "a \<in> domain (stock n)" using am by (simp only: nt)
    show "app \<sigma> \<sigma> ?i a = a"
      using book_identity_denotation_application[where n=n, OF typed an] by (simp only: nt)
  qed
  show ?thesis by (rule bexI[where x="?i"]; fact)
qed

end

end
