theory Bacon_Book_Full_Environment
  imports Bacon_Book_Lambda_Application
begin

section \<open>The full typed λ-language specialization\<close>

text \<open>
  Admitting every raw term leaves the typing, nonlogical signature and
  permitted-logical-symbol guards to select the full typed λ-language.
  This specialization supplies the explicit memberships needed by the
  abstraction theorem; it introduces no additional semantic field.
  Source: the full-language case of Definition 14.13, p.302.
\<close>

locale book_full_environment = book_environment_conditions domain app logical_type logical_signature signature stock UNIV denote
  for domain :: "otype \<Rightarrow> 'v set"
    and app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v"
    and logical_type :: "'l \<Rightarrow> otype" and logical_signature :: "'l set"
    and signature :: "'c ssignature" and stock :: sgcontext
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> ('c,'l) named_term \<Rightarrow> 'v"
begin

theorem book_full_lambda_application:
  assumes language: "book_in_language logical_type logical_signature signature stock M \<tau>"
    and typed: "book_env_typed domain stock g" and member: "a \<in> domain (stock n)"
  shows "app (stock n) \<tau> (denote g (NLam n M)) a = denote (g(n := a)) M"
  by (rule book_lambda_application[OF UNIV_I UNIV_I UNIV_I UNIV_I language typed member])

end

end
