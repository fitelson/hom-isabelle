theory Bacon_Book_General_Interpretation
  imports Bacon_Book_General_Lambda_Language Bacon_Book_General_Application
begin

section \<open>Interpreting a language satisfying the source closure conditions\<close>

text \<open>
  Combine the independently stated language conditions with the environment
  clauses, including application to variables omitted from the language.
  The admitted raw set is ⋃τ.𝒥τ; the language clauses retain its exact
  typing. Source role: Definitions 9.1 and 14.13, pp.190 and 302.

  This is an interpretation interface, not a claim that every general
  language or every applicative structure has such an interpretation.
  The environment still uses the established raw typed conversion relation;
  its reverse correspondence with printed-guard, α-inclusive conversion
  remains a separately tracked syntactic bridge.
\<close>

locale book_general_interpretation =
  book_general_lambda_language L \<Lambda> \<Sigma> G J +
  book_general_environment_conditions domain app L \<Lambda> \<Sigma> G "\<Union>(range J)" denote
  for L :: "'l \<Rightarrow> otype" and \<Lambda> :: "'l set" and \<Sigma> :: "'c ssignature"
    and G :: sgcontext and J :: "otype \<Rightarrow> ('c,'l) named_term set"
    and domain :: "otype \<Rightarrow> 'v set"
    and app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v"
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> ('c,'l) named_term \<Rightarrow> 'v"
begin

theorem book_general_interpretation_application:
  assumes member: "NApp F A \<in> J \<tau>"
    and typed: "book_env_typed domain G g"
  obtains \<sigma> where "F \<in> J (Arr \<sigma> \<tau>)"
    and "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
    and "denote g (NApp F A) = app \<sigma> \<tau> (denote g F) (book_argument_value denote g A)"
proof -
  obtain \<sigma> where fm: "F \<in> J (Arr \<sigma> \<tau>)"
    and al: "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
    and am: "A \<in> J \<sigma> \<or> (\<exists>n. A = NVar n)"
    by (rule book_general_application_parts[OF member]; rule that; assumption)
  have head_member: "F \<in> \<Union>(range J)" using fm by blast
  have app_member: "NApp F A \<in> \<Union>(range J)" using member by blast
  have admissible: "A \<in> \<Union>(range J) \<or> (\<exists>n. A = NVar n)" using am by blast
  have equation: "denote g (NApp F A) = app \<sigma> \<tau> (denote g F) (book_argument_value denote g A)"
    by (rule book_general_denote_app[OF head_member app_member term_language[OF fm] al typed admissible])
  show thesis by (rule that[OF fm al equation])
qed

end

theorem book_general_interpretation_restrict_full:
  assumes language: "book_general_lambda_language L \<Lambda> \<Sigma> G J"
    and full: "book_full_environment D app L \<Lambda> \<Sigma> G denote"
  shows "book_general_interpretation L \<Lambda> \<Sigma> G J D app denote"
proof -
  interpret Language: book_general_lambda_language L \<Lambda> \<Sigma> G J by (rule language)
  interpret Full: book_full_environment D app L \<Lambda> \<Sigma> G denote by (rule full)
  interpret Restricted: book_general_environment_conditions D app L \<Lambda> \<Sigma> G "\<Union>(range J)" denote
    by (rule Full.book_full_environment_general_restriction)
  show ?thesis by unfold_locales
qed

end
