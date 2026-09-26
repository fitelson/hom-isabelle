theory Bacon_Book_Lambda_I_Conversion_Closed_Values
  imports Bacon_Book_Lambda_I_Conversion_Denotation Bacon_Book_Lambda_I_Conversion_Domain_Inhabitation
    Bacon_Book_Lambda_I_Conversion_Logical_Values Bacon_Book_Lambda_I_Conversion_Environment
    Bacon_Book_Environment_Development.Bacon_Book_Total_Assignments
begin

section \<open>An actual total assignment in the full λI witness signature\<close>

text \<open>
  Every Dσ in the constructed full witness signature is nonempty.
  Select g₀(n)∈DG(n); this gives an actual typed total assignment,
  not a choice from a possibly empty collection of assignments.
  The λI model class records the logical-symbol clause directly as
  Jg(l)=κ(l) at every typed assignment; no separate witnessed
  closed-value convention is needed.
\<close>

definition book_lambda_I_henkin_conversion_assignment ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> nat \<Rightarrow> ('c book_henkin_name) book_named_term set" where
  "book_lambda_I_henkin_conversion_assignment \<Sigma> G n =
    (SOME X. X \<in> book_lambda_I_conversion_domain (book_lambda_I_henkin_full_signature \<Sigma> G) G (G n))"

theorem book_lambda_I_henkin_conversion_assignment_typed:
  assumes rich: "sg_rich G"
  shows "book_env_typed (book_lambda_I_conversion_domain (book_lambda_I_henkin_full_signature \<Sigma> G) G) G
    (book_lambda_I_henkin_conversion_assignment \<Sigma> G)"
proof (unfold book_env_typed_def, rule allI)
  fix n
  have nonempty: "book_lambda_I_conversion_domain (book_lambda_I_henkin_full_signature \<Sigma> G) G (G n) \<noteq> {}"
    by (rule book_lambda_I_henkin_conversion_domain_nonempty[OF rich])
  show "book_lambda_I_henkin_conversion_assignment \<Sigma> G n \<in>
    book_lambda_I_conversion_domain (book_lambda_I_henkin_full_signature \<Sigma> G) G (G n)"
    unfolding book_lambda_I_henkin_conversion_assignment_def
    by (rule book_domain_choice[where D="book_lambda_I_conversion_domain (book_lambda_I_henkin_full_signature \<Sigma> G) G"
      and \<sigma>="G n", OF nonempty])
qed

corollary book_lambda_I_henkin_conversion_assignment_exists:
  assumes rich: "sg_rich G"
  shows "\<exists>g. book_env_typed (book_lambda_I_conversion_domain (book_lambda_I_henkin_full_signature \<Sigma> G) G) G g"
  by (rule exI[where x="book_lambda_I_henkin_conversion_assignment \<Sigma> G"];
      rule book_lambda_I_henkin_conversion_assignment_typed[OF rich])

section \<open>Logical symbols denote their classes at every assignment\<close>

theorem book_lambda_I_conversion_logical_denote:
  "book_lambda_I_conversion_denote \<Sigma> G g (NLogical l) = book_lambda_I_conversion_logical_value \<Sigma> G l"
proof -
  have language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NLogical l) (book_minimal_logical_type l)"
    by (rule book_lambda_I_closed_terms_language[OF book_lambda_I_conversion_logical_closed_terms])
  have closed: "named_fv (NLogical l) = {}" by simp
  show ?thesis unfolding book_lambda_I_conversion_logical_value_def
    by (rule book_lambda_I_conversion_denote_closed[OF language closed])
qed

end
