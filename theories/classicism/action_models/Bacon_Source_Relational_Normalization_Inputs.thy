theory Bacon_Source_Relational_Normalization_Inputs
  imports Bacon_Source_Relational_Model_Normalization
begin

section \<open>Genuine inputs occurring in the logical model clauses\<close>

text \<open>
  The operations ¬, ∧, ∨, ∀σ, ∃σ and =σ have R types
  when their argument indices do. Their applications and the updated
  instances Fv are therefore genuine R inputs to J. Source: §1.1,
  p.5, and Definition 3.1(iii), p.44. Each guard is derived from
  R grammar; an F typing with an R result alone would not suffice.
\<close>

lemma paper_R_normalization_App:
  assumes head: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "paper_R_in_language \<Sigma> G A \<sigma>"
  shows "paper_R_in_language \<Sigma> G (NApp F A) \<tau>"
  using head argument unfolding paper_R_in_language_def
  by (auto intro: paper_R_has_type.App)

lemma paper_R_normalization_Var:
  assumes rt: "paper_R_type (G n)"
  shows "paper_R_in_language \<Sigma> G (NVar n) (G n)"
  unfolding paper_R_in_language_def
  by (rule conjI[OF paper_R_has_type.Var[where G=G and n=n, OF rt]]; simp)

lemma paper_R_bbk_adequate_App_iff:
  "named_adequate g (NApp F A) \<longleftrightarrow> named_adequate g F \<and> named_adequate g A"
  by (simp add: named_adequate_def)

lemma paper_R_bbk_logical_language:
  assumes rt: "paper_R_type (paper_logical_type l)"
  shows "paper_R_in_language \<Sigma> G (NLogical l) (paper_logical_type l)"
  unfolding paper_R_in_language_def
  by (rule conjI[OF paper_R_has_type.Logical[OF rt]]; simp)

lemma paper_R_bbk_logical_adequate:
  "named_adequate g (NLogical l)"
  by (simp add: named_adequate_def)

lemma paper_R_bbk_normalize_unary_truth:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M"
    and operator_type: "paper_logical_type l = Arr \<sigma> Prop"
    and language: "paper_R_in_language \<Sigma> G A \<sigma>"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g A"
  shows "paper_bbk_valuation (paper_R_bbk_normalize \<Sigma> G M)
      (paper_bbk_denote (paper_R_bbk_normalize \<Sigma> G M) g (NApp (NLogical l) A)) =
    paper_bbk_valuation M (paper_bbk_denote M g (NApp (NLogical l) A))"
proof -
  have argument_R: "paper_R_type \<sigma>" by (rule paper_R_language_result_type[OF language])
  have operator_R: "paper_R_type (paper_logical_type l)"
    by (simp add: operator_type argument_R)
  have op: "paper_R_in_language \<Sigma> G (NLogical l) (Arr \<sigma> Prop)"
    using paper_R_bbk_logical_language[where \<Sigma>=\<Sigma> and G=G and l=l, OF operator_R]
    by (simp only: operator_type)
  have whole: "paper_R_in_language \<Sigma> G (NApp (NLogical l) A) Prop"
    by (rule paper_R_normalization_App[OF op language])
  have whole_adequate: "named_adequate g (NApp (NLogical l) A)"
    by (simp only: paper_R_bbk_adequate_App_iff; rule conjI[OF paper_R_bbk_logical_adequate adequate])
  show ?thesis by (rule paper_R_bbk_normalize_truth[OF valid whole typed whole_adequate])
qed

lemma paper_R_bbk_normalize_binary_truth:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M"
    and operator_type: "paper_logical_type l = Arr \<sigma> (Arr \<tau> Prop)"
    and first: "paper_R_in_language \<Sigma> G A \<sigma>"
    and second: "paper_R_in_language \<Sigma> G B \<tau>"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate_A: "named_adequate g A" and adequate_B: "named_adequate g B"
  shows "paper_bbk_valuation (paper_R_bbk_normalize \<Sigma> G M)
      (paper_bbk_denote (paper_R_bbk_normalize \<Sigma> G M) g (NApp (NApp (NLogical l) A) B)) =
    paper_bbk_valuation M (paper_bbk_denote M g (NApp (NApp (NLogical l) A) B))"
proof -
  have first_R: "paper_R_type \<sigma>" by (rule paper_R_language_result_type[OF first])
  have second_R: "paper_R_type \<tau>" by (rule paper_R_language_result_type[OF second])
  have operator_R: "paper_R_type (paper_logical_type l)"
    by (simp add: operator_type first_R second_R)
  have op: "paper_R_in_language \<Sigma> G (NLogical l) (Arr \<sigma> (Arr \<tau> Prop))"
    using paper_R_bbk_logical_language[where \<Sigma>=\<Sigma> and G=G and l=l, OF operator_R]
    by (simp only: operator_type)
  have whole: "paper_R_in_language \<Sigma> G (NApp (NApp (NLogical l) A) B) Prop"
    by (rule paper_R_normalization_App[OF paper_R_normalization_App[OF op first] second])
  have whole_adequate: "named_adequate g (NApp (NApp (NLogical l) A) B)"
    by (simp only: paper_R_bbk_adequate_App_iff;
      rule conjI[OF conjI[OF paper_R_bbk_logical_adequate adequate_A] adequate_B])
  show ?thesis by (rule paper_R_bbk_normalize_truth[OF valid whole typed whole_adequate])
qed

lemma paper_R_bbk_normalize_quantifier_instance:
  assumes valid: "paper_R_bbk_data_valid \<Sigma> G M"
    and predicate: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g F"
    and variable_type: "G n = \<sigma>" and member: "a \<in> paper_bbk_domain M \<sigma>"
  shows "paper_bbk_valuation (paper_R_bbk_normalize \<Sigma> G M)
      (paper_bbk_denote (paper_R_bbk_normalize \<Sigma> G M) (g(n := Some a)) (NApp F (NVar n))) =
    paper_bbk_valuation M (paper_bbk_denote M (g(n := Some a)) (NApp F (NVar n)))"
proof -
  have argument_R: "paper_R_type \<sigma>"
    by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have variable_R: "paper_R_type (G n)" by (simp only: variable_type; rule argument_R)
  have variable: "paper_R_in_language \<Sigma> G (NVar n) \<sigma>"
    using paper_R_normalization_Var[where \<Sigma>=\<Sigma> and G=G and n=n, OF variable_R]
    by (simp only: variable_type)
  have language: "paper_R_in_language \<Sigma> G (NApp F (NVar n)) Prop"
    by (rule paper_R_normalization_App[OF predicate variable])
  have typed_member: "a \<in> paper_bbk_domain M (G n)" using member by (simp only: variable_type)
  have updated: "named_env_typed (paper_bbk_domain M) G (g(n := Some a))"
    by (rule named_assignment_update_typed[where D="paper_bbk_domain M" and G=G and n=n,
      OF typed typed_member])
  have updated_adequate: "named_adequate (g(n := Some a)) (NApp F (NVar n))"
    by (rule named_quantifier_application_adequate[OF adequate])
  show ?thesis by (rule paper_R_bbk_normalize_truth[OF valid language updated updated_adequate])
qed

end
