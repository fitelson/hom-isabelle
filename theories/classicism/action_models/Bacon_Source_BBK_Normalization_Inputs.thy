theory Bacon_Source_BBK_Normalization_Inputs
  imports Bacon_Source_BBK_Model_Normalization
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Conversion_Contexts
begin

section \<open>Genuine inputs occurring in the logical model clauses\<close>

lemma paper_bbk_adequate_App_iff:
  "named_adequate g (NApp F A) \<longleftrightarrow> named_adequate g F \<and> named_adequate g A"
  by (simp add: named_adequate_def)

lemma paper_bbk_logical_language:
  "named_in_language paper_logical_type \<Sigma> G (NLogical l) (paper_logical_type l)"
  by (simp add: named_in_language_def named_logical_type_iff)

lemma paper_bbk_logical_adequate:
  "named_adequate g (NLogical l)"
  by (simp add: named_adequate_def)

lemma paper_bbk_normalize_unary_truth:
  assumes valid: "paper_bbk_data_valid \<Sigma> G M"
    and operator_type: "paper_logical_type l = Arr \<sigma> Prop"
    and language: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g A"
  shows "paper_bbk_valuation (paper_bbk_normalize \<Sigma> G M)
      (paper_bbk_denote (paper_bbk_normalize \<Sigma> G M) g (NApp (NLogical l) A)) =
    paper_bbk_valuation M (paper_bbk_denote M g (NApp (NLogical l) A))"
proof -
  have op: "named_in_language paper_logical_type \<Sigma> G (NLogical l) (Arr \<sigma> Prop)"
    using paper_bbk_logical_language[where \<Sigma>=\<Sigma> and G=G and l=l] by (simp only: operator_type)
  have whole: "named_in_language paper_logical_type \<Sigma> G (NApp (NLogical l) A) Prop"
    by (rule named_language_App[OF op language])
  have whole_adequate: "named_adequate g (NApp (NLogical l) A)"
    by (simp only: paper_bbk_adequate_App_iff; rule conjI[OF paper_bbk_logical_adequate adequate])
  show ?thesis by (rule paper_bbk_normalize_truth[OF valid whole typed whole_adequate])
qed

lemma paper_bbk_normalize_binary_truth:
  assumes valid: "paper_bbk_data_valid \<Sigma> G M"
    and operator_type: "paper_logical_type l = Arr \<sigma> (Arr \<tau> Prop)"
    and first: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and second: "named_in_language paper_logical_type \<Sigma> G B \<tau>"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate_A: "named_adequate g A" and adequate_B: "named_adequate g B"
  shows "paper_bbk_valuation (paper_bbk_normalize \<Sigma> G M)
      (paper_bbk_denote (paper_bbk_normalize \<Sigma> G M) g (NApp (NApp (NLogical l) A) B)) =
    paper_bbk_valuation M (paper_bbk_denote M g (NApp (NApp (NLogical l) A) B))"
proof -
  have op: "named_in_language paper_logical_type \<Sigma> G (NLogical l) (Arr \<sigma> (Arr \<tau> Prop))"
    using paper_bbk_logical_language[where \<Sigma>=\<Sigma> and G=G and l=l] by (simp only: operator_type)
  have whole: "named_in_language paper_logical_type \<Sigma> G (NApp (NApp (NLogical l) A) B) Prop"
    by (rule named_language_App[OF named_language_App[OF op first] second])
  have whole_adequate: "named_adequate g (NApp (NApp (NLogical l) A) B)"
    by (simp only: paper_bbk_adequate_App_iff;
      rule conjI[OF conjI[OF paper_bbk_logical_adequate adequate_A] adequate_B])
  show ?thesis by (rule paper_bbk_normalize_truth[OF valid whole typed whole_adequate])
qed

lemma paper_bbk_normalize_quantifier_instance:
  assumes valid: "paper_bbk_data_valid \<Sigma> G M"
    and predicate: "named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g F"
    and variable_type: "G n = \<sigma>" and member: "a \<in> paper_bbk_domain M \<sigma>"
  shows "paper_bbk_valuation (paper_bbk_normalize \<Sigma> G M)
      (paper_bbk_denote (paper_bbk_normalize \<Sigma> G M) (g(n := Some a)) (NApp F (NVar n))) =
    paper_bbk_valuation M (paper_bbk_denote M (g(n := Some a)) (NApp F (NVar n)))"
proof -
  have variable: "named_in_language paper_logical_type \<Sigma> G (NVar n) \<sigma>"
    by (simp add: named_in_language_def named_var_type_iff variable_type)
  have language: "named_in_language paper_logical_type \<Sigma> G (NApp F (NVar n)) Prop"
    by (rule named_language_App[OF predicate variable])
  have typed_member: "a \<in> paper_bbk_domain M (G n)" using member by (simp only: variable_type)
  have updated: "named_env_typed (paper_bbk_domain M) G (g(n := Some a))"
    by (rule named_assignment_update_typed[OF typed typed_member])
  have updated_adequate: "named_adequate (g(n := Some a)) (NApp F (NVar n))"
    by (rule named_quantifier_application_adequate[OF adequate])
  show ?thesis by (rule paper_bbk_normalize_truth[OF valid language updated updated_adequate])
qed

end
