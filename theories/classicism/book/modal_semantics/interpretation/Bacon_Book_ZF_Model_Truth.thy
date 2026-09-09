theory Bacon_Book_ZF_Model_Truth
  imports Bacon_Book_ZF_Model_Interpretation_Uniqueness
begin

section \<open>Truth at a world and truth under every typed assignment\<close>

definition book_ZF_truth_at where "book_ZF_truth_at J w g A = Elem w (J w g A)"
definition book_ZF_formula_valid where
  "book_ZF_formula_valid D G J root A = (\<forall>g. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> root)) G g \<longrightarrow> book_ZF_truth_at J root g A)"
definition book_ZF_satisfies where
  "book_ZF_satisfies D G J root S = (\<forall>A\<in>S. book_ZF_formula_valid D G J root A)"

context book_ZF_modal_interpretation
begin

theorem formula_valid_independent:
  assumes other: "book_ZF_modal_interpretation W R root D i signature I G K"
    and language: "book_in_language book_minimal_logical_type UNIV signature G A Prop"
  shows "book_ZF_formula_valid D G J root A = book_ZF_formula_valid D G K root A"
proof -
  have same: "J root g A = K root g A" if typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> root)) G g" for g
    by (rule interpretation_unique[OF other language root_world typed])
  show ?thesis unfolding book_ZF_formula_valid_def book_ZF_truth_at_def using same by auto
qed

theorem satisfaction_independent:
  assumes other: "book_ZF_modal_interpretation W R root D i signature I G K"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_in_language book_minimal_logical_type UNIV signature G A Prop"
  shows "book_ZF_satisfies D G J root S = book_ZF_satisfies D G K root S"
  unfolding book_ZF_satisfies_def
  by (rule ball_cong[OF refl]; rule formula_valid_independent[OF other language]; assumption)

end

text \<open>
  These are the truth clauses of Definitions 18.1–18.2, with typed
  assignments explicit. Mathematical claims retain formula-language
  guards. Whenever two interpretations of a model satisfy the
  independent clauses, they give the same truth and satisfaction
  predicates on that language. Generic existence is still separate;
  it is not smuggled into the definition of modelhood or validity.
\<close>

end
