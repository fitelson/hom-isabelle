theory Bacon_Book_Classicism_Modal_T
  imports Bacon_Book_H_Modal_Certificates
begin

section \<open>T already holds in the book's H\<close>

theorem book_H_modal_T:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P"
  shows "book_H \<Sigma> G (book_imp (book_box G P) P)"
proof -
  have bl: "book_theory_formula \<Sigma> G (book_box G P)" by (rule book_box_language[OF rich pl])
  have result_type: "book_theory_formula \<Sigma> G (book_imp (book_box G P) P)" by (rule book_imp_language[OF bl pl])
  show ?thesis unfolding book_H_canonical_completeness[OF rich result_type]
  proof (unfold book_canonical_consequence_def, intro allI impI)
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and "\<forall>B\<in>{}. book_formula_valid D G J V B"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "book_formula_valid D G J V (book_imp (book_box G P) P)"
    proof (rule book_formula_validI)
      fix g
      assume typed: "book_env_typed D G g"
      have implication: "V (J g (book_box G P)) \<longrightarrow> V (J g P)"
      proof
        assume boxed: "V (J g (book_box G P))"
        have equivalent: "book_leibniz_equiv D app V Prop (J g P) (J g (book_top G))"
          using boxed by (simp only: M.book_box_truth[OF rich typed pl])
        have same: "V (J g P) = V (J g (book_top G))" by (rule M.book_minimal_leibniz_valuation[OF equivalent])
        show "V (J g P)" by (simp only: same; rule M.book_top_true[OF rich typed])
      qed
      show "V (J g (book_imp (book_box G P) P))"
        by (simp only: M.book_imp_truth[OF typed bl pl]; rule implication)
    qed
  qed
qed

corollary book_C_modal_T:
  "sg_rich G \<Longrightarrow> book_theory_formula \<Sigma> G P \<Longrightarrow>
    book_C_proves \<Sigma> G (book_imp (book_box G P) P)"
  by (rule book_C_proves.H, rule book_H_modal_T; assumption)

end
