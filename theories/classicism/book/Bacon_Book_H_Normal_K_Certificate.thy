theory Bacon_Book_H_Normal_K_Certificate
  imports Bacon_Book_Normal_K_Truth Bacon_Book_H_Modal_Certificates
begin

section \<open>H proves the conditional K calculation\<close>

definition book_K_formula :: "sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term" where
  "book_K_formula G P Q = book_imp (book_box G (book_imp P Q)) (book_imp (book_box G P) (book_box G Q))"

lemma book_K_language:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P" and ql: "book_theory_formula \<Sigma> G Q"
  shows "book_theory_formula \<Sigma> G (book_K_formula G P Q)"
  unfolding book_K_formula_def
  by (rule book_imp_language[OF book_box_language[OF rich book_imp_language[OF pl ql]]
    book_imp_language[OF book_box_language[OF rich pl] book_box_language[OF rich ql]]])

theorem book_H_normal_K_conditional:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P" and ql: "book_theory_formula \<Sigma> G Q"
  shows "book_H \<Sigma> G (book_imp (book_leibniz G Prop (book_imp (book_top G) Q) Q) (book_K_formula G P Q))"
proof -
  let ?E = "book_leibniz G Prop (book_imp (book_top G) Q) Q"
  have el: "book_theory_formula \<Sigma> G ?E"
    by (rule book_leibniz_language[OF rich book_imp_language[OF book_top_language[OF rich] ql] ql])
  have kl: "book_theory_formula \<Sigma> G (book_K_formula G P Q)" by (rule book_K_language[OF rich pl ql])
  have whole: "book_theory_formula \<Sigma> G (book_imp ?E (book_K_formula G P Q))" by (rule book_imp_language[OF el kl])
  have il: "book_theory_formula \<Sigma> G (book_box G (book_imp P Q))"
    by (rule book_box_language[OF rich book_imp_language[OF pl ql]])
  have bpl: "book_theory_formula \<Sigma> G (book_box G P)" by (rule book_box_language[OF rich pl])
  have bql: "book_theory_formula \<Sigma> G (book_box G Q)" by (rule book_box_language[OF rich ql])
  have tail: "book_theory_formula \<Sigma> G (book_imp (book_box G P) (book_box G Q))" by (rule book_imp_language[OF bpl bql])
  show ?thesis unfolding book_H_canonical_completeness[OF rich whole]
  proof (unfold book_canonical_consequence_def, intro allI impI)
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and "\<forall>B\<in>{}. book_formula_valid D G J V B"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "book_formula_valid D G J V (book_imp ?E (book_K_formula G P Q))"
    proof (rule book_formula_validI)
      fix g
      assume typed: "book_env_typed D G g"
      have calculation: "V (J g ?E) \<longrightarrow> V (J g (book_box G (book_imp P Q))) \<longrightarrow>
        V (J g (book_box G P)) \<longrightarrow> V (J g (book_box G Q))"
        by (intro impI; rule M.book_normal_K_truth_from_identity[OF rich typed pl ql]; assumption)
      show "V (J g (book_imp ?E (book_K_formula G P Q)))"
        by (simp only: M.book_imp_truth[OF typed el kl];
          simp only: book_K_formula_def M.book_imp_truth[OF typed il tail]
            M.book_imp_truth[OF typed bpl bql]; rule calculation)
    qed
  qed
qed

end
