theory Bacon_Book_Classicism_Modal_Four
  imports Bacon_Book_Modal_Four_Truth Bacon_Book_Classicism_Necessitation
begin

section \<open>Axiom 4 in the book's own C calculus\<close>

theorem book_H_box_top:
  assumes rich: "sg_rich G"
  shows "book_H \<Sigma> G (book_box G (book_top G))"
proof -
  have language: "book_theory_formula \<Sigma> G (book_box G (book_top G))"
    by (rule book_box_language[OF rich book_top_language[OF rich]])
  show ?thesis unfolding book_H_canonical_completeness[OF rich language]
  proof (unfold book_canonical_consequence_def, intro allI impI)
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and "\<forall>B\<in>{}. book_formula_valid D G J V B"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "book_formula_valid D G J V (book_box G (book_top G))"
      by (rule book_formula_validI; rule M.book_box_top_true[OF rich]; assumption)
  qed
qed

theorem book_H_modal_four_conditional:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P"
  shows "book_H \<Sigma> G (book_imp (book_box G (book_box G (book_top G)))
    (book_imp (book_box G P) (book_box G (book_box G P))))"
proof -
  let ?T = "book_box G (book_box G (book_top G))"
  let ?B = "book_box G P"
  let ?BB = "book_box G ?B"
  have tl: "book_theory_formula \<Sigma> G ?T" by (rule book_box_language[OF rich book_box_language[OF rich book_top_language[OF rich]]])
  have bl: "book_theory_formula \<Sigma> G ?B" by (rule book_box_language[OF rich pl])
  have bbl: "book_theory_formula \<Sigma> G ?BB" by (rule book_box_language[OF rich bl])
  have tail: "book_theory_formula \<Sigma> G (book_imp ?B ?BB)" by (rule book_imp_language[OF bl bbl])
  have whole: "book_theory_formula \<Sigma> G (book_imp ?T (book_imp ?B ?BB))" by (rule book_imp_language[OF tl tail])
  show ?thesis unfolding book_H_canonical_completeness[OF rich whole]
  proof (unfold book_canonical_consequence_def, intro allI impI)
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and "\<forall>A\<in>{}. book_formula_valid D G J V A"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "book_formula_valid D G J V (book_imp ?T (book_imp ?B ?BB))"
    proof (rule book_formula_validI)
      fix g
      assume typed: "book_env_typed D G g"
      have calculation: "V (J g ?T) \<longrightarrow> V (J g ?B) \<longrightarrow> V (J g ?BB)"
        by (intro impI; rule M.book_modal_four_truth[OF rich typed pl]; assumption)
      show "V (J g (book_imp ?T (book_imp ?B ?BB)))"
        by (simp only: M.book_imp_truth[OF typed tl tail] M.book_imp_truth[OF typed bl bbl]; rule calculation)
    qed
  qed
qed

theorem book_C_modal_4:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P"
  shows "book_C_proves \<Sigma> G (book_imp (book_box G P) (book_box G (book_box G P)))"
proof -
  have box_top: "book_C_proves \<Sigma> G (book_box G (book_top G))"
    by (rule book_C_proves.H[OF book_H_box_top[OF rich]])
  have necessary: "book_C_proves \<Sigma> G (book_box G (book_box G (book_top G)))"
    by (rule book_C_necessitation[OF rich box_top])
  have conditional: "book_C_proves \<Sigma> G (book_imp (book_box G (book_box G (book_top G)))
      (book_imp (book_box G P) (book_box G (book_box G P))))"
    by (rule book_C_proves.H[OF book_H_modal_four_conditional[OF rich pl]])
  have bl: "book_theory_formula \<Sigma> G (book_box G P)" by (rule book_box_language[OF rich pl])
  show ?thesis by (rule book_C_proves.MP[OF necessary conditional book_imp_language[OF bl book_box_language[OF rich bl]]])
qed

text \<open>
  Only the original theorem □⊤ is necessitated. The conditional
  calculation is an H certificate obtained from independently verified
  H completeness. The result is □P→□□P, with P allowed open.
  No C completeness, new modal axiom, or R-language theorem is assumed.
  This supplies the transitivity input for canonical accessibility.
\<close>

end
