theory Bacon_Book_H_Modal_Certificates
  imports Bacon_Book_Box_Truth
    Bacon_Book_Environment_Development.Bacon_Book_Canonical_Completeness
begin

section \<open>H certificates obtained from the already verified H completeness theorem\<close>

theorem book_H_imp_iff_top:
  assumes rich: "sg_rich G" and language: "book_theory_formula \<Sigma> G P"
  shows "book_H \<Sigma> G (book_imp P (book_iff G P (book_top G)))"
proof -
  have top: "book_theory_formula \<Sigma> G (book_top G)" by (rule book_top_language[OF rich])
  have iff_type: "book_theory_formula \<Sigma> G (book_iff G P (book_top G))"
    by (rule book_iff_language[OF rich language top])
  have result_type: "book_theory_formula \<Sigma> G (book_imp P (book_iff G P (book_top G)))"
    by (rule book_imp_language[OF language iff_type])
  show ?thesis unfolding book_H_canonical_completeness[OF rich result_type]
  proof (unfold book_canonical_consequence_def, intro allI impI)
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and "\<forall>B\<in>{}. book_formula_valid D G J V B"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "book_formula_valid D G J V (book_imp P (book_iff G P (book_top G)))"
    proof (rule book_formula_validI)
      fix g
      assume typed: "book_env_typed D G g"
      show "V (J g (book_imp P (book_iff G P (book_top G))))"
        by (simp only: M.book_imp_truth[OF typed language iff_type]
          M.book_iff_truth[OF rich typed language top] M.book_top_true[OF rich typed]; simp)
    qed
  qed
qed

theorem book_H_box_fold_unfold:
  assumes rich: "sg_rich G" and language: "book_theory_formula \<Sigma> G P"
  shows "book_H \<Sigma> G (book_imp (book_leibniz G Prop P (book_top G)) (book_box G P))"
    and "book_H \<Sigma> G (book_imp (book_box G P) (book_leibniz G Prop P (book_top G)))"
proof -
  let ?E = "book_leibniz G Prop P (book_top G)"
  let ?B = "book_box G P"
  have el: "book_theory_formula \<Sigma> G ?E" by (rule book_leibniz_language[OF rich language book_top_language[OF rich]])
  have bl: "book_theory_formula \<Sigma> G ?B" by (rule book_box_language[OF rich language])
  have prove: "book_H \<Sigma> G (book_imp A B)"
    if al: "book_theory_formula \<Sigma> G A" and cl: "book_theory_formula \<Sigma> G B"
      and shape: "(A = ?E \<and> B = ?B) \<or> (A = ?B \<and> B = ?E)" for A B
  proof -
    have pl: "book_theory_formula \<Sigma> G (book_imp A B)" by (rule book_imp_language[OF al cl])
    show ?thesis unfolding book_H_canonical_completeness[OF rich pl]
    proof (unfold book_canonical_consequence_def, intro allI impI)
      fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k
      assume model: "book_full_minimal_model D app \<Sigma> G J V k" and "\<forall>C\<in>{}. book_formula_valid D G J V C"
      interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
      show "book_formula_valid D G J V (book_imp A B)"
      proof (rule book_formula_validI)
        fix g
        assume typed: "book_env_typed D G g"
        have same: "V (J g A) = V (J g B)"
          using M.book_box_unfolding_truth[OF rich typed language] shape by blast
        show "V (J g (book_imp A B))" by (simp only: M.book_imp_truth[OF typed al cl] same; simp)
      qed
    qed
  qed
  show "book_H \<Sigma> G (book_imp ?E ?B)" by (rule prove[OF el bl]; simp)
  show "book_H \<Sigma> G (book_imp ?B ?E)" by (rule prove[OF bl el]; simp)
qed

text \<open>
  These proofs use completeness of H for the already constructed full
  minimal general models. No C completeness or C semantic soundness is
  assumed. They recover actual H proof judgments for three elementary
  formulas; later C arguments use those judgments as H leaves.
  Model truth only establishes the H certificates, not modal-model existence.
\<close>

end
