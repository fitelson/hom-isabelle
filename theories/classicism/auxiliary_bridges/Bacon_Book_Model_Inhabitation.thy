theory Bacon_Book_Model_Inhabitation
  imports Bacon_Finite_Calibration_BBK_Inhabitation
    Bacon_Book_Environment_Development.Bacon_Book_BBK_Model
    Bacon_Book_Environment_Development.Bacon_Book_Open_Deduction_Boundary
    Bacon_Book_Environment_Development.Bacon_Book_Logic
begin

section \<open>Independent inhabitation of the full minimal book model class\<close>

text \<open>
  The existing finite H calibration proves consistency of the represented
  H calculus; its separately verified canonical construction supplies a
  BBK model. The new BBK-to-book bridge turns that actual model into a
  full minimal book model, preserving its domains and valuation.

  This downstream combination uses no book completeness theorem and
  does not assume that the book model class is inhabited. The old finite
  calibration is not relabeled a source model: the BBK and book model
  fields are supplied by their checked constructions. Keeping this leaf
  downstream leaves the independent book syntax and soundness proofs
  free of the calibration and older proof judgments.

  Scope: arbitrary nonlogical name carrier and signature, full F/full
  λ-language, minimal logical basis, rich stock, and actual witnessed
  logical values. The displayed semantic carrier is explicit; it is not
  quantified over as a HOL type. No Goodman application is used.
\<close>

theorem book_full_minimal_model_exists:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
  shows "\<exists>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
    \<exists>ap :: otype \<Rightarrow> otype \<Rightarrow> ('c phenkin_full_name) pHc_value \<Rightarrow>
      ('c phenkin_full_name) pHc_value \<Rightarrow> ('c phenkin_full_name) pHc_value.
    \<exists>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
      'c book_named_term \<Rightarrow> ('c phenkin_full_name) pHc_value.
    \<exists>V K. book_full_minimal_model D ap \<Sigma> G J V K"
proof -
  obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set"
    and J V where model: "pbbk_model \<Sigma> D J V"
    using pbbk_model_exists_from_finite_calibration[where \<Sigma>=\<Sigma>] by (elim exE)
  interpret M: pbbk_model \<Sigma> D J V by (rule model)
  have book_model: "book_full_minimal_model D M.pbbk_book_app \<Sigma> G
    (M.pbbk_book_denote G) V M.pbbk_book_logical_value"
    by (rule M.pbbk_to_book_full_minimal_model[OF rich])
  show ?thesis by (rule exI[where x=D], rule exI[where x=M.pbbk_book_app],
    rule exI[where x="M.pbbk_book_denote G"], rule exI[where x=V],
    rule exI[where x=M.pbbk_book_logical_value], rule book_model)
qed

corollary book_standard_full_minimal_model_exists:
  fixes \<Sigma> :: "'c ssignature"
  shows "\<exists>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
    \<exists>ap J V K. book_full_minimal_model D ap \<Sigma> sg_standard_stock J V K"
  by (rule book_full_minimal_model_exists[OF sg_standard_stock_rich])

theorem book_empty_theory_nonderives_bottom:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
  shows "\<not> book_theory_derivable \<Sigma> G {} (book_bottom G)"
proof -
  obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set"
    and ap J V K where model: "book_full_minimal_model D ap \<Sigma> G J V K"
    using book_full_minimal_model_exists[where \<Sigma>=\<Sigma>, OF rich] by (elim exE)
  interpret Book: book_full_minimal_model D ap \<Sigma> G J V K by (rule model)
  obtain g where typed: "book_env_typed D G g"
    using Book.book_minimal_assignment_exists by (elim exE)
  show ?thesis
  proof
    assume derivation: "book_theory_derivable \<Sigma> G {} (book_bottom G)"
    have valid: "book_formula_valid D G J V (book_bottom G)"
      by (rule Book.book_axiom_generated_soundness[OF rich derivation])
    have true_bottom: "V (J g (book_bottom G))" by (rule book_formula_validE[OF valid typed])
    show False by (rule notE[OF Book.book_bottom_false[OF rich typed] true_bottom])
  qed
qed

theorem book_open_deduction_failure:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
  shows "book_theory_derivable \<Sigma> G {NVar (book_prop_name G)} (book_bottom G) \<and>
    \<not> book_theory_derivable \<Sigma> G {} (book_imp (NVar (book_prop_name G)) (book_bottom G))"
proof -
  obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set"
    and ap J V K where model: "book_full_minimal_model D ap \<Sigma> G J V K"
    using book_full_minimal_model_exists[where \<Sigma>=\<Sigma>, OF rich] by (elim exE)
  interpret Book: book_full_minimal_model D ap \<Sigma> G J V K by (rule model)
  show ?thesis by (rule Book.book_unrestricted_open_deduction_counterexample[OF rich])
qed

corollary book_H_nonderives_bottom:
  assumes rich: "sg_rich G"
  shows "\<not> book_H \<Sigma> G (book_bottom G)"
  by (simp only: book_H_iff_theory[OF rich]; rule book_empty_theory_nonderives_bottom[OF rich])

end
