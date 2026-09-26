theory Bacon_Book_Lambda_I_Model_Regression
  imports Bacon_Book_Lambda_I_Development.Bacon_Book_Lambda_I_Audit
    Bacon_Auxiliary_Bridge_Development.Bacon_Book_Model_Inhabitation
begin

ML_file "../../core_audit/Bacon_Core_Audit_Check.ML"

section \<open>An actual λI model with a typed assignment satisfying ⊥ → ⊥\<close>

text \<open>
  Regression outside the core λI session. The auxiliary bridge establishes
  an actual full minimal model at every signature under a rich stock (from
  the finite calibration of H and its canonical construction), and every
  full minimal model restricts to a λI model. The displayed fields D, App,
  J, v and κ, together with a typed total assignment, therefore satisfy
  ⊥ → ⊥, which is globally true; consequently {⊥ → ⊥} is λI-consistent.
  This is a model witness, not a use of any full-H proof-theoretic result
  inside the λI completeness pipeline, which lives in the core session.
\<close>

theorem book_lambda_I_bottom_implication_model_exists:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
  shows "\<exists>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set. \<exists>ap J V K g.
    book_lambda_I_model D ap \<Sigma> G J V K \<and> book_env_typed D G g \<and>
    V (J g (book_imp (book_bottom G) (book_bottom G))) \<and>
    book_formula_valid D G J V (book_imp (book_bottom G) (book_bottom G))"
proof -
  obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set" and ap J V K
    where full: "book_full_minimal_model D ap \<Sigma> G J V K"
    using book_full_minimal_model_exists[where \<Sigma>=\<Sigma>, OF rich] by blast
  have model: "book_lambda_I_model D ap \<Sigma> G J V K"
    by (rule book_full_minimal_model_lambda_I[OF full])
  interpret M: book_lambda_I_model D ap \<Sigma> G J V K by (rule model)
  obtain g where typed: "book_env_typed D G g"
    and truth: "V (J g (book_imp (book_bottom G) (book_bottom G)))"
    using M.book_lambda_I_bottom_implication_satisfied[OF rich] by blast
  have bottom: "book_lambda_I_formula \<Sigma> G (book_bottom G)"
    by (rule book_lambda_I_bottom_language[OF rich])
  have valid: "book_formula_valid D G J V (book_imp (book_bottom G) (book_bottom G))"
  proof (rule book_formula_validI)
    fix h
    assume ht: "book_env_typed D G h"
    show "V (J h (book_imp (book_bottom G) (book_bottom G)))"
      by (simp only: M.imp_truth[OF ht bottom bottom]; blast)
  qed
  show ?thesis
    by (rule exI[where x=D], rule exI[where x=ap], rule exI[where x=J], rule exI[where x=V],
      rule exI[where x=K], rule exI[where x=g], rule conjI[OF model conjI[OF typed conjI[OF truth valid]]])
qed

corollary book_lambda_I_bottom_implication_consistent:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
  shows "book_lambda_I_consistent \<Sigma> G {book_imp (book_bottom G) (book_bottom G)}"
proof -
  obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set" and ap J V K g
    where model: "book_lambda_I_model D ap \<Sigma> G J V K"
    and valid: "book_formula_valid D G J V (book_imp (book_bottom G) (book_bottom G))"
    using book_lambda_I_bottom_implication_model_exists[where \<Sigma>=\<Sigma>, OF rich] by blast
  interpret M: book_lambda_I_model D ap \<Sigma> G J V K by (rule model)
  show ?thesis by (rule M.book_lambda_I_satisfiable_consistent[OF rich]) (simp add: valid)
qed

ML \<open>
local
  val targets =
   [("an actual λI model and typed assignment satisfy ⊥ → ⊥, globally", "book_lambda_I_bottom_implication_model_exists"),
    ("{⊥ → ⊥} is λI-consistent", "book_lambda_I_bottom_implication_consistent")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-lambda-I-regression"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: pure HOL\n"
    ^ "SCOPE: satisfiability regression for the λI model class on an actual model obtained from the auxiliary-bridge full minimal model existence theorem (finite calibration of H plus its canonical construction) and the restriction of full minimal models to λI models; this is a witness outside the core λI session and is not used by the λI completeness pipeline\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-lambda-I-regression-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

end
