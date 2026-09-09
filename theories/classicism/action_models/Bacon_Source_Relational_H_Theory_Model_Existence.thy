theory Bacon_Source_Relational_H_Theory_Model_Existence
  imports Bacon_Source_Relational_Universal_Closure_Validity
    Bacon_Source_Relational_Model_Existence
begin

section \<open>An actual R-BBK model of a consistent H-theory\<close>

text \<open>
  A consistent H-theory T may contain open formulas. Its closed
  sentence fragment is consistent and therefore has a model by
  Theorem 3.2, pp.44–45. Every member of T has a finite universal
  closure in that fragment, so the same model validates all of T.

  The H-theory closure premise is essential to this argument:
  arbitrary locally consistent open premise sets are not covered.
  The semantic carrier is explicit, and no countability, supplied
  model, Propositional Equivalence or C premise is assumed.
  This is the H-theory model-existence step used in n.73, p.51.
\<close>

theorem paper_R_H_theory_model_existence:
  fixes \<Sigma> :: "'c ssignature" and T :: "'c paper_named_term set"
  assumes rich: "paper_R_rich G"
    and theory_h: "paper_R_H_theory \<Sigma> G T"
    and consistent: "paper_R_named_consistent \<Sigma> G T"
  shows "\<exists>D :: otype \<Rightarrow> (('c paper_R_henkin_name) paper_named_term set) set.
    \<exists>J :: (('c paper_R_henkin_name) paper_named_term set) named_assignment \<Rightarrow>
      'c paper_named_term \<Rightarrow> ('c paper_R_henkin_name) paper_named_term set.
    \<exists>V :: (('c paper_R_henkin_name) paper_named_term set) \<Rightarrow> bool.
      paper_R_bbk_model \<Sigma> G D J V \<and>
      (\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A)"
proof -
  let ?S = "paper_R_sentence_fragment \<Sigma> G T"
  have sentences: "paper_R_closed_theory \<Sigma> G ?S"
    by (rule paper_R_sentence_fragment_closed)
  have fragment_consistent: "paper_R_named_consistent \<Sigma> G ?S"
    by (rule paper_R_sentence_fragment_consistent[OF consistent])
  obtain D :: "otype \<Rightarrow> (('c paper_R_henkin_name) paper_named_term set) set"
    and J and V where model: "paper_R_bbk_model \<Sigma> G D J V"
    and fragment_valid: "\<forall>A\<in>?S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A"
    using paper_R_BBK_model_existence[OF rich sentences fragment_consistent] by blast
  interpret Model: paper_R_bbk_model \<Sigma> G D J V by (rule model)
  have valid: "Model.paper_R_valid A" if member: "A \<in> T" for A
    by (rule Model.paper_R_H_theory_valid_from_sentence_fragment[OF theory_h _ member],
      rule bspec[OF fragment_valid]; assumption)
  have all_valid: "\<forall>A\<in>T. Model.paper_R_valid A"
    by (intro ballI; rule valid; assumption)
  show ?thesis by (rule exI[where x=D], rule exI[where x=J],
    rule exI[where x=V], rule conjI[OF model all_valid])
qed

end
