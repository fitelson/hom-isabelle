theory Bacon_Source_Relational_H_Theory_Bounded_Model
  imports Bacon_Source_Relational_Universal_Closure_Validity
    Bacon_Source_Relational_Bounded_Model_Existence
begin

section \<open>Consistent H-theories on a prescribed infinite carrier\<close>

text \<open>
  The same closed-fragment argument retains the exact cardinal
  bound of the native sentence-set construction. Given infinite U
  with |⋃σΣσ|≤|U|, the resulting model has ⋃σDσ⊆U and validates
  every member of the supplied consistent H-theory, including
  its open formulas under every typed adequate partial assignment.

  Source role: n.73, p.51, and the fixed-carrier construction on p.52.
  The bound concerns declared names, not their ambient HOL type.
  Neither the whole ambient canonical carrier nor all sets of open
  premises are asserted to embed or have a model.
\<close>

theorem paper_R_H_theory_bounded_model_existence:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature" and T :: "'c paper_named_term set"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G"
    and theory_h: "paper_R_H_theory \<Sigma> G T"
    and consistent: "paper_R_named_consistent \<Sigma> G T"
  shows "\<exists>D :: otype \<Rightarrow> 'u set.
    \<exists>J :: 'u named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'u.
    \<exists>V :: 'u \<Rightarrow> bool. paper_R_bbk_model \<Sigma> G D J V \<and>
      (\<Union>\<sigma>. D \<sigma>) \<subseteq> U \<and>
      (\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A)"
proof -
  let ?S = "paper_R_sentence_fragment \<Sigma> G T"
  have sentences: "paper_R_closed_theory \<Sigma> G ?S"
    by (rule paper_R_sentence_fragment_closed)
  have fragment_consistent: "paper_R_named_consistent \<Sigma> G ?S"
    by (rule paper_R_sentence_fragment_consistent[OF consistent])
  obtain D :: "otype \<Rightarrow> 'u set" and J and V
    where model: "paper_R_bbk_model \<Sigma> G D J V"
    and bound: "(\<Union>\<sigma>. D \<sigma>) \<subseteq> U"
    and fragment_valid: "\<forall>A\<in>?S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A"
    using paper_R_BBK_bounded_model_existence[
      OF infinite names rich sentences fragment_consistent] by blast
  interpret Model: paper_R_bbk_model \<Sigma> G D J V by (rule model)
  have valid: "Model.paper_R_valid A" if member: "A \<in> T" for A
    by (rule Model.paper_R_H_theory_valid_from_sentence_fragment[OF theory_h _ member],
      rule bspec[OF fragment_valid]; assumption)
  have all_valid: "\<forall>A\<in>T. Model.paper_R_valid A"
    by (intro ballI; rule valid; assumption)
  show ?thesis by (rule exI[where x=D], rule exI[where x=J],
    rule exI[where x=V], rule conjI[OF model conjI[OF bound all_valid]])
qed

end
