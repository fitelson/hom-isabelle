theory Bacon_Source_Relational_H_Theory_Closed_Extension_Model
  imports Bacon_Source_Relational_H_Theory_Model_Existence
begin

section \<open>Adding closed sentences to an H-theory\<close>

text \<open>
  If T is an H-theory, S consists of closed sentences, and T∪S is
  locally H-consistent, there is a model of all of T∪S. Apply the
  sentence-set model-existence theorem to the closed fragment of T
  together with S, then recover every open member of T by universal
  instantiation. We do not require T∪S itself to be an H-theory.

  Source role: n.73's addition of a positive closed diagram and a
  closed negative discriminator to an H-theory. This avoids applying
  an open-theory existence theorem to a mere premise set.
\<close>

theorem paper_R_H_theory_closed_extension_model:
  fixes \<Sigma> :: "'c ssignature" and T S :: "'c paper_named_term set"
  assumes rich: "paper_R_rich G"
    and theory_h: "paper_R_H_theory \<Sigma> G T"
    and closed: "paper_R_closed_theory \<Sigma> G S"
    and consistent: "paper_R_named_consistent \<Sigma> G (T \<union> S)"
  shows "\<exists>D :: otype \<Rightarrow> (('c paper_R_henkin_name) paper_named_term set) set.
    \<exists>J :: (('c paper_R_henkin_name) paper_named_term set) named_assignment \<Rightarrow>
      'c paper_named_term \<Rightarrow> ('c paper_R_henkin_name) paper_named_term set.
    \<exists>V :: (('c paper_R_henkin_name) paper_named_term set) \<Rightarrow> bool.
      paper_R_bbk_model \<Sigma> G D J V \<and>
      (\<forall>A\<in>T \<union> S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A)"
proof -
  let ?F = "paper_R_sentence_fragment \<Sigma> G T"
  let ?U = "?F \<union> S"
  have sentences: "paper_R_closed_theory \<Sigma> G ?U"
    using paper_R_sentence_fragment_closed[where \<Sigma>=\<Sigma> and G=G and T=T] closed
    unfolding paper_R_closed_theory_def by blast
  have subset: "?U \<subseteq> T \<union> S"
    using paper_R_sentence_fragment_subset[where \<Sigma>=\<Sigma> and G=G and T=T] by blast
  have fragment_consistent: "paper_R_named_consistent \<Sigma> G ?U"
    by (rule paper_R_named_consistent_mono[OF consistent subset])
  obtain D :: "otype \<Rightarrow> (('c paper_R_henkin_name) paper_named_term set) set"
    and J and V where model: "paper_R_bbk_model \<Sigma> G D J V"
    and valid: "\<forall>A\<in>?U. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A"
    using paper_R_BBK_model_existence[OF rich sentences fragment_consistent] by blast
  interpret Model: paper_R_bbk_model \<Sigma> G D J V by (rule model)
  have fragment_valid: "Model.paper_R_valid A" if "A \<in> ?F" for A
    using valid that by blast
  have theory_valid: "Model.paper_R_valid A" if "A \<in> T" for A
    by (rule Model.paper_R_H_theory_valid_from_sentence_fragment[OF theory_h fragment_valid that])
  have all_valid: "\<forall>A\<in>T \<union> S. Model.paper_R_valid A"
    using theory_valid valid by blast
  show ?thesis by (rule exI[where x=D], rule exI[where x=J],
    rule exI[where x=V], rule conjI[OF model all_valid])
qed

end
