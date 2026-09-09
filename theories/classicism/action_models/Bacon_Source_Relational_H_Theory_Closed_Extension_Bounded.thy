theory Bacon_Source_Relational_H_Theory_Closed_Extension_Bounded
  imports Bacon_Source_Relational_H_Theory_Bounded_Model
begin

section \<open>Closed additions to an H-theory on a prescribed infinite carrier\<close>

text \<open>
  If T is an H-theory, S consists of closed sentences, and T∪S
  is locally H-consistent, construct a model validating T∪S with
  ⋃σDσ⊆U. The bound |⋃σΣσ|≤|U| and infinitude of U are
  the exact hypotheses of the bounded sentence-set construction.
  Apply it to the closed fragment of T together with S, then recover
  the open members of T by universal instantiation.

  Source role: n.73's closed diagram and discriminator, together
  with the uniform-carrier refinement on p.52. We do not assume
  that T∪S is itself an H-theory or supply the target model.
\<close>

theorem paper_R_H_theory_closed_extension_bounded_model:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature" and T S :: "'c paper_named_term set"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G"
    and theory_h: "paper_R_H_theory \<Sigma> G T"
    and closed: "paper_R_closed_theory \<Sigma> G S"
    and consistent: "paper_R_named_consistent \<Sigma> G (T \<union> S)"
  shows "\<exists>D :: otype \<Rightarrow> 'u set.
    \<exists>J :: 'u named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'u.
    \<exists>V :: 'u \<Rightarrow> bool. paper_R_bbk_model \<Sigma> G D J V \<and>
      (\<Union>\<sigma>. D \<sigma>) \<subseteq> U \<and>
      (\<forall>A\<in>T \<union> S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A)"
proof -
  let ?F = "paper_R_sentence_fragment \<Sigma> G T"
  let ?S = "?F \<union> S"
  have sentences: "paper_R_closed_theory \<Sigma> G ?S"
    using paper_R_sentence_fragment_closed[where \<Sigma>=\<Sigma> and G=G and T=T] closed
    unfolding paper_R_closed_theory_def by blast
  have subset: "?S \<subseteq> T \<union> S"
    using paper_R_sentence_fragment_subset[where \<Sigma>=\<Sigma> and G=G and T=T] by blast
  have fragment_consistent: "paper_R_named_consistent \<Sigma> G ?S"
    by (rule paper_R_named_consistent_mono[OF consistent subset])
  obtain D :: "otype \<Rightarrow> 'u set" and J and V
    where model: "paper_R_bbk_model \<Sigma> G D J V"
    and bound: "(\<Union>\<sigma>. D \<sigma>) \<subseteq> U"
    and valid: "\<forall>A\<in>?S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A"
    using paper_R_BBK_bounded_model_existence[
      OF infinite names rich sentences fragment_consistent] by blast
  interpret Model: paper_R_bbk_model \<Sigma> G D J V by (rule model)
  have fragment_valid: "Model.paper_R_valid A" if "A \<in> ?F" for A
    using valid that by blast
  have theory_valid: "Model.paper_R_valid A" if "A \<in> T" for A
    by (rule Model.paper_R_H_theory_valid_from_sentence_fragment[OF theory_h fragment_valid that])
  have all_valid: "\<forall>A\<in>T \<union> S. Model.paper_R_valid A"
    using theory_valid valid by blast
  show ?thesis by (rule exI[where x=D], rule exI[where x=J],
    rule exI[where x=V], rule conjI[OF model conjI[OF bound all_valid]])
qed

end
