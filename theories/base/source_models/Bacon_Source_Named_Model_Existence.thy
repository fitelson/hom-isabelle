theory Bacon_Source_Named_Model_Existence
  imports Bacon_Source_BBK_Model_Existence Bacon_Source_Named_Forward_Validity
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Consistency_Correspondence
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Sentence_Sets
begin

section \<open>Every consistent native named sentence set has a named BBK model\<close>

text \<open>
  A consistent sentence set in the independently defined named H calculus
  has a model of the independent named BBK clauses. Source: the
  sentence-set model-existence direction of Bacon–Dorr Theorem 3.2,
  pp.44–45, for the represented full F language.

  The syntactic consistency iff transfers the premise to the encoded
  sentence set. Its verified finite-frame model supplies the named model
  by the proved tagged construction. Truth transport makes each original
  sentence valid at all typed adequate partial assignments.

  Σ and G are unchanged. Neither S nor the nonlogical-name carrier is
  required to be countable. The canonical carrier and additional type
  tag are displayed, rather than hidden in a model-existence assumption.
\<close>

theorem paper_named_BBK_model_existence:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_named_term set"
  assumes sentences: "paper_named_sentence_set \<Sigma> G S" and rich: "sg_rich G"
    and consistent: "paper_named_consistent \<Sigma> G S"
  shows "\<exists>D :: otype \<Rightarrow> (otype \<times> ('c phenkin_full_name) pHc_value) set.
    \<exists>J :: (otype \<times> ('c phenkin_full_name) pHc_value) named_assignment \<Rightarrow>
      'c paper_named_term \<Rightarrow> (otype \<times> ('c phenkin_full_name) pHc_value).
    \<exists>V :: (otype \<times> ('c phenkin_full_name) pHc_value) \<Rightarrow> bool.
      paper_named_bbk_model \<Sigma> G D J V \<and>
      (\<forall>A \<in> S. paper_named_bbk_model.named_valid \<Sigma> G D J V A)"
proof -
  have source_sentences: "paper_sentence_set \<Sigma> (named_to_source G [] ` S)"
    by (rule paper_named_sentence_set_encoding[OF sentences])
  have source_consistent: "paper_global_consistent \<Sigma> G (named_to_source G [] ` S)"
    by (rule iffD1[OF paper_named_consistency_iff[OF rich] consistent])
  obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set" and J V
    where source_model: "paper_db_bbk_model \<Sigma> D J V"
    and realizes: "\<forall>A \<in> named_to_source G [] ` S. \<forall>g. V (J g A)"
    using paper_db_BBK_model_existence[OF source_sentences rich source_consistent] by blast
  interpret Source: paper_db_bbk_model \<Sigma> D J V by (rule source_model)
  let ?D = "named_tag_domain D"
  let ?J = "Source.tagged_named_denote G"
  let ?V = "\<lambda>v. V (snd v)"
  have named_model: "paper_named_bbk_model \<Sigma> G ?D ?J ?V"
    by (rule Source.paper_db_tagged_named_model[OF rich])
  have named_valid: "paper_named_bbk_model.named_valid \<Sigma> G ?D ?J ?V A"
    if member: "A \<in> S" for A
  proof (rule Source.paper_db_named_valid_from_truth[OF rich
    paper_named_sentence_member_language[OF sentences member]])
    fix h
    assume typed: "paper_global_env_typed D G h"
    show "V (J h (named_to_source G [] A))" using realizes member by blast
  qed
  have all_sentences: "\<forall>A \<in> S. paper_named_bbk_model.named_valid \<Sigma> G ?D ?J ?V A"
    by (intro ballI, rule named_valid, assumption)
  show ?thesis by (rule exI[where x="?D"], rule exI[where x="?J"], rule exI[where x="?V"],
    rule conjI[OF named_model all_sentences])
qed

end
