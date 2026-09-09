theory Bacon_Source_Named_Countable_Model_Existence
  imports Bacon_Source_Named_Model_Existence Bacon_Source_Named_Recoding_Validity
    Bacon_Source_Named_Nat_Coding
begin

section \<open>Countable declared signatures permit named domains contained in ℕ\<close>

text \<open>
  If Σ has countably many declared names and S is a consistent named
  sentence set, S has an independent named BBK model with Dσ ⊆ ℕ
  at every type. Source: the moreover clause of Bacon–Dorr Theorem 3.2,
  pp.44–45. The ambient constant-name carrier need not be countable.

  First obtain the existing source model on nat. Its proved named copy
  has carrier otype × nat, which the explicit injective code sends into
  nat. Generic model recoding preserves all clauses and validity. We do
  not attempt to code the arbitrary canonical ambient carrier, which need
  not be countable even when the declared signature is countable.
\<close>

theorem paper_named_BBK_countable_signature_model_existence:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_named_term set"
  assumes countable_signature: "countable (\<Union>\<sigma>. \<Sigma> \<sigma>)"
    and sentences: "paper_named_sentence_set \<Sigma> G S" and rich: "sg_rich G"
    and consistent: "paper_named_consistent \<Sigma> G S"
  shows "\<exists>D :: otype \<Rightarrow> nat set.
    \<exists>J :: nat named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool.
      paper_named_bbk_model \<Sigma> G D J V \<and>
      (\<forall>A \<in> S. paper_named_bbk_model.named_valid \<Sigma> G D J V A)"
proof -
  have source_sentences: "paper_sentence_set \<Sigma> (named_to_source G [] ` S)"
    by (rule paper_named_sentence_set_encoding[OF sentences])
  have source_consistent: "paper_global_consistent \<Sigma> G (named_to_source G [] ` S)"
    by (rule iffD1[OF paper_named_consistency_iff[OF rich] consistent])
  obtain D :: "otype \<Rightarrow> nat set" and J V
    where source_model: "paper_db_bbk_model \<Sigma> D J V"
    and realizes: "\<forall>A \<in> named_to_source G [] ` S. \<forall>g. V (J g A)"
    using paper_db_BBK_countable_signature_model_existence[OF countable_signature source_sentences rich source_consistent]
    by (elim exE conjE)
  interpret Source: paper_db_bbk_model \<Sigma> D J V by (rule source_model)
  interpret Tagged: paper_named_bbk_model \<Sigma> G "named_tag_domain D"
    "Source.tagged_named_denote G" "\<lambda>v. V (snd v)"
    by (rule Source.paper_db_tagged_named_model[OF rich])
  let ?D = "named_image_domain named_nat_code (named_tag_domain D)"
  let ?J = "Tagged.named_recode_denote named_nat_code"
  let ?V = "Tagged.named_recode_valuation named_nat_code"
  have coded_model: "paper_named_bbk_model \<Sigma> G ?D ?J ?V"
    by (rule Tagged.named_recode_model[OF named_nat_code_inj])
  have tagged_valid: "Tagged.named_valid A" if member: "A \<in> S" for A
  proof (rule Source.paper_db_named_valid_from_truth[OF rich
    paper_named_sentence_member_language[OF sentences member]])
    fix h
    assume typed: "paper_global_env_typed D G h"
    show "V (J h (named_to_source G [] A))" using realizes member by blast
  qed
  have coded_valid: "paper_named_bbk_model.named_valid \<Sigma> G ?D ?J ?V A"
    if member: "A \<in> S" for A
    by (rule iffD2[OF Tagged.named_recode_valid_iff[OF named_nat_code_inj] tagged_valid[OF member]])
  have all_sentences: "\<forall>A \<in> S. paper_named_bbk_model.named_valid \<Sigma> G ?D ?J ?V A"
    by (intro ballI, rule coded_valid, assumption)
  show ?thesis by (rule exI[where x="?D"], rule exI[where x="?J"], rule exI[where x="?V"],
    rule conjI[OF coded_model all_sentences])
qed

end
