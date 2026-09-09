theory Bacon_Source_BBK_Model_Existence
  imports Bacon_Source_Vocabulary_Development.Bacon_Source_Consistency_Correspondence
    Bacon_Source_Vocabulary_Development.Bacon_Source_BBK_Pullback_Model
    Bacon_Parametric_Canonical_Development.Bacon_Parametric_BBK_Model_Existence
    Bacon_Parametric_Countable_Development.Bacon_Parametric_Declared_Signature_Model_Existence
begin

section \<open>Models of consistent sentence sets in the first-class language\<close>

text \<open>
  A consistent sentence set S of the first-class paper language has a model
  in the separately declared finite-frame BBK interface. Translate S,
  use the proved consistency correspondence and target model-existence
  theorem, then pull the interpretation back to source terms.

  Source role: the model-existence step of Bacon–Dorr Theorem 3.2,
  pp.44–45. This construction preserves Σ, does not assume that Σ has
  closed inhabitants, and imposes no cardinality bound on S or names.

  Precise status: existence in paper_db_bbk_model, with independently
  specified first-class logical truth clauses and explicit de Bruijn
  coherence. Subsequent soundness leaves cover every weak finite-frame
  structure on an arbitrary carrier; the closed strong-completeness leaf
  quantifies over all such structures on an explicit canonical carrier,
  not just those constructed here. Equivalence with the paper's adequate
  named assignments and the book's different general-model theorem remain
  separate obligations.
\<close>

theorem paper_db_BBK_model_existence:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_term set"
  assumes sentences: "paper_sentence_set \<Sigma> S" and rich: "sg_rich G"
    and consistent: "paper_global_consistent \<Sigma> G S"
  shows "\<exists>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
    \<exists>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
      'c paper_term \<Rightarrow> ('c phenkin_full_name) pHc_value.
    \<exists>V :: ('c phenkin_full_name) pHc_value \<Rightarrow> bool.
      paper_db_bbk_model \<Sigma> D J V \<and> (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  have typed: "pH_typed_theory \<Sigma> [] (image paper_to_pterm S)"
    by (rule paper_sentence_set_target[OF sentences])
  have target_consistent: "pH_consistent \<Sigma> [] (image paper_to_pterm S)"
    by (rule paper_source_consistent_to_target[OF sentences rich consistent])
  obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set" and J V
    where model: "pbbk_model \<Sigma> D J V"
    and realizes: "\<forall>A \<in> image paper_to_pterm S. \<forall>g. V (J g A)"
    using pH_BBK_model_existence[OF typed target_consistent] by blast
  have source_model: "paper_db_bbk_model \<Sigma> D (\<lambda>g A. J g (paper_to_pterm A)) V"
    by (rule pbbk_to_paper_db_model[OF model])
  have source_realizes: "\<forall>A \<in> S. \<forall>g. V (J g (paper_to_pterm A))"
    using realizes by blast
  show ?thesis
    by (rule exI[where x=D], rule exI[where x="\<lambda>g A. J g (paper_to_pterm A)"],
      rule exI[where x=V], rule conjI[OF source_model source_realizes])
qed

section \<open>Countably many declared names suffice for natural-number domains\<close>

text \<open>
  When ⋃σ Σσ is countable, all Dσ may be subsets of ℕ. The ambient
  name carrier may still be uncountable. No additional restriction on S
  is imposed. This is the countable clause of Theorem 3.2 within the same
  finite-frame interface and with the same named-representation qualification.
\<close>

theorem paper_db_BBK_countable_signature_model_existence:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_term set"
  assumes countable_signature: "countable (\<Union>\<sigma>. \<Sigma> \<sigma>)"
    and sentences: "paper_sentence_set \<Sigma> S" and rich: "sg_rich G"
    and consistent: "paper_global_consistent \<Sigma> G S"
  shows "\<exists>D :: otype \<Rightarrow> nat set.
    \<exists>J :: (nat \<Rightarrow> nat) \<Rightarrow> 'c paper_term \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool.
      paper_db_bbk_model \<Sigma> D J V \<and> (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  have typed: "pH_typed_theory \<Sigma> [] (image paper_to_pterm S)"
    by (rule paper_sentence_set_target[OF sentences])
  have target_consistent: "pH_consistent \<Sigma> [] (image paper_to_pterm S)"
    by (rule paper_source_consistent_to_target[OF sentences rich consistent])
  obtain D :: "otype \<Rightarrow> nat set" and J V where model: "pbbk_model \<Sigma> D J V"
    and realizes: "\<forall>A \<in> image paper_to_pterm S. \<forall>g. V (J g A)"
    using pH_BBK_countable_signature_model_existence[OF countable_signature typed target_consistent] by blast
  have source_model: "paper_db_bbk_model \<Sigma> D (\<lambda>g A. J g (paper_to_pterm A)) V"
    by (rule pbbk_to_paper_db_model[OF model])
  have source_realizes: "\<forall>A \<in> S. \<forall>g. V (J g (paper_to_pterm A))"
    using realizes by blast
  show ?thesis
    by (rule exI[where x=D], rule exI[where x="\<lambda>g A. J g (paper_to_pterm A)"],
      rule exI[where x=V], rule conjI[OF source_model source_realizes])
qed

end
