theory Bacon_Source_ZF_Arbitrary_Signature_Action_Completeness
  imports Bacon_Source_ZF_Arbitrary_Signature_Action_Countermodel Bacon_Source_ZF_Action_Validity_On
begin

section \<open>Arbitrary-signature action completeness on the explicit compressed-name label carrier\<close>

theorem paper_ZF_arbitrary_signature_action_complete:
  fixes \<Sigma> :: "'c ssignature" and A :: "'c paper_named_term"
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G A Prop"
    and valid: "paper_ZF_action_valid_on TYPE(('c + unit,ZF) paper_bbk_model_data) \<Sigma> G A"
  shows "paper_R_classicism_proves \<Sigma> G A"
proof (rule ccontr)
  assume missing: "\<not> paper_R_classicism_proves \<Sigma> G A"
  obtain Obj :: "('c + unit,ZF) paper_bbk_model_data set" and Ar s t c i Root D T I g
    where model: "paper_ZF_action_model \<Sigma> G Obj Ar s t c i Root D T I"
    and typed: "paper_ZF_action_env_typed D G Root g" and adequate: "named_adequate g A"
    and false_at: "\<not> paper_ZF_action_holds Ar s t c i D T I G (i Root) g A"
    using paper_ZF_arbitrary_signature_action_countermodel[OF rich language missing] by blast
  have true_at: "paper_ZF_action_holds Ar s t c i D T I G (i Root) g A"
    using valid model typed adequate unfolding paper_ZF_action_valid_on_def by blast
  show False using false_at true_at by contradiction
qed

theorem paper_ZF_arbitrary_signature_action_iff:
  fixes \<Sigma> :: "'c ssignature" and A :: "'c paper_named_term"
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G A Prop"
  shows "paper_R_classicism_proves \<Sigma> G A \<longleftrightarrow>
    paper_ZF_action_valid_on TYPE(('c + unit,ZF) paper_bbk_model_data) \<Sigma> G A"
proof
  assume derivation: "paper_R_classicism_proves \<Sigma> G A"
  show "paper_ZF_action_valid_on TYPE(('c + unit,ZF) paper_bbk_model_data) \<Sigma> G A"
    by (rule paper_ZF_classicism_valid_on[OF derivation])
next
  assume valid: "paper_ZF_action_valid_on TYPE(('c + unit,ZF) paper_bbk_model_data) \<Sigma> G A"
  show "paper_R_classicism_proves \<Sigma> G A"
    by (rule paper_ZF_arbitrary_signature_action_complete[OF rich language valid])
qed

text \<open>
  There is no declared-signature cardinal bound in these statements.
  Completeness uses finite compression of the SINGLE formula and pulls
  back its countermodel's constants; soundness is the independent theorem
  on every world-label type. The quantified action models have arbitrary
  independent frame/action data on the stated label carrier, not a
  requirement that their labels be BBK models.

  The original record-indexed validity definition is unchanged. No world
  reindexing to ('c,ZF) or claim of arbitrary-theory compression is made.
  These results retain R-richness, the R formula guard, typed adequate
  root assignments, and the explicit HOL-ZF foundation.
\<close>

end
