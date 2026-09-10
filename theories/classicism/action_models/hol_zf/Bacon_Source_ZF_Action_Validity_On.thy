theory Bacon_Source_ZF_Action_Validity_On
  imports Bacon_Source_ZF_Action_Completeness
begin

section \<open>Action validity on an explicitly specified world-label type\<close>

definition paper_ZF_action_valid_on ::
  "'o itself \<Rightarrow> 'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "paper_ZF_action_valid_on (world_type :: 'o itself) \<Sigma> G A \<longleftrightarrow>
    (\<forall>Obj :: 'o set. \<forall>Ar s t c i Root D T I g.
      paper_ZF_action_model \<Sigma> G Obj Ar s t c i Root D T I \<longrightarrow>
      paper_ZF_action_env_typed D G Root g \<longrightarrow> named_adequate g A \<longrightarrow>
        paper_ZF_action_holds Ar s t c i D T I G (i Root) g A)"

text \<open>
  The type witness TYPE('o) fixes the world-label carrier explicitly.
  The quantified objects, arrows, frame maps, domains, transports and
  constant values range over ALL independent action models on that
  carrier. No BBK condition is imposed on the labels, even when the
  label type happens to be a record type.

  These are exactly the existing universal validity clauses, with the
  world type made independent of the nonlogical constant-name type.
  The old record-indexed definition is retained unchanged. Source:
  Definition 3.20, p.56, and Theorem 3.23, p.58. No world encoding,
  completeness statement or model-existence premise is introduced.
\<close>

lemma paper_ZF_record_action_valid_as_valid_on:
  fixes \<Sigma> :: "'c ssignature"
  shows "paper_ZF_record_action_valid \<Sigma> G A =
    paper_ZF_action_valid_on TYPE(('c,ZF) paper_bbk_model_data) \<Sigma> G A"
  by (simp only: paper_ZF_record_action_valid_def paper_ZF_action_valid_on_def)

section \<open>Native Classicism is sound on every world-label type\<close>

theorem paper_ZF_classicism_valid_on:
  assumes derivation: "paper_R_classicism_proves \<Sigma> G A"
  shows "paper_ZF_action_valid_on TYPE('o) \<Sigma> G A"
proof (unfold paper_ZF_action_valid_on_def, intro allI impI)
  fix Obj :: "'o set"
  fix Ar s t c i Root D T I g
  assume model: "paper_ZF_action_model \<Sigma> G Obj Ar s t c i Root D T I"
    and typed: "paper_ZF_action_env_typed D G Root g"
    and adequate: "named_adequate g A"
  show "paper_ZF_action_holds Ar s t c i D T I G (i Root) g A"
    using paper_ZF_action_classicism_soundness[OF model derivation] typed adequate by blast
qed

end
