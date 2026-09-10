theory Bacon_Source_ZF_Action_Completeness
  imports Bacon_Source_ZF_Action_Countermodel Bacon_Source_ZF_Action_Classicism_Soundness
begin

section \<open>Validity over all action models on the specified world-index carrier\<close>

definition paper_ZF_record_action_valid :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "paper_ZF_record_action_valid \<Sigma> G A \<longleftrightarrow>
    (\<forall>Obj :: ('c,ZF) paper_bbk_model_data set. \<forall>Ar s t c i Root D T I g.
      paper_ZF_action_model \<Sigma> G Obj Ar s t c i Root D T I \<longrightarrow>
      paper_ZF_action_env_typed D G Root g \<longrightarrow> named_adequate g A \<longrightarrow>
        paper_ZF_action_holds Ar s t c i D T I G (i Root) g A)"

text \<open>
  The world-index type is ('c,ZF) model records. The universal quantifier
  imposes NO BBK predicate on these labels: it ranges over all independent
  action models on that index carrier, with arbitrary frame and action
  data meeting the action-model definition. In particular it is not
  restricted to models supplied by the hull construction.

  Truth is at the root identity under every typed adequate partial
  assignment. The statement is relative to HOL-ZF and does not quantify
  polymorphically over all possible HOL world-index types.
\<close>

theorem paper_ZF_classicism_action_valid:
  assumes derivation: "paper_R_classicism_proves \<Sigma> G A"
  shows "paper_ZF_record_action_valid \<Sigma> G A"
proof (unfold paper_ZF_record_action_valid_def, intro allI impI)
  fix Obj Ar s t c i Root D T I g
  assume model: "paper_ZF_action_model \<Sigma> G Obj Ar s t c i Root D T I"
    and typed: "paper_ZF_action_env_typed D G Root g" and adequate: "named_adequate g A"
  show "paper_ZF_action_holds Ar s t c i D T I G (i Root) g A"
    using paper_ZF_action_classicism_soundness[OF model derivation] typed adequate by blast
qed

theorem paper_ZF_classicism_action_complete:
  fixes B :: ZF and \<Sigma> :: "'c ssignature" and A :: "'c paper_named_term"
  assumes infinite: "infinite (explode B)"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of (explode B)"
    and rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G A Prop"
    and valid: "paper_ZF_record_action_valid \<Sigma> G A"
  shows "paper_R_classicism_proves \<Sigma> G A"
proof (rule ccontr)
  assume missing: "\<not> paper_R_classicism_proves \<Sigma> G A"
  obtain Obj :: "('c,ZF) paper_bbk_model_data set" and Ar s t c i Root D T I g
    where model: "paper_ZF_action_model \<Sigma> G Obj Ar s t c i Root D T I"
    and typed: "paper_ZF_action_env_typed D G Root g" and adequate: "named_adequate g A"
    and false_at: "\<not> paper_ZF_action_holds Ar s t c i D T I G (i Root) g A"
    using paper_ZF_action_countermodel[OF infinite names rich language missing] by blast
  have true_at: "paper_ZF_action_holds Ar s t c i D T I G (i Root) g A"
    using valid model typed adequate unfolding paper_ZF_record_action_valid_def by blast
  show False using false_at true_at by contradiction
qed

theorem paper_ZF_classicism_action_iff:
  fixes B :: ZF and \<Sigma> :: "'c ssignature" and A :: "'c paper_named_term"
  assumes infinite: "infinite (explode B)"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of (explode B)"
    and rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G A Prop"
  shows "paper_R_classicism_proves \<Sigma> G A \<longleftrightarrow> paper_ZF_record_action_valid \<Sigma> G A"
proof
  assume derivation: "paper_R_classicism_proves \<Sigma> G A"
  show "paper_ZF_record_action_valid \<Sigma> G A" by (rule paper_ZF_classicism_action_valid[OF derivation])
next
  assume valid: "paper_ZF_record_action_valid \<Sigma> G A"
  show "paper_R_classicism_proves \<Sigma> G A"
    by (rule paper_ZF_classicism_action_complete[OF infinite names rich language valid])
qed

text \<open>
  This combines independent action-model soundness with the constructed
  action countermodel for each non-theorem. It covers open R formulas;
  the counterassignment is not replaced by the empty assignment.
  The arbitrary-signature theorem retains its bound by an actual
  infinite HOL-ZF set B. It makes no assertion that every ambient HOL
  constant carrier has a bounded injection into ZF.
  Source: Theorem 3.23, p.58, through Propositions 3.21–3.22,
  pp.57 and 72.
\<close>

end
