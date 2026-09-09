theory Bacon_Source_ZF_Arbitrary_Signature_Action_Countermodel
  imports Bacon_Source_ZF_Pure_Action_Completeness Bacon_Source_ZF_Action_Constant_Pullback
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Signature_Compression_Proof
begin

section \<open>An action countermodel without a signature-cardinality premise\<close>

text \<open>
  Retain the finitely many names occurring in A and collapse all other
  names to one dummy. The type-indexed section proves that the compressed
  formula remains a native C non-theorem. Its declared signature is finite,
  so the existing Nat-bounded countermodel construction applies.

  Pull back only the interpretation of constants along the compression
  map. The frame, root, domains, transports and counterassignment remain
  unchanged. Their world-index carrier is the COMPRESSED-name record
  type ('c+unit,ZF), even after the action signature returns to Σ.
  Those records serve only as labels of the resulting action model.

  No cardinal bound on Σ, representation of the entire ambient name
  type, model premise, or world reindexing is used. This is a single-formula
  countermodel theorem, not compression of an arbitrary infinite theory.
  Source role: Theorem 3.23, relative to the standard HOL-ZF foundation.
\<close>

theorem paper_ZF_arbitrary_signature_action_countermodel:
  fixes \<Sigma> :: "'c ssignature" and A :: "'c paper_named_term"
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G A Prop"
    and missing: "\<not> paper_R_classicism_proves \<Sigma> G A"
  shows "\<exists>Obj :: ('c + unit,ZF) paper_bbk_model_data set. \<exists>Ar :: ZF.
    \<exists>s :: ZF \<Rightarrow> ('c + unit,ZF) paper_bbk_model_data. \<exists>t :: ZF \<Rightarrow> ('c + unit,ZF) paper_bbk_model_data.
    \<exists>c :: ZF \<Rightarrow> ZF \<Rightarrow> ZF. \<exists>i :: ('c + unit,ZF) paper_bbk_model_data \<Rightarrow> ZF.
    \<exists>Root :: ('c + unit,ZF) paper_bbk_model_data.
    \<exists>D :: otype \<Rightarrow> ('c + unit,ZF) paper_bbk_model_data \<Rightarrow> ZF.
    \<exists>T :: otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF. \<exists>I :: otype \<Rightarrow> 'c \<Rightarrow> ZF.
    \<exists>g :: ZF named_assignment.
      paper_ZF_action_model \<Sigma> G Obj Ar s t c i Root D T I \<and>
      paper_ZF_action_env_typed D G Root g \<and> named_adequate g A \<and>
      \<not> paper_ZF_action_holds Ar s t c i D T I G (i Root) g A"
proof -
  let ?K = "paper_R_constant_names A"
  let ?f = "paper_R_compress_name ?K"
  let ?\<Omega> = "paper_R_compressed_signature \<Sigma> ?K"
  let ?C = "paper_R_constant_map ?f A"
  have names_countable: "countable (\<Union>\<sigma>. ?\<Omega> \<sigma>)"
    by (rule paper_R_compressed_signature_countable[OF paper_R_constant_names_finite])
  have names_bound: "card_of (\<Union>\<sigma>. ?\<Omega> \<sigma>) \<le>o card_of (explode HOLZF.Nat)"
    by (rule paper_ZF_countable_set_Nat_bound[OF names_countable])
  have compact_language: "paper_R_in_language ?\<Omega> G ?C Prop"
    by (rule paper_R_compression_language[OF language])
  have compact_missing: "\<not> paper_R_classicism_proves ?\<Omega> G ?C"
    by (rule paper_R_compression_non_theorem[OF missing subset_refl])
  obtain Obj :: "('c + unit,ZF) paper_bbk_model_data set" and Ar s t c i Root D T I g
    where compact_model: "paper_ZF_action_model ?\<Omega> G Obj Ar s t c i Root D T I"
    and typed: "paper_ZF_action_env_typed D G Root g" and compact_adequate: "named_adequate g ?C"
    and compact_false: "\<not> paper_ZF_action_holds Ar s t c i D T I G (i Root) g ?C"
    using paper_ZF_action_countermodel[OF paper_ZF_nat_values_infinite names_bound rich compact_language compact_missing] by blast
  let ?I = "\<lambda>\<sigma> b. I \<sigma> (?f b)"
  have maps: "(\<lambda>_. ?f) \<sigma> b \<in> ?\<Omega> \<sigma>" if "b \<in> \<Sigma> \<sigma>" for \<sigma> b
    by (rule paper_R_compressed_signature_maps[where \<Sigma>="\<Sigma>" and K="?K" and \<sigma>="\<sigma>", OF that])
  have model: "paper_ZF_action_model \<Sigma> G Obj Ar s t c i Root D T ?I"
    by (rule paper_ZF_action_model_typed_constant_pullback[where \<rho>="\<lambda>_. ?f", OF compact_model maps])
  have adequate: "named_adequate g A" using compact_adequate
    by (simp only: named_adequate_def paper_R_constant_map_fv)
  have correspondence: "paper_ZF_action_holds Ar s t c i D T ?I G (i Root) g A =
      paper_ZF_action_holds Ar s t c i D T I G (i Root) g ?C"
    by (simp only: paper_ZF_action_holds_typed_constants[where \<rho>="\<lambda>_. ?f"] paper_R_typed_constant_map_uniform)
  have false_at: "\<not> paper_ZF_action_holds Ar s t c i D T ?I G (i Root) g A"
    by (simp only: correspondence; rule compact_false)
  show ?thesis
    by (rule exI[where x=Obj], rule exI[where x=Ar], rule exI[where x=s], rule exI[where x=t],
      rule exI[where x=c], rule exI[where x=i], rule exI[where x=Root], rule exI[where x=D], rule exI[where x=T],
      rule exI[where x="?I"], rule exI[where x=g], rule conjI[OF model], rule conjI[OF typed], rule conjI[OF adequate false_at])
qed

end
