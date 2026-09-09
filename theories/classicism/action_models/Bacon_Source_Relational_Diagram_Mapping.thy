theory Bacon_Source_Relational_Diagram_Mapping
  imports Bacon_Source_Relational_Naming_Model Bacon_Source_Relational_Positive_Diagram
begin

section \<open>Interpreting the value names in a model of the diagram\<close>

text \<open>
  Let M⁺ be the naming expansion of M and N⁺ a model of its positive
  identity diagram. Define hσ(a) to be N⁺'s denotation of the new name
  for a:σ. This name denotes a in M⁺, but need not denote a in N⁺;
  the two models may even have different ambient carriers.

  Every closed A:σ satisfies the identity A=name(⟦A⟧M⁺) in Δ(M⁺).
  Truth of this identity in N⁺ gives
  hσ(⟦A⟧M⁺)=⟦A⟧N⁺. This is the closed-expression part of
  footnote 73's denotation-preserving map, not yet its full open-term
  commuting property. No preservation of truth values is required.
\<close>

locale paper_R_diagram_target =
  source: paper_R_bbk_model \<Sigma> G D J V +
  target: paper_R_bbk_model "paper_R_naming_signature \<Sigma> D" G E K W
  for \<Sigma> :: "'c ssignature" and G :: sgcontext
    and D :: "otype \<Rightarrow> 'v set"
    and J :: "'v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'v"
    and V :: "'v \<Rightarrow> bool"
    and E :: "otype \<Rightarrow> 'w set"
    and K :: "'w named_assignment \<Rightarrow> ('c + 'v) paper_named_term \<Rightarrow> 'w"
    and W :: "'w \<Rightarrow> bool" +
  assumes diagram: "A \<in> paper_R_positive_diagram (paper_R_naming_signature \<Sigma> D) G
    source.paper_R_naming_denote \<Longrightarrow> target.paper_R_valid A"
begin

definition paper_R_diagram_map :: "otype \<Rightarrow> 'v \<Rightarrow> 'w" where
  "paper_R_diagram_map \<sigma> a = K Map.empty (NConst (Inr a) \<sigma>)"

lemma paper_R_diagram_value_name_language:
  assumes member: "a \<in> D \<sigma>"
  shows "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (NConst (Inr a) \<sigma>) \<sigma>"
proof -
  have rt: "paper_R_type \<sigma>" by (rule source.paper_R_domain_member_type[OF member])
  show ?thesis unfolding paper_R_in_language_def
    by (rule conjI[OF paper_R_has_type.Const[OF rt]]; simp add: member)
qed

theorem paper_R_diagram_map_typed:
  assumes member: "a \<in> D \<sigma>"
  shows "paper_R_diagram_map \<sigma> a \<in> E \<sigma>"
proof -
  have language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (NConst (Inr a) \<sigma>) \<sigma>"
    by (rule paper_R_diagram_value_name_language[OF member])
  have typed: "named_env_typed E G Map.empty" by (simp add: named_env_typed_def)
  have adequate: "named_adequate Map.empty (NConst (Inr a) \<sigma>)" by (simp add: named_adequate_def)
  show ?thesis unfolding paper_R_diagram_map_def by (rule target.denote_type[OF language typed adequate])
qed

lemma paper_R_diagram_closed_name_identity:
  assumes language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A \<sigma>"
    and closed: "named_fv A = {}"
  shows "named_paper_eq \<sigma> A (NConst (Inr (source.paper_R_naming_denote Map.empty A)) \<sigma>)
    \<in> paper_R_positive_diagram (paper_R_naming_signature \<Sigma> D) G source.paper_R_naming_denote"
proof -
  let ?a = "source.paper_R_naming_denote Map.empty A"
  have typed: "named_env_typed D G Map.empty" by (simp add: named_env_typed_def)
  have adequate: "named_adequate Map.empty A" by (simp add: named_adequate_def closed)
  have member: "?a \<in> D \<sigma>" by (rule source.paper_R_naming_denote_type[OF language typed adequate])
  have name_language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (NConst (Inr ?a) \<sigma>) \<sigma>"
    by (rule paper_R_diagram_value_name_language[OF member])
  have name_closed: "named_fv (NConst (Inr ?a) \<sigma>) = {}" by simp
  have name_value: "source.paper_R_naming_denote Map.empty (NConst (Inr ?a) \<sigma>) = ?a"
    by (rule source.paper_R_naming_denote_value_constant[OF member typed])
  show ?thesis by (rule paper_R_positive_diagramI[where J=source.paper_R_naming_denote,
    OF language name_language closed name_closed sym[OF name_value]])
qed

theorem paper_R_diagram_map_closed_denote:
  assumes language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A \<sigma>"
    and closed: "named_fv A = {}"
  shows "paper_R_diagram_map \<sigma> (source.paper_R_naming_denote Map.empty A) = K Map.empty A"
proof -
  let ?a = "source.paper_R_naming_denote Map.empty A"
  let ?B = "NConst (Inr ?a) \<sigma> :: ('c + 'v) paper_named_term"
  have source_typed: "named_env_typed D G Map.empty" by (simp add: named_env_typed_def)
  have adequate: "named_adequate Map.empty A" by (simp add: named_adequate_def closed)
  have member: "?a \<in> D \<sigma>" by (rule source.paper_R_naming_denote_type[OF language source_typed adequate])
  have name_language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G ?B \<sigma>"
    by (rule paper_R_diagram_value_name_language[OF member])
  have valid: "target.paper_R_valid (named_paper_eq \<sigma> A ?B)"
    by (rule diagram[OF paper_R_diagram_closed_name_identity[OF language closed]])
  have typed: "named_env_typed E G Map.empty" by (simp add: named_env_typed_def)
  have name_adequate: "named_adequate Map.empty ?B" by (simp add: named_adequate_def)
  have identity_adequate: "named_adequate Map.empty (named_paper_eq \<sigma> A ?B)"
    by (simp add: named_adequate_def named_paper_primitive_fv closed)
  have truth: "W (K Map.empty (named_paper_eq \<sigma> A ?B))"
    by (rule target.paper_R_validE[OF valid typed identity_adequate])
  have same: "K Map.empty A = K Map.empty ?B"
    by (rule iffD1[OF target.valuation_identity[OF language name_language typed adequate name_adequate]];
      use truth in \<open>simp only: named_paper_eq_def\<close>)
  show ?thesis unfolding paper_R_diagram_map_def by (rule sym[OF same])
qed

end

end
