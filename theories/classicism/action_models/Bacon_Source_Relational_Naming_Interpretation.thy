theory Bacon_Source_Relational_Naming_Interpretation
  imports Bacon_Source_Relational_Naming_Chosen_Chart Bacon_Source_Relational_Naming_Larger_Support
begin

section \<open>The actual finite-chart interpretation of the naming language\<close>

text \<open>
  Interpret each expanded term using its chosen finite chart in the
  original model. The already-proved chart independence identifies this
  value with the value computed in every valid chart for the same term.
  Old expressions retain their original denotations, and Inr(a):σ
  denotes a for every a∈Dσ, whether or not a had an old closed name.
  Source: the naming extension ℒ_M in p.51 n.73.

  Only the supplied original R BBK model is used. This leaf establishes
  the interpretation and its basic equations, not the entire expanded
  BBK-model certificate. No new value carrier or valuation is introduced.
\<close>

context paper_R_bbk_model
begin

definition paper_R_naming_denote ::
  "'v named_assignment \<Rightarrow> ('c + 'v) paper_named_term \<Rightarrow> 'v" where
  "paper_R_naming_denote g A = paper_R_naming_chart_denote (paper_R_naming_chosen_chart stock A) g A"

theorem paper_R_naming_denote_at_chart:
  assumes language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and chart: "paper_R_naming_chart stock (paper_R_naming_support A) (named_vars A) x"
  shows "paper_R_naming_denote g A = paper_R_naming_chart_denote x g A"
  unfolding paper_R_naming_denote_def
  by (rule paper_R_naming_chart_denote_independent[
    OF language typed adequate paper_R_naming_chosen_chart_language[OF stock_rich language] chart])

theorem paper_R_naming_denote_type:
  assumes language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
  shows "paper_R_naming_denote g A \<in> domain \<tau>"
proof -
  let ?x = "paper_R_naming_chosen_chart stock A"
  have chart: "paper_R_naming_chart stock (paper_R_naming_support A) (named_vars A) ?x"
    by (rule paper_R_naming_chosen_chart_language[OF stock_rich language])
  have old_language: "paper_R_in_language signature stock (paper_R_naming_replace ?x A) \<tau>"
    by (rule paper_R_naming_replace_language[OF language chart subset_refl])
  have assignment_type: "named_env_typed domain stock (paper_R_naming_override (paper_R_naming_support A) ?x g)"
    by (rule paper_R_naming_term_override_typed[OF language chart typed])
  have assignment_adequate: "named_adequate (paper_R_naming_override (paper_R_naming_support A) ?x g)
      (paper_R_naming_replace ?x A)"
    by (rule paper_R_naming_override_adequate[OF adequate subset_refl])
  show ?thesis unfolding paper_R_naming_denote_def paper_R_naming_chart_denote_def
    by (rule denote_type[OF old_language assignment_type assignment_adequate])
qed

lemma paper_R_naming_denote_old:
  "paper_R_naming_denote g (map_named_term Inl id A) = denote g A"
  by (simp only: paper_R_naming_denote_def paper_R_naming_chart_denote_def
    paper_R_naming_support_old_embedding paper_R_naming_override_empty paper_R_naming_replace_old)

lemma paper_R_naming_denote_var_raw:
  "paper_R_naming_denote g (NVar n) = denote g (NVar n)"
  by (simp only: paper_R_naming_denote_def paper_R_naming_chart_denote_def
    paper_R_naming_support.simps paper_R_naming_override_empty paper_R_naming_replace.simps)

lemma paper_R_naming_denote_logical:
  "paper_R_naming_denote g (NLogical l) = denote g (NLogical l)"
  by (simp only: paper_R_naming_denote_def paper_R_naming_chart_denote_def
    paper_R_naming_support.simps paper_R_naming_override_empty paper_R_naming_replace.simps)

theorem paper_R_naming_denote_var:
  assumes typed: "named_env_typed domain stock g" and assigned: "g n = Some a"
  shows "paper_R_naming_denote g (NVar n) = a"
  by (simp only: paper_R_naming_denote_var_raw; rule denote_var[OF typed assigned])

theorem paper_R_naming_denote_value_constant:
  assumes member: "a \<in> domain \<sigma>" and typed: "named_env_typed domain stock g"
  shows "paper_R_naming_denote g (NConst (Inr a) \<sigma>) = a"
proof -
  let ?A = "NConst (Inr a) \<sigma> :: ('c + 'v) paper_named_term"
  let ?x = "paper_R_naming_chosen_chart stock ?A"
  let ?K = "paper_R_naming_support ?A"
  have rt: "paper_R_type \<sigma>" by (rule paper_R_domain_member_type[OF member])
  have language: "paper_R_in_language (paper_R_naming_signature signature domain) stock ?A \<sigma>"
    unfolding paper_R_in_language_def
    by (rule conjI[OF paper_R_has_type.Const[OF rt]]; simp add: member)
  have chart: "paper_R_naming_chart stock ?K (named_vars ?A) ?x"
    by (rule paper_R_naming_chosen_chart_language[OF stock_rich language])
  have injective: "inj_on ?x ?K" by (rule paper_R_naming_chart_injective[OF chart])
  have key: "(\<sigma>,a) \<in> ?K" by simp
  have assigned: "paper_R_naming_override ?K ?x g (?x (\<sigma>,a)) = Some a"
    using paper_R_naming_override_lookup[OF injective key] by simp
  have assignment_type: "named_env_typed domain stock (paper_R_naming_override ?K ?x g)"
    by (rule paper_R_naming_term_override_typed[OF language chart typed])
  have variable_value: "denote (paper_R_naming_override ?K ?x g) (NVar (?x (\<sigma>,a))) = a"
    by (rule denote_var[OF assignment_type assigned])
  show ?thesis unfolding paper_R_naming_denote_def paper_R_naming_chart_denote_def
    by (simp only: paper_R_naming_replace.simps sum.case; rule variable_value)
qed

theorem paper_R_naming_denote_common_chart:
  assumes language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and chart: "paper_R_naming_chart stock L N x"
    and support: "paper_R_naming_support A \<subseteq> L" and avoid: "named_vars A \<subseteq> N"
    and payloads: "\<forall>k\<in>L. snd k \<in> domain (fst k)"
  shows "paper_R_naming_denote g A = denote (paper_R_naming_override L x g) (paper_R_naming_replace x A)"
  unfolding paper_R_naming_denote_def
  by (rule sym, rule paper_R_naming_common_chart_denote[
    OF language typed adequate chart support avoid payloads
      paper_R_naming_chosen_chart_language[OF stock_rich language]])

end

end
