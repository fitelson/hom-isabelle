theory Bacon_Source_Relational_Naming_Logical_Chart
  imports Bacon_Source_Relational_Naming_Structure
begin

section \<open>One actual chart interprets a primitive formula and its operands\<close>

context paper_R_bbk_model
begin

lemma paper_R_naming_unary_values:
  assumes whole: "paper_R_in_language (paper_R_naming_signature signature domain) stock (NApp (NLogical l) A) Prop"
    and operand: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<sigma>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
  obtains h C where "paper_R_in_language signature stock C \<sigma>"
    and "named_env_typed domain stock h" and "named_adequate h C"
    and "paper_R_naming_denote g A = denote h C"
    and "paper_R_naming_denote g (NApp (NLogical l) A) = denote h (NApp (NLogical l) C)"
proof -
  note finish = that
  let ?W = "NApp (NLogical l) A"
  let ?x = "paper_R_naming_chosen_chart stock ?W"
  let ?K = "paper_R_naming_support ?W"
  let ?N = "named_vars ?W"
  let ?h = "paper_R_naming_override ?K ?x g"
  let ?C = "paper_R_naming_replace ?x A"
  have chart: "paper_R_naming_chart stock ?K ?N ?x"
    by (rule paper_R_naming_chosen_chart_language[OF stock_rich whole])
  have names: "named_in_signature (paper_R_naming_signature signature domain) ?W"
    using whole unfolding paper_R_in_language_def by blast
  have payloads: "\<forall>k\<in>?K. snd k \<in> domain (fst k)"
    by (rule paper_R_naming_support_values[OF names])
  have support: "paper_R_naming_support A \<subseteq> ?K" and avoid: "named_vars A \<subseteq> ?N" by auto
  have cl: "paper_R_in_language signature stock ?C \<sigma>"
    by (rule paper_R_naming_replace_language[OF operand chart support])
  have ht: "named_env_typed domain stock ?h" by (rule paper_R_naming_override_typed[OF typed chart payloads])
  have ca: "named_adequate ?h ?C" by (rule paper_R_naming_override_adequate[OF adequate support])
  have value_operand: "paper_R_naming_denote g A = denote ?h ?C"
    by (rule paper_R_naming_denote_common_chart[OF operand typed adequate chart support avoid payloads])
  have wa: "named_adequate g ?W" using adequate unfolding named_adequate_def by auto
  have value_whole: "paper_R_naming_denote g ?W = denote ?h (NApp (NLogical l) ?C)"
    using paper_R_naming_denote_common_chart[OF whole typed wa chart subset_refl subset_refl payloads]
    by (simp only: paper_R_naming_replace.simps)
  show thesis by (rule finish[OF cl ht ca value_operand value_whole])
qed

lemma paper_R_naming_binary_values:
  assumes whole: "paper_R_in_language (paper_R_naming_signature signature domain) stock (NApp (NApp (NLogical l) A) B) Prop"
    and first: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<sigma>"
    and second: "paper_R_in_language (paper_R_naming_signature signature domain) stock B \<tau>"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  obtains h C E where "paper_R_in_language signature stock C \<sigma>"
    and "paper_R_in_language signature stock E \<tau>" and "named_env_typed domain stock h"
    and "named_adequate h C" and "named_adequate h E"
    and "paper_R_naming_denote g A = denote h C" and "paper_R_naming_denote g B = denote h E"
    and "paper_R_naming_denote g (NApp (NApp (NLogical l) A) B) = denote h (NApp (NApp (NLogical l) C) E)"
proof -
  note finish = that
  let ?W = "NApp (NApp (NLogical l) A) B"
  let ?x = "paper_R_naming_chosen_chart stock ?W"
  let ?K = "paper_R_naming_support ?W"
  let ?N = "named_vars ?W"
  let ?h = "paper_R_naming_override ?K ?x g"
  let ?C = "paper_R_naming_replace ?x A"
  let ?E = "paper_R_naming_replace ?x B"
  have chart: "paper_R_naming_chart stock ?K ?N ?x"
    by (rule paper_R_naming_chosen_chart_language[OF stock_rich whole])
  have names: "named_in_signature (paper_R_naming_signature signature domain) ?W"
    using whole unfolding paper_R_in_language_def by blast
  have payloads: "\<forall>k\<in>?K. snd k \<in> domain (fst k)" by (rule paper_R_naming_support_values[OF names])
  have asupport: "paper_R_naming_support A \<subseteq> ?K" and bsupport: "paper_R_naming_support B \<subseteq> ?K"
    and aavoid: "named_vars A \<subseteq> ?N" and bavoid: "named_vars B \<subseteq> ?N" by auto
  have cl: "paper_R_in_language signature stock ?C \<sigma>"
    by (rule paper_R_naming_replace_language[OF first chart asupport])
  have el: "paper_R_in_language signature stock ?E \<tau>"
    by (rule paper_R_naming_replace_language[OF second chart bsupport])
  have ht: "named_env_typed domain stock ?h" by (rule paper_R_naming_override_typed[OF typed chart payloads])
  have ca: "named_adequate ?h ?C" by (rule paper_R_naming_override_adequate[OF aa asupport])
  have ea: "named_adequate ?h ?E" by (rule paper_R_naming_override_adequate[OF ba bsupport])
  have left_value: "paper_R_naming_denote g A = denote ?h ?C"
    by (rule paper_R_naming_denote_common_chart[OF first typed aa chart asupport aavoid payloads])
  have right_value: "paper_R_naming_denote g B = denote ?h ?E"
    by (rule paper_R_naming_denote_common_chart[OF second typed ba chart bsupport bavoid payloads])
  have wa: "named_adequate g ?W" using aa ba unfolding named_adequate_def by auto
  have whole_value: "paper_R_naming_denote g ?W = denote ?h (NApp (NApp (NLogical l) ?C) ?E)"
    using paper_R_naming_denote_common_chart[OF whole typed wa chart subset_refl subset_refl payloads]
    by (simp only: paper_R_naming_replace.simps)
  show thesis by (rule finish[OF cl el ht ca ea left_value right_value whole_value])
qed

end

end
