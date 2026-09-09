theory Bacon_Source_Relational_Naming_Boolean_Truth
  imports Bacon_Source_Relational_Naming_Logical_Chart Bacon_Source_Relational_Identity_Axiom_Truth
begin

section \<open>The original valuation supplies Boolean and identity truth\<close>

text \<open>
  Each application formula and its operands use one actual finite chart.
  The original valuation is unchanged. Identity compares the resulting
  values themselves, not their truth values. Source: Definition 3.1(iii),
  p.44, and the naming extension of p.51 n.73.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_naming_neg_truth:
  assumes language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A Prop"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
  shows "valuation (paper_R_naming_denote g (NApp (NLogical SNot) A)) =
    (\<not> valuation (paper_R_naming_denote g A))"
proof -
  have whole: "paper_R_in_language (paper_R_naming_signature signature domain) stock (NApp (NLogical SNot) A) Prop"
    using paper_R_named_not_language[OF language] by (simp only: named_paper_not_def)
  obtain h C where cl: "paper_R_in_language signature stock C Prop" and ht: "named_env_typed domain stock h"
    and ca: "named_adequate h C" and av: "paper_R_naming_denote g A = denote h C"
    and wv: "paper_R_naming_denote g (NApp (NLogical SNot) A) = denote h (NApp (NLogical SNot) C)"
    by (rule paper_R_naming_unary_values[OF whole language typed adequate])
  show ?thesis by (simp only: wv av; rule valuation_neg[OF cl ht ca])
qed

theorem paper_R_naming_conj_truth:
  assumes first: "paper_R_in_language (paper_R_naming_signature signature domain) stock A Prop"
    and second: "paper_R_in_language (paper_R_naming_signature signature domain) stock B Prop"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "valuation (paper_R_naming_denote g (NApp (NApp (NLogical SAnd) A) B)) =
    (valuation (paper_R_naming_denote g A) \<and> valuation (paper_R_naming_denote g B))"
proof -
  have whole: "paper_R_in_language (paper_R_naming_signature signature domain) stock (NApp (NApp (NLogical SAnd) A) B) Prop"
    using paper_R_named_and_language[OF first second] by (simp only: named_paper_and_def)
  obtain h C E where cl: "paper_R_in_language signature stock C Prop" and el: "paper_R_in_language signature stock E Prop"
    and ht: "named_env_typed domain stock h" and ca: "named_adequate h C" and ea: "named_adequate h E"
    and av: "paper_R_naming_denote g A = denote h C" and bv: "paper_R_naming_denote g B = denote h E"
    and wv: "paper_R_naming_denote g (NApp (NApp (NLogical SAnd) A) B) = denote h (NApp (NApp (NLogical SAnd) C) E)"
    by (rule paper_R_naming_binary_values[OF whole first second typed aa ba])
  show ?thesis by (simp only: wv av bv; rule valuation_conj[OF cl el ht ca ea])
qed

theorem paper_R_naming_disj_truth:
  assumes first: "paper_R_in_language (paper_R_naming_signature signature domain) stock A Prop"
    and second: "paper_R_in_language (paper_R_naming_signature signature domain) stock B Prop"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "valuation (paper_R_naming_denote g (NApp (NApp (NLogical SOr) A) B)) =
    (valuation (paper_R_naming_denote g A) \<or> valuation (paper_R_naming_denote g B))"
proof -
  have whole: "paper_R_in_language (paper_R_naming_signature signature domain) stock (NApp (NApp (NLogical SOr) A) B) Prop"
    using paper_R_named_or_language[OF first second] by (simp only: named_paper_or_def)
  obtain h C E where cl: "paper_R_in_language signature stock C Prop" and el: "paper_R_in_language signature stock E Prop"
    and ht: "named_env_typed domain stock h" and ca: "named_adequate h C" and ea: "named_adequate h E"
    and av: "paper_R_naming_denote g A = denote h C" and bv: "paper_R_naming_denote g B = denote h E"
    and wv: "paper_R_naming_denote g (NApp (NApp (NLogical SOr) A) B) = denote h (NApp (NApp (NLogical SOr) C) E)"
    by (rule paper_R_naming_binary_values[OF whole first second typed aa ba])
  show ?thesis by (simp only: wv av bv; rule valuation_disj[OF cl el ht ca ea])
qed

theorem paper_R_naming_identity_truth:
  assumes first: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<sigma>"
    and second: "paper_R_in_language (paper_R_naming_signature signature domain) stock B \<sigma>"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "valuation (paper_R_naming_denote g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) =
    (paper_R_naming_denote g A = paper_R_naming_denote g B)"
proof -
  have whole: "paper_R_in_language (paper_R_naming_signature signature domain) stock (NApp (NApp (NLogical (SEq \<sigma>)) A) B) Prop"
    using paper_R_named_eq_language[OF first second] by (simp only: named_paper_eq_def)
  obtain h C E where cl: "paper_R_in_language signature stock C \<sigma>" and el: "paper_R_in_language signature stock E \<sigma>"
    and ht: "named_env_typed domain stock h" and ca: "named_adequate h C" and ea: "named_adequate h E"
    and av: "paper_R_naming_denote g A = denote h C" and bv: "paper_R_naming_denote g B = denote h E"
    and wv: "paper_R_naming_denote g (NApp (NApp (NLogical (SEq \<sigma>)) A) B) = denote h (NApp (NApp (NLogical (SEq \<sigma>)) C) E)"
    by (rule paper_R_naming_binary_values[OF whole first second typed aa ba])
  show ?thesis by (simp only: wv av bv; rule valuation_identity[OF cl el ht ca ea])
qed

end

end
