theory Bacon_Source_Relational_Recoding_Truth
  imports Bacon_Source_Relational_Recoding_Structure Bacon_Source_Relational_Identity_Proof_Basics
begin

section \<open>Boolean and identity truth survive guarded carrier recoding\<close>

text \<open>
  Every use of the inverse at a denotation is guarded by an R-language
  term and a typed adequate image assignment. Injectivity is confined to
  ⋃σDσ. The source model's Boolean and actual-identity clauses then
  transfer directly. Source: Definition 3.1, pp.43–44. No target-model
  certificate, global carrier injection or equality-of-truth-values
  principle is assumed.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_recode_neg_truth:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
    and language: "paper_R_in_language signature stock A Prop"
    and typed: "named_env_typed (paper_R_recode_domain f domain) stock g" and adequate: "named_adequate g A"
  shows "paper_R_recode_valuation f (paper_R_recode_denote f g (NApp (NLogical SNot) A)) =
    (\<not> paper_R_recode_valuation f (paper_R_recode_denote f g A))"
proof -
  let ?g = "paper_R_recode_assignment (paper_R_recode_inverse domain f) g"
  have dt: "named_env_typed domain stock ?g" by (rule paper_R_recode_inverse_assignment_typed[OF injective typed])
  have da: "named_adequate ?g A" by (rule iffD2[OF paper_R_recode_assignment_adequate_iff adequate])
  have whole: "paper_R_in_language signature stock (NApp (NLogical SNot) A) Prop"
    using paper_R_named_not_language[OF language] by (simp only: named_paper_not_def)
  have wa: "named_adequate g (NApp (NLogical SNot) A)"
    using adequate by (simp add: named_adequate_def)
  show ?thesis by (simp only: paper_R_recode_truth[OF injective whole typed wa]
    paper_R_recode_truth[OF injective language typed adequate] valuation_neg[OF language dt da])
qed

theorem paper_R_recode_conj_truth:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
    and al: "paper_R_in_language signature stock A Prop" and bl: "paper_R_in_language signature stock B Prop"
    and typed: "named_env_typed (paper_R_recode_domain f domain) stock g"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "paper_R_recode_valuation f (paper_R_recode_denote f g (NApp (NApp (NLogical SAnd) A) B)) =
    (paper_R_recode_valuation f (paper_R_recode_denote f g A) \<and> paper_R_recode_valuation f (paper_R_recode_denote f g B))"
proof -
  let ?g = "paper_R_recode_assignment (paper_R_recode_inverse domain f) g"
  have dt: "named_env_typed domain stock ?g" by (rule paper_R_recode_inverse_assignment_typed[OF injective typed])
  have da: "named_adequate ?g A" by (rule iffD2[OF paper_R_recode_assignment_adequate_iff aa])
  have db: "named_adequate ?g B" by (rule iffD2[OF paper_R_recode_assignment_adequate_iff ba])
  have whole: "paper_R_in_language signature stock (NApp (NApp (NLogical SAnd) A) B) Prop"
    using paper_R_named_and_language[OF al bl] by (simp only: named_paper_and_def)
  have wa: "named_adequate g (NApp (NApp (NLogical SAnd) A) B)"
    using aa ba by (auto simp: named_adequate_def)
  show ?thesis by (simp only: paper_R_recode_truth[OF injective whole typed wa]
    paper_R_recode_truth[OF injective al typed aa] paper_R_recode_truth[OF injective bl typed ba]
    valuation_conj[OF al bl dt da db])
qed

theorem paper_R_recode_disj_truth:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
    and al: "paper_R_in_language signature stock A Prop" and bl: "paper_R_in_language signature stock B Prop"
    and typed: "named_env_typed (paper_R_recode_domain f domain) stock g"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "paper_R_recode_valuation f (paper_R_recode_denote f g (NApp (NApp (NLogical SOr) A) B)) =
    (paper_R_recode_valuation f (paper_R_recode_denote f g A) \<or> paper_R_recode_valuation f (paper_R_recode_denote f g B))"
proof -
  let ?g = "paper_R_recode_assignment (paper_R_recode_inverse domain f) g"
  have dt: "named_env_typed domain stock ?g" by (rule paper_R_recode_inverse_assignment_typed[OF injective typed])
  have da: "named_adequate ?g A" by (rule iffD2[OF paper_R_recode_assignment_adequate_iff aa])
  have db: "named_adequate ?g B" by (rule iffD2[OF paper_R_recode_assignment_adequate_iff ba])
  have whole: "paper_R_in_language signature stock (NApp (NApp (NLogical SOr) A) B) Prop"
    using paper_R_named_or_language[OF al bl] by (simp only: named_paper_or_def)
  have wa: "named_adequate g (NApp (NApp (NLogical SOr) A) B)"
    using aa ba by (auto simp: named_adequate_def)
  show ?thesis by (simp only: paper_R_recode_truth[OF injective whole typed wa]
    paper_R_recode_truth[OF injective al typed aa] paper_R_recode_truth[OF injective bl typed ba]
    valuation_disj[OF al bl dt da db])
qed

theorem paper_R_recode_identity_truth:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
    and al: "paper_R_in_language signature stock A \<sigma>" and bl: "paper_R_in_language signature stock B \<sigma>"
    and typed: "named_env_typed (paper_R_recode_domain f domain) stock g"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "paper_R_recode_valuation f (paper_R_recode_denote f g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) =
    (paper_R_recode_denote f g A = paper_R_recode_denote f g B)"
proof -
  let ?g = "paper_R_recode_assignment (paper_R_recode_inverse domain f) g"
  have dt: "named_env_typed domain stock ?g" by (rule paper_R_recode_inverse_assignment_typed[OF injective typed])
  have da: "named_adequate ?g A" by (rule iffD2[OF paper_R_recode_assignment_adequate_iff aa])
  have db: "named_adequate ?g B" by (rule iffD2[OF paper_R_recode_assignment_adequate_iff ba])
  have whole: "paper_R_in_language signature stock (NApp (NApp (NLogical (SEq \<sigma>)) A) B) Prop"
    using paper_R_named_identity_language[OF al bl] by (simp only: named_paper_eq_def)
  have wa: "named_adequate g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)"
    using aa ba by (auto simp: named_adequate_def)
  show ?thesis by (simp only: paper_R_recode_truth[OF injective whole typed wa]
    valuation_identity[OF al bl dt da db] paper_R_recode_denote_equal_iff[OF injective al bl typed typed aa ba])
qed

end

end
