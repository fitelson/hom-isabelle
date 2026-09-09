theory Bacon_Source_Relational_Recoding_Validity
  imports Bacon_Source_Relational_Recoding_Model Bacon_Source_Relational_Validity_Basics
begin

section \<open>Carrier recoding preserves and reflects validity\<close>

text \<open>
  A is valid in M exactly when it is valid in its recoded copy.
  Pull image-domain assignments back for preservation and push original
  assignments forward for reflection. Both directions cover all typed
  adequate partial assignments, including those for open formulas.

  Source: the validity convention after Definition 3.1, p.44, and
  the countable-model refinement of Theorem 3.2. Injectivity is only
  on ⋃σDσ. No surjectivity onto the target carrier is required.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_recode_valid_iff:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
  shows "paper_R_bbk_model.paper_R_valid signature stock (paper_R_recode_domain f domain)
    (paper_R_recode_denote f) (paper_R_recode_valuation f) A \<longleftrightarrow> paper_R_valid A"
proof -
  interpret Coded: paper_R_bbk_model signature stock "paper_R_recode_domain f domain"
    "paper_R_recode_denote f" "paper_R_recode_valuation f"
    by (rule paper_R_recode_model[OF injective])
  show ?thesis
  proof
    assume valid: "Coded.paper_R_valid A"
    have language: "paper_R_in_language signature stock A Prop"
      by (rule Coded.paper_R_valid_language[OF valid])
    show "paper_R_valid A"
    proof (rule paper_R_validI[OF language])
      fix g
      assume typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
      have ct: "named_env_typed (paper_R_recode_domain f domain) stock (paper_R_recode_assignment f g)"
        by (rule paper_R_recode_assignment_typed[OF typed])
      have ca: "named_adequate (paper_R_recode_assignment f g) A"
        by (rule iffD2[OF paper_R_recode_assignment_adequate_iff adequate])
      have truth: "paper_R_recode_valuation f (paper_R_recode_denote f (paper_R_recode_assignment f g) A)"
        by (rule Coded.paper_R_validE[OF valid ct ca])
      show "valuation (denote g A)" using truth
        by (simp only: paper_R_recode_truth[OF injective language ct ca]
          paper_R_recode_assignment_inverse_left[OF injective typed])
    qed
  next
    assume valid: "paper_R_valid A"
    have language: "paper_R_in_language signature stock A Prop"
      by (rule paper_R_valid_language[OF valid])
    show "Coded.paper_R_valid A"
    proof (rule Coded.paper_R_validI[OF language])
      fix g
      assume typed: "named_env_typed (paper_R_recode_domain f domain) stock g"
        and adequate: "named_adequate g A"
      have dt: "named_env_typed domain stock (paper_R_recode_assignment (paper_R_recode_inverse domain f) g)"
        by (rule paper_R_recode_inverse_assignment_typed[OF injective typed])
      have da: "named_adequate (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A"
        by (rule iffD2[OF paper_R_recode_assignment_adequate_iff adequate])
      have truth: "valuation (denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A)"
        by (rule paper_R_validE[OF valid dt da])
      show "paper_R_recode_valuation f (paper_R_recode_denote f g A)"
        by (simp only: paper_R_recode_truth[OF injective language typed adequate]; rule truth)
    qed
  qed
qed

end

end
