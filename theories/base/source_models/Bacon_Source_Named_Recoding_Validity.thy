theory Bacon_Source_Named_Recoding_Validity
  imports Bacon_Source_Named_Recoding_Model
begin

section \<open>Validity is preserved and reflected by injective recoding\<close>

text \<open>
  A formula is valid in a named model iff it is valid in its injectively
  recoded copy. Push original assignments forward for one direction;
  pull typed image-domain assignments back for the other. Source role:
  the assignment-based validity convention following Definition 3.1,
  Bacon–Dorr p.44.

  Both directions quantify over all typed adequate partial assignments.
  Open formulas are included. No arbitrary target value outside the coded
  domains is required to have a preimage.
\<close>

context paper_named_bbk_model
begin

theorem named_recode_valid_iff:
  assumes injective: "inj f"
  shows "paper_named_bbk_model.named_valid signature stock (named_image_domain f domain)
    (named_recode_denote f) (named_recode_valuation f) A \<longleftrightarrow> named_valid A"
proof -
  interpret Coded: paper_named_bbk_model signature stock "named_image_domain f domain"
    "named_recode_denote f" "named_recode_valuation f" by (rule named_recode_model[OF injective])
  show ?thesis
  proof
    assume valid: "Coded.named_valid A"
    have language: "named_in_language paper_logical_type signature stock A Prop"
      using valid unfolding Coded.named_valid_def by (rule conjunct1)
    have truths: "\<And>g. named_env_typed (named_image_domain f domain) stock g \<Longrightarrow>
      named_adequate g A \<Longrightarrow> named_recode_valuation f (named_recode_denote f g A)"
      using valid unfolding Coded.named_valid_def Coded.named_satisfies_def by blast
    show "named_valid A"
    proof (unfold named_valid_def, rule conjI[OF language], intro allI impI)
      fix g
      assume typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
      have ct: "named_env_typed (named_image_domain f domain) stock (named_map_assignment f g)"
        by (rule named_map_assignment_typed[OF typed])
      have ca: "named_adequate (named_map_assignment f g) A"
        by (rule iffD2[OF named_map_assignment_adequate adequate])
      have truth: "named_recode_valuation f (named_recode_denote f (named_map_assignment f g) A)"
        by (rule truths[OF ct ca])
      show "named_satisfies g A" using truth
        by (simp only: named_satisfies_def named_recode_truth[OF injective] named_map_inv_map[OF injective])
    qed
  next
    assume valid: "named_valid A"
    have language: "named_in_language paper_logical_type signature stock A Prop"
      using valid unfolding named_valid_def by (rule conjunct1)
    have truths: "\<And>g. named_env_typed domain stock g \<Longrightarrow>
      named_adequate g A \<Longrightarrow> valuation (denote g A)"
      using valid unfolding named_valid_def named_satisfies_def by blast
    show "Coded.named_valid A"
    proof (unfold Coded.named_valid_def, rule conjI[OF language], intro allI impI)
      fix g
      assume typed: "named_env_typed (named_image_domain f domain) stock g" and adequate: "named_adequate g A"
      have qt: "named_env_typed domain stock (named_map_assignment (inv f) g)"
        by (rule named_map_assignment_inv_typed[OF injective typed])
      have qa: "named_adequate (named_map_assignment (inv f) g) A"
        by (rule iffD2[OF named_map_assignment_adequate adequate])
      have truth: "valuation (denote (named_map_assignment (inv f) g) A)" by (rule truths[OF qt qa])
      show "Coded.named_satisfies g A"
        by (simp only: Coded.named_satisfies_def named_recode_truth[OF injective]; rule truth)
    qed
  qed
qed

end

end
