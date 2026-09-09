theory Bacon_Source_Relational_Bounded_Classicism_Completeness
  imports Bacon_Source_Relational_Bounded_Classicism_Category
    Bacon_Source_Relational_Bounded_Theory_Common Bacon_Source_Relational_Classicism_Soundness
begin

section \<open>The constructed intensional category has exactly the native C theory\<close>

theorem paper_R_bounded_classicism_common_theory:
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G"
  shows "paper_R_common_theory \<Sigma> G (paper_R_bounded_classicism_models \<Sigma> G U) =
    {A. paper_R_classicism_proves \<Sigma> G A}"
  by (rule paper_R_bounded_models_common_theory[OF infinite names rich paper_R_classicism_is_H_theory])

theorem paper_R_bounded_classicism_representation:
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G"
  shows "paper_category (paper_R_bounded_classicism_models \<Sigma> G U) (paper_R_bounded_classicism_arrows \<Sigma> G U)
      paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) \<and>
    paper_R_intensional_on \<Sigma> G (paper_R_bounded_classicism_models \<Sigma> G U) (paper_R_bounded_classicism_arrows \<Sigma> G U) \<and>
    paper_R_common_theory \<Sigma> G (paper_R_bounded_classicism_models \<Sigma> G U) = {A. paper_R_classicism_proves \<Sigma> G A}"
  by (rule conjI[OF paper_R_bounded_classicism_category],
    rule conjI[OF paper_R_bounded_classicism_intensional[OF infinite names rich]
      paper_R_bounded_classicism_common_theory[OF infinite names rich]])

corollary paper_R_bounded_classicism_valid_iff:
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G"
  shows "paper_R_classicism_proves \<Sigma> G A \<longleftrightarrow>
    A \<in> paper_R_common_theory \<Sigma> G (paper_R_bounded_classicism_models \<Sigma> G U)"
  by (simp only: paper_R_bounded_classicism_common_theory[OF infinite names rich] mem_Collect_eq)

section \<open>Soundness and completeness for all selected categories on the same carrier\<close>

theorem paper_R_classicism_selected_category_iff:
  fixes U :: "'v set" and \<Sigma> :: "'c ssignature"
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G"
  shows "paper_R_classicism_proves \<Sigma> G A \<longleftrightarrow>
    (\<forall>Obj :: ('c,'v) paper_bbk_model_data set. \<forall>Arrows.
      paper_R_bbk_subcategory \<Sigma> G Obj Arrows \<longrightarrow> paper_R_intensional_on \<Sigma> G Obj Arrows \<longrightarrow>
        A \<in> paper_R_common_theory \<Sigma> G Obj)"
proof
  assume derivation: "paper_R_classicism_proves \<Sigma> G A"
  show "\<forall>Obj :: ('c,'v) paper_bbk_model_data set. \<forall>Arrows.
      paper_R_bbk_subcategory \<Sigma> G Obj Arrows \<longrightarrow> paper_R_intensional_on \<Sigma> G Obj Arrows \<longrightarrow>
        A \<in> paper_R_common_theory \<Sigma> G Obj"
    by (intro allI impI; rule paper_R_classicism_category_soundness[OF _ _ derivation]; assumption)
next
  assume universal: "\<forall>Obj :: ('c,'v) paper_bbk_model_data set. \<forall>Arrows.
      paper_R_bbk_subcategory \<Sigma> G Obj Arrows \<longrightarrow> paper_R_intensional_on \<Sigma> G Obj Arrows \<longrightarrow>
        A \<in> paper_R_common_theory \<Sigma> G Obj"
  have common: "A \<in> paper_R_common_theory \<Sigma> G (paper_R_bounded_classicism_models \<Sigma> G U)"
    using universal paper_R_bounded_classicism_subcategory[where \<Sigma>=\<Sigma> and G=G and U=U]
      paper_R_bounded_classicism_intensional[OF infinite names rich] by blast
  show "paper_R_classicism_proves \<Sigma> G A"
    by (rule iffD2[OF paper_R_bounded_classicism_valid_iff[OF infinite names rich] common])
qed

text \<open>
  The converse uses the actual bounded category constructed above and
  the independent H-theory countermodel/common-theory result. It does
  not presuppose C completeness. The forward direction is the earlier
  soundness theorem for arbitrary selected intensional R categories.

  Open formulas are evaluated at every typed adequate partial assignment.
  The quantifiers here range over sets of records and arrows on one
  specified HOL value carrier, not a proper class of varying carriers.
  The declared-signature bound |⋃σΣσ|≤|U| and R-rich stock remain
  explicit. No separate nonemptiness or consistency claim is added.
\<close>

end
