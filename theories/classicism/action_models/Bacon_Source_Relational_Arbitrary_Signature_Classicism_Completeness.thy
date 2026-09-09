theory Bacon_Source_Relational_Arbitrary_Signature_Classicism_Completeness
  imports Bacon_Source_Relational_Bounded_Classicism_Completeness
begin

section \<open>A sufficiently large value carrier for every signature\<close>

lemma paper_R_signature_value_universe_infinite:
  "infinite (UNIV :: ('c + nat) set)"
proof
  assume finite: "finite (UNIV :: ('c + nat) set)"
  have image_finite: "finite ((Inr :: nat \<Rightarrow> 'c + nat) ` UNIV)"
    by (rule finite_subset[OF subset_UNIV finite])
  have injective: "inj_on (Inr :: nat \<Rightarrow> 'c + nat) UNIV"
    by (auto intro: inj_onI)
  have "finite (UNIV :: nat set)" by (rule finite_imageD[OF image_finite injective])
  then show False by simp
qed

lemma paper_R_declared_names_in_signature_universe:
  fixes \<Sigma> :: "'c ssignature"
  shows "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of (UNIV :: ('c + nat) set)"
  by (rule card_of_ordLeqI[where f="Inl :: 'c \<Rightarrow> 'c + nat"]; auto intro: inj_onI)

theorem paper_R_arbitrary_signature_classicism_representation:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "paper_R_rich G"
  shows "paper_category
      (paper_R_bounded_classicism_models \<Sigma> G (UNIV :: ('c + nat) set))
      (paper_R_bounded_classicism_arrows \<Sigma> G UNIV)
      paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) \<and>
    paper_R_intensional_on \<Sigma> G (paper_R_bounded_classicism_models \<Sigma> G (UNIV :: ('c + nat) set))
      (paper_R_bounded_classicism_arrows \<Sigma> G UNIV) \<and>
    paper_R_common_theory \<Sigma> G (paper_R_bounded_classicism_models \<Sigma> G (UNIV :: ('c + nat) set)) =
      {A. paper_R_classicism_proves \<Sigma> G A}"
  by (rule paper_R_bounded_classicism_representation[
    OF paper_R_signature_value_universe_infinite paper_R_declared_names_in_signature_universe rich])

theorem paper_R_arbitrary_signature_classicism_selected_category_iff:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "paper_R_rich G"
  shows "paper_R_classicism_proves \<Sigma> G A \<longleftrightarrow>
    (\<forall>Obj :: ('c,'c + nat) paper_bbk_model_data set. \<forall>Arrows.
      paper_R_bbk_subcategory \<Sigma> G Obj Arrows \<longrightarrow>
      paper_R_intensional_on \<Sigma> G Obj Arrows \<longrightarrow>
      A \<in> paper_R_common_theory \<Sigma> G Obj)"
  by (rule paper_R_classicism_selected_category_iff[
    OF paper_R_signature_value_universe_infinite paper_R_declared_names_in_signature_universe rich])

text \<open>
  There is no cardinality restriction on Σ here. The chosen value
  carrier is the disjoint sum of its ambient constant-name type with
  ℕ: Inl bounds the declared names, and Inr supplies infinitude.
  These tags are only a cardinality construction, not a requirement
  that any nonlogical constant denote its own name.

  This gives Theorem 3.12's BBK-category soundness/completeness for
  arbitrary signatures on an explicit sufficiently large carrier.
  It does not assert that EVERY previously specified infinite U can
  accommodate an unbounded signature or every consistent Σ-theory.
  The pure-language result on each infinite U remains separate.
\<close>

end
