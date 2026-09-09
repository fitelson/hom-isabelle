theory Bacon_Source_Relational_Pure_Classicism_Completeness
  imports Bacon_Source_Relational_Bounded_Classicism_Completeness
begin

section \<open>Pure Classicism over every infinite value set\<close>

lemma paper_R_empty_signature_cardinal_bound:
  fixes U :: "'v set"
  shows "card_of (\<Union>\<sigma>. (\<lambda>_ :: otype. {} :: 'c set) \<sigma>) \<le>o card_of U"
  by (rule card_of_ordLeqI[where f="\<lambda>_ :: 'c. (undefined :: 'v)"]; simp)

theorem paper_R_pure_classicism_intensional:
  fixes U :: "'v set"
  assumes infinite: "infinite U" and rich: "paper_R_rich G"
  shows "paper_R_intensional_on (\<lambda>_. {} :: 'c set) G
    (paper_R_bounded_classicism_models (\<lambda>_. {}) G U)
    (paper_R_bounded_classicism_arrows (\<lambda>_. {}) G U)"
  by (rule paper_R_bounded_classicism_intensional[
    OF infinite paper_R_empty_signature_cardinal_bound rich])

theorem paper_R_pure_classicism_common_theory:
  fixes U :: "'v set"
  assumes infinite: "infinite U" and rich: "paper_R_rich G"
  shows "paper_R_common_theory (\<lambda>_. {} :: 'c set) G
    (paper_R_bounded_classicism_models (\<lambda>_. {}) G U) =
    {A. paper_R_classicism_proves (\<lambda>_. {}) G A}"
  by (rule paper_R_bounded_classicism_common_theory[
    OF infinite paper_R_empty_signature_cardinal_bound rich])

theorem paper_R_pure_classicism_selected_category_iff:
  fixes U :: "'v set" and A :: "'c paper_named_term"
  assumes infinite: "infinite U" and rich: "paper_R_rich G"
  shows "paper_R_classicism_proves (\<lambda>_. {}) G A \<longleftrightarrow>
    (\<forall>Obj :: ('c,'v) paper_bbk_model_data set. \<forall>Arrows.
      paper_R_bbk_subcategory (\<lambda>_. {}) G Obj Arrows \<longrightarrow>
      paper_R_intensional_on (\<lambda>_. {}) G Obj Arrows \<longrightarrow>
      A \<in> paper_R_common_theory (\<lambda>_. {}) G Obj)"
  by (rule paper_R_classicism_selected_category_iff[
    OF infinite paper_R_empty_signature_cardinal_bound rich])

text \<open>
  In the pure language ℒ, the nonlogical signature is empty. Its
  cardinal bound is therefore automatic, so each infinite U gives
  the actual intensional model category and the soundness/completeness
  equivalence above. Source: the distinction ℒ / ℒ(Σ) on p.6 and
  the fixed-infinite-set strengthening on p.52.

  These corollaries do not remove the declared-name bound for an
  arbitrary nonlogical signature or for an arbitrary theory requiring
  many distinct named individuals. The HOL value carrier stays fixed
  in the displayed category quantifiers.
\<close>

end
