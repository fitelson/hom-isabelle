theory Goodman_Exact_QLN_Model
  imports Goodman_Exact_Generic_Interpretation Goodman_Exact_QLN_Transfer
begin

section \<open>The complete native zeroary/unary QLN background\<close>

definition gi_native_QLN_background where
  "gi_native_QLN_background G = gb_recombination_background G \<union> gb_exhaustion_axioms G"

theorem gi_exact_generic_QLN_background_gvalid:
  assumes rich: "sg_rich G" and member: "A \<in> gi_native_QLN_background G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G A"
  using member unfolding gi_native_QLN_background_def gb_recombination_background_def
    gb_exhaustion_axioms_def
  by (auto intro: gi_exact_generic_background_gvalid[OF rich]
    gi_exact_generic_zeroary_recombination_gvalid[OF rich]
    gi_exact_generic_unary_recombination_gvalid[OF rich]
    gi_exact_generic_zeroary_exhaustion_gvalid[OF rich]
    gi_exact_generic_unary_exhaustion_gvalid[OF rich])

corollary gi_exact_generic_QLN_background_consistent:
  assumes rich: "sg_rich G"
  shows "goodman_book_consistent gb_signature G (gi_native_QLN_background G)"
  by (rule pp_e_constants.gi_exact_goodman_consistent_of_global_axioms[
    OF gi_exact_generic_constants rich gi_exact_generic_QLN_background_gvalid[OF rich]])

section \<open>The remaining PP condition is membership of the actual classifier\<close>

lemma gi_exact_generic_target_PP_value:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_goodman_denote pp_e_generic_internal_constants G g gb_target_PP =
    pp_e_eval pp_e_generic_internal_constants pp_e_closed_env pp_target_PP"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of pp_target_PP \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_target_PP_def pp_purity_of_pure_def pp_pure_def pp_Pure_def)
  have denotation: "gi_exact_goodman_denote pp_e_generic_internal_constants G g
      (gi_to_book G [] k pp_target_PP) =
    pp_e_eval pp_e_generic_internal_constants pp_e_closed_env pp_target_PP"
    by (rule pp_e_constants.gi_exact_goodman_closed_denotation_translation[
      OF gi_exact_generic_constants rich typed_pp_target_PP typed names vocabulary])
  show ?thesis using denotation by (simp only: gi_PP_translation[OF names])
qed

theorem gi_exact_generic_native_PP_holds_iff:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_valuation w (gi_exact_goodman_denote pp_e_generic_internal_constants G g gb_target_PP)
    \<longleftrightarrow> gi_exact_native_logical_stock G (Arr gb_unary Prop) w
      (pp_e_classifier gb_unary (pp_e_closed_logical_stock gb_unary))"
  by (simp only: gi_exact_generic_target_PP_value[OF rich typed]
    gi_exact_valuation_def pp_e_generic_target_PP_holds_iff
    gi_exact_native_stock_iff_original[OF rich])

theorem gi_exact_generic_native_PP_global_iff:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G gb_target_PP
    \<longleftrightarrow> gi_exact_native_logical_stock G (Arr gb_unary Prop) []
      (pp_e_classifier gb_unary (pp_e_closed_logical_stock gb_unary))"
proof -
  have all_worlds: "gi_exact_goodman_global_valid pp_e_generic_internal_constants G gb_target_PP
    \<longleftrightarrow> (\<forall>w. gi_exact_native_logical_stock G (Arr gb_unary Prop) w
      (pp_e_classifier gb_unary (pp_e_closed_logical_stock gb_unary)))"
    unfolding gi_exact_goodman_global_valid_iff
    using gi_exact_generic_native_PP_holds_iff[OF rich]
      gi_exact_default_assignment_typed[where G=G] by blast
  show ?thesis by (simp only: all_worlds gi_exact_native_stock_iff_original[OF rich]
    pp_e_closed_logical_stock_all_worlds_iff_root)
qed

theorem gi_exact_generic_native_QLN_PP_global_iff:
  assumes rich: "sg_rich G"
  shows "(\<forall>A \<in> gb_zeroary_unary_QLN_PP_axioms G.
      gi_exact_goodman_global_valid pp_e_generic_internal_constants G A)
    \<longleftrightarrow> gi_exact_native_logical_stock G (Arr gb_unary Prop) []
      (pp_e_classifier gb_unary (pp_e_closed_logical_stock gb_unary))"
proof -
  have package: "gb_zeroary_unary_QLN_PP_axioms G = insert gb_target_PP (gi_native_QLN_background G)"
    unfolding gb_zeroary_unary_QLN_PP_axioms_def gb_recombination_PP_axioms_def
      gi_native_QLN_background_def by auto
  show ?thesis
    using gi_exact_generic_QLN_background_gvalid[OF rich]
    by (simp add: package gi_exact_generic_native_PP_global_iff[OF rich])
qed

corollary gi_exact_generic_native_QLN_PP_consistent_if_classifier:
  assumes rich: "sg_rich G"
    and classifier: "gi_exact_native_logical_stock G (Arr gb_unary Prop) []
      (pp_e_classifier gb_unary (pp_e_closed_logical_stock gb_unary))"
  shows "goodman_book_consistent gb_signature G (gb_zeroary_unary_QLN_PP_axioms G)"
proof (rule pp_e_constants.gi_exact_goodman_consistent_of_global_axioms[
    OF gi_exact_generic_constants rich])
  fix A assume "A \<in> gb_zeroary_unary_QLN_PP_axioms G"
  then show "gi_exact_goodman_global_valid pp_e_generic_internal_constants G A"
    using classifier gi_exact_generic_native_QLN_PP_global_iff[OF rich] by blast
qed

text \<open>
  The QLN background is instantiated on the exact carriers and its native
  logical-purity schema includes every closed logical named term. This
  supplies a consistency theorem relative to HOL–ZF for that background.
  PP itself is not validated: the final implication retains membership of
  the actual unary Pure classifier in the complete logical stock. That
  membership premise has not been established here; consistency of the
  background alone establishes neither the membership premise nor PP.

  The interpretation of Fun uses the world-indexed generic seed. We have
  not identified it with the particular fundamental proposition obtained
  by a separate application of Bacon's Theorem 10.1.
\<close>

end
