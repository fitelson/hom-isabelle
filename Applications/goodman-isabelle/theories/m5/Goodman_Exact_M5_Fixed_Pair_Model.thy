theory Goodman_Exact_M5_Fixed_Pair_Model
  imports Goodman_Exact_Basis_QSS
begin

text \<open>
  This separate instance uses the notes' literal pair {[5]}, {[],[5]}.
  No assertion that this fixed pair avoids a preassigned R-orbit is made.
  Rebuilding needs only the invariant value, so the general construction
  applies without the R-dependent avoidance repair.
\<close>

definition gi_exact_M5_fixed_value where
  "gi_exact_M5_fixed_value = gi_exact_M2_classifier (gi_M5_swapped_index {[5]})"

lemma gi_exact_M5_fixed_raw:
  "pp_e_raw_operator gi_exact_M5_fixed_value = gi_M5_exotic {[5]}"
  by (simp only: gi_exact_M5_fixed_value_def gi_exact_M2_classifier_raw gi_M5_exotic_def)

lemma gi_exact_M5_fixed_expanded_stock:
  "gi_exact_expanded_stock gi_M5_exotic_name gi_exact_M5_fixed_value"
proof
  show "gi_M5_exotic_name \<noteq> pp_pure_name" by (simp add: gi_M5_exotic_name_def pp_pure_name_def)
  show "gi_M5_exotic_name \<noteq> pp_fun_name" by (simp add: gi_M5_exotic_name_def pp_fun_name_def)
  show "Elem gi_exact_M5_fixed_value (pp_e_domain gb_unary)"
    unfolding gi_exact_M5_fixed_value_def by (rule gi_exact_M2_classifier_member)
  fix i show "pp_b_action gb_unary i gi_exact_M5_fixed_value = gi_exact_M5_fixed_value"
    unfolding gi_exact_M5_fixed_value_def by (rule gi_exact_M2_classifier_invariant)
qed

abbreviation gi_M5_fixed_constants where
  "gi_M5_fixed_constants \<equiv> gi_M5_rebuilt_constants gi_M5_exotic_name gi_exact_M5_fixed_value"

theorem gi_exact_M5_fixed_QLN_model:
  "sg_rich G \<Longrightarrow> A \<in> gi_native_QLN_background G \<Longrightarrow>
    gi_exact_goodman_global_valid gi_M5_fixed_constants G A"
  by (rule gi_exact_expanded_stock.gi_M5_rebuilt_native_QLN_background_gvalid[OF gi_exact_M5_fixed_expanded_stock]; assumption)

theorem gi_exact_M5_fixed_QSS_model:
  "sg_rich G \<Longrightarrow> gi_exact_goodman_global_valid gi_M5_fixed_constants G (gb_QSS G)"
  by (rule gi_exact_expanded_stock.gi_M5_rebuilt_native_QSS_gvalid[OF gi_exact_M5_fixed_expanded_stock]; assumption)

theorem gi_exact_M5_fixed_operator_pure:
  "pp_e_holds (pp_e_eval gi_M5_fixed_constants \<rho> (pp_pure gb_unary (Const gi_M5_exotic_name gb_unary))) w"
  by (rule gi_exact_expanded_stock.gi_M5_rebuilt_K_pure_holds[OF gi_exact_M5_fixed_expanded_stock])

theorem gi_exact_M5_fixed_operator_denotation:
  "pp_e_eval gi_M5_fixed_constants \<rho> (Const gi_M5_exotic_name gb_unary) = gi_exact_M5_fixed_value"
  by (rule gi_exact_expanded_stock.gi_M5_rebuilt_exotic_constant_denotation[OF gi_exact_M5_fixed_expanded_stock])

theorem gi_exact_M5_fixed_operator_involution:
  assumes pm: "Elem p (pp_e_domain Prop)"
  shows "gi_exact_M5_fixed_value \<acute> (gi_exact_M5_fixed_value \<acute> p) = p"
proof -
  have km: "Elem gi_exact_M5_fixed_value (pp_e_domain gb_unary)"
    unfolding gi_exact_M5_fixed_value_def by (rule gi_exact_M2_classifier_member)
  have cm: "Elem (gi_exact_value_compose gi_exact_M5_fixed_value gi_exact_M5_fixed_value) (pp_e_domain gb_unary)"
    by (rule gi_exact_value_compose_member[OF km km])
  have im: "Elem (pp_e_closed_den pp_identity_operator) (pp_e_domain gb_unary)"
    by (rule pp_e_closed_den_in_domain[OF typed_pp_identity_operator[unfolded pp_unary_ty_def]])
  have raw: "pp_e_raw_operator (gi_exact_value_compose gi_exact_M5_fixed_value gi_exact_M5_fixed_value) =
    pp_e_raw_operator (pp_e_closed_den pp_identity_operator)"
    by (rule ext; simp only: gi_exact_raw_value_compose[OF km km] gi_exact_M5_fixed_raw
      pp_e_raw_operator_identity comp_apply gi_M5_fixed_exotic_involution id_apply)
  have square: "gi_exact_value_compose gi_exact_M5_fixed_value gi_exact_M5_fixed_value = pp_e_closed_den pp_identity_operator"
    by (rule gi_exact_raw_operator_injective[OF cm im raw])
  have applied: "gi_exact_value_compose gi_exact_M5_fixed_value gi_exact_M5_fixed_value \<acute> p =
    pp_e_closed_den pp_identity_operator \<acute> p" by (rule arg_cong[OF square, where f="\<lambda>F. F \<acute> p"])
  show ?thesis using applied by (simp only: gi_exact_value_compose_def pp_e_closed_den_def
    pp_identity_operator_def pp_e_eval.simps Lambda_app[OF pm] extend_env.simps)
qed

theorem gi_exact_M5_fixed_operator_classification_failure:
  "\<not> gi_M5_truth_preserving (pp_e_raw_operator gi_exact_M5_fixed_value) \<and>
    \<not> gi_M5_truth_flipping (pp_e_raw_operator gi_exact_M5_fixed_value)"
  "\<not> (\<exists>A. pp_e_raw_operator gi_exact_M5_fixed_value = gi_M5_biconditional_operator A)"
  by (simp only: gi_exact_M5_fixed_raw;
    (rule gi_M5_no_echo_pair.not_truth_uniform[OF gi_M5_fixed_pair]
      | rule gi_M5_no_echo_pair.not_biconditional[OF gi_M5_fixed_pair]))+

text \<open>All conclusions concern the same rebuilt exact interpreter. The
  classification failure is stated through its faithful raw representation;
  PP and root evaluations of classification sentences are not added here.\<close>

end
