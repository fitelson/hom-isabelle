theory Goodman_Exact_M5_TU_Refutation
  imports Goodman_Exact_M5_Rebuilt_Model
begin

section \<open>The actual TU formula quantifies over the rebuilt pure involution\<close>

lemma gi_M5_identity_value:
  "pp_e_eval C \<rho> pp_identity_operator = pp_e_closed_den pp_identity_operator"
  by (simp add: pp_identity_operator_def pp_e_closed_den_def)

lemma gi_M5_truth_preserving_value:
  "pp_e_holds (pp_e_eval C (extend_env X \<rho>) (pp_truth_preserving (Var 0))) w \<longleftrightarrow>
    (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow> (pp_e_holds (X \<acute> p) w \<longleftrightarrow> pp_e_holds p w))"
  by (simp add: pp_truth_preserving_def pp_e_eval_shift; blast)

lemma gi_M5_truth_flipping_value:
  "pp_e_holds (pp_e_eval C (extend_env X \<rho>) (pp_truth_flipping (Var 0))) w \<longleftrightarrow>
    (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow> (pp_e_holds (X \<acute> p) w \<longleftrightarrow> \<not> pp_e_holds p w))"
  by (simp add: pp_truth_flipping_def pp_e_eval_shift; blast)

context gi_exact_expanded_stock
begin

lemma gi_M5_rebuilt_group_member_value:
  assumes xm: "Elem X (pp_e_domain gb_unary)"
  shows "pp_e_holds (pp_e_eval (gi_M5_rebuilt_constants k K) (extend_env X \<rho>) (pp_group_member (Var 0))) []
    \<longleftrightarrow> gi_basis_pure (gi_M5_expanded_basis k K) gb_unary [] X \<and>
      (\<exists>Y. Elem Y (pp_e_domain gb_unary) \<and> gi_basis_pure (gi_M5_expanded_basis k K) gb_unary [] Y \<and>
        pp_e_eqv gb_unary [] (gi_exact_value_compose X Y) (pp_e_closed_den pp_identity_operator) \<and>
        pp_e_eqv gb_unary [] (gi_exact_value_compose Y X) (pp_e_closed_den pp_identity_operator))"
  using xm
  by (simp only: pp_group_member_def pp_reversible_def pp_pure_def
    pp_e_eval_Conj_holds pp_e_eval_Exists_holds pp_e_eval_Eq_holds
    gi_M5_rebuilt_Pure_value gi_exact_eval_compose pp_e_eval_shift gi_M5_identity_value
    pp_e_eval.simps(1,3) extend_env.simps pp_unary_ty_def pp_e_classifier_holds
    cong: conj_cong)

lemma gi_M5_self_compose_identity:
  assumes involutive: "\<And>p. Elem p (pp_e_domain Prop) \<Longrightarrow> K \<acute> (K \<acute> p) = p"
  shows "gi_exact_value_compose K K = pp_e_closed_den pp_identity_operator"
proof -
  have composed: "Elem (gi_exact_value_compose K K) (pp_e_domain gb_unary)"
    by (rule gi_exact_value_compose_member[OF K_typed K_typed])
  have identity: "Elem (pp_e_closed_den pp_identity_operator) (pp_e_domain gb_unary)"
    by (rule pp_e_closed_den_in_domain[OF typed_pp_identity_operator[unfolded pp_unary_ty_def]])
  show ?thesis
  proof (rule pp_b_function_ext[OF pp_b_arrow_member_function[OF composed] pp_b_arrow_member_function[OF identity]])
    fix p assume pm: "Elem p (pp_e_domain Prop)"
    show "gi_exact_value_compose K K \<acute> p = pp_e_closed_den pp_identity_operator \<acute> p"
      by (simp only: gi_exact_value_compose_def pp_e_closed_den_def pp_identity_operator_def
        pp_e_eval.simps Lambda_app[OF pm] extend_env.simps involutive[OF pm])
  qed
qed

theorem gi_M5_rebuilt_involution_is_group_member:
  assumes involutive: "\<And>p. Elem p (pp_e_domain Prop) \<Longrightarrow> K \<acute> (K \<acute> p) = p"
  shows "pp_e_holds (pp_e_eval (gi_M5_rebuilt_constants k K) (extend_env K \<rho>) (pp_group_member (Var 0))) []"
proof -
  have pure: "gi_basis_pure (gi_M5_expanded_basis k K) gb_unary [] K" by (rule gi_M5_rebuilt_K_pure)
  have identity: "Elem (pp_e_closed_den pp_identity_operator) (pp_e_domain gb_unary)"
    by (rule pp_e_closed_den_in_domain[OF typed_pp_identity_operator[unfolded pp_unary_ty_def]])
  have square: "gi_exact_value_compose K K = pp_e_closed_den pp_identity_operator"
    by (rule gi_M5_self_compose_identity[OF involutive])
  have inverse: "pp_e_eqv gb_unary [] (gi_exact_value_compose K K) (pp_e_closed_den pp_identity_operator)"
    by (simp only: square; rule pp_e_eqv_reflexive[OF identity])
  show ?thesis by (simp only: gi_M5_rebuilt_group_member_value[OF K_typed];
    use pure K_typed inverse in blast)
qed

theorem gi_M5_rebuilt_TU_implies_uniform:
  assumes involutive: "\<And>p. Elem p (pp_e_domain Prop) \<Longrightarrow> K \<acute> (K \<acute> p) = p"
    and truth: "pp_e_holds (pp_e_eval (gi_M5_rebuilt_constants k K) \<rho> pp_TU) []"
  shows "(\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow> (pp_e_holds (K \<acute> p) [] \<longleftrightarrow> pp_e_holds p []))
    \<or> (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow> (pp_e_holds (K \<acute> p) [] \<longleftrightarrow> \<not> pp_e_holds p []))"
proof -
  have group: "pp_e_holds (pp_e_eval (gi_M5_rebuilt_constants k K) (extend_env K \<rho>) (pp_group_member (Var 0))) []"
    by (rule gi_M5_rebuilt_involution_is_group_member[OF involutive])
  have conditional:
    "\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      pp_e_holds (pp_e_eval (gi_M5_rebuilt_constants k K) (extend_env X \<rho>) (pp_group_member (Var 0))) [] \<longrightarrow>
      pp_e_holds (pp_e_eval (gi_M5_rebuilt_constants k K) (extend_env X \<rho>) (pp_truth_preserving (Var 0))) [] \<or>
      pp_e_holds (pp_e_eval (gi_M5_rebuilt_constants k K) (extend_env X \<rho>) (pp_truth_flipping (Var 0))) []"
    using truth by (simp only: pp_TU_def pp_unary_ty_def pp_e_eval_Forall_holds pp_e_eval_Imp_holds pp_e_eval_Disj_holds)
  have alternatives:
    "pp_e_holds (pp_e_eval (gi_M5_rebuilt_constants k K) (extend_env K \<rho>) (pp_truth_preserving (Var 0))) [] \<or>
      pp_e_holds (pp_e_eval (gi_M5_rebuilt_constants k K) (extend_env K \<rho>) (pp_truth_flipping (Var 0))) []"
    using conditional K_typed group by blast
  show ?thesis using alternatives by (simp only: gi_M5_truth_preserving_value gi_M5_truth_flipping_value)
qed

end

section \<open>A root counterexample to the source and translated TU formulas\<close>

theorem gi_exact_M5_rebuilt_TU_false_at_root:
  "\<not> pp_e_holds (pp_e_eval (gi_M5_exotic_constants R) \<rho> pp_TU) []"
proof
  assume truth: "pp_e_holds (pp_e_eval (gi_M5_exotic_constants R) \<rho> pp_TU) []"
  interpret M: gi_exact_expanded_stock gi_M5_exotic_name "gi_exact_M5_exotic R"
    by (rule gi_exact_M5_exotic_expanded_stock)
  have involutive: "gi_exact_M5_exotic R \<acute> (gi_exact_M5_exotic R \<acute> p) = p"
    if "Elem p (pp_e_domain Prop)" for p
    by (rule gi_exact_M5_exotic_involution[OF that])
  have alternatives:
    "(\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
        (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> pp_e_holds p [])) \<or>
      (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
        (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> \<not> pp_e_holds p []))"
    by (rule M.gi_M5_rebuilt_TU_implies_uniform[OF involutive truth])
  show False using alternatives gi_exact_M5_exotic_not_truth_uniform[of R] by blast
qed

lemma gi_M5_TU_vocabulary:
  "consts_of pp_TU \<subseteq> {pp_pure_name, pp_fun_name}"
  by (simp add: pp_TU_def pp_group_member_def pp_reversible_def pp_compose_def pp_identity_operator_def
    pp_truth_preserving_def pp_truth_flipping_def pp_pure_def pp_Pure_def shift_def consts_of_rename)

theorem gi_exact_M5_native_TU_false_at_root:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap"
    and typed: "book_env_typed gi_exact_domain G g"
  shows "\<not> gi_exact_valuation [] (gi_exact_goodman_denote (gi_M5_exotic_constants R) G g
    (gi_to_book G [] cmap pp_TU))"
proof -
  have constants: "pp_e_constants (gi_M5_exotic_constants R)"
    by (rule gi_exact_expanded_stock.gi_M5_rebuilt_constants_locale[OF gi_exact_M5_exotic_expanded_stock])
  have denotation: "gi_exact_goodman_denote (gi_M5_exotic_constants R) G g (gi_to_book G [] cmap pp_TU) =
    pp_e_eval (gi_M5_exotic_constants R) pp_e_closed_env pp_TU"
    by (rule pp_e_constants.gi_exact_goodman_closed_denotation_translation[
      OF constants rich typed_pp_TU typed names gi_M5_TU_vocabulary])
  show ?thesis by (simp only: denotation gi_exact_valuation_def; rule gi_exact_M5_rebuilt_TU_false_at_root)
qed

corollary gi_exact_M5_native_TU_not_global:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap"
  shows "\<not> gi_exact_goodman_global_valid (gi_M5_exotic_constants R) G (gi_to_book G [] cmap pp_TU)"
proof
  assume global: "gi_exact_goodman_global_valid (gi_M5_exotic_constants R) G (gi_to_book G [] cmap pp_TU)"
  have at_root: "gi_exact_valuation [] (gi_exact_goodman_denote (gi_M5_exotic_constants R) G
    (gi_exact_default_assignment G) (gi_to_book G [] cmap pp_TU))"
    using global gi_exact_default_assignment_typed[where G=G]
    unfolding gi_exact_goodman_global_valid_iff by blast
  have not_at_root: "\<not> gi_exact_valuation [] (gi_exact_goodman_denote (gi_M5_exotic_constants R) G
    (gi_exact_default_assignment G) (gi_to_book G [] cmap pp_TU))"
    by (rule gi_exact_M5_native_TU_false_at_root[OF rich names gi_exact_default_assignment_typed])
  show False by (rule notE[OF not_at_root at_root])
qed

theorem gi_M5_TU_not_derivable_from_QLN_background:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap"
  shows "\<not> goodman_book_proves gb_signature G (gi_native_QLN_background G) (gi_to_book G [] cmap pp_TU)"
proof
  assume derivation: "goodman_book_proves gb_signature G (gi_native_QLN_background G) (gi_to_book G [] cmap pp_TU)"
  have constants: "pp_e_constants (gi_M5_exotic_constants {})"
    by (rule gi_exact_expanded_stock.gi_M5_rebuilt_constants_locale[OF gi_exact_M5_exotic_expanded_stock])
  have global: "gi_exact_goodman_global_valid (gi_M5_exotic_constants {}) G (gi_to_book G [] cmap pp_TU)"
    by (rule pp_e_constants.gi_exact_goodman_extension_global_sound[OF constants rich derivation];
      rule gi_exact_M5_rebuilt_QLN_model[OF rich]; assumption)
  show False by (rule notE[OF gi_exact_M5_native_TU_not_global[OF rich names] global])
qed

text \<open>
  This now evaluates the actual TU formula, using the pure self-inverse K
  as its quantified witness. The root counterexample is in the fully rebuilt
  exact interpretation and is transferred to the actual native axiom-extension
  predicate. The conclusion is nonderivability of translated TU from the
  explicit no-PP zeroary/unary QLN background. No Persistence schema is added,
  and this is not a countermodel to the background plus PP. Root falsity is
  not asserted at every world. Inv and WI require their own further bridge.
\<close>

end
