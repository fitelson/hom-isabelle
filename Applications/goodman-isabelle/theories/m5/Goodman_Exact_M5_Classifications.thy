theory Goodman_Exact_M5_Classifications
  imports Goodman_Exact_M5_TU_Refutation
    Goodman_Integration_T6.Goodman_T6_Restricted_Signature
begin

section \<open>Inv at the root would make the exotic operator truth-uniform\<close>

lemma gi_M5_negation_value:
  "pp_e_eval C \<rho> pp_negation_operator = pp_e_closed_den pp_negation_operator"
  by (simp add: pp_negation_operator_def pp_e_closed_den_def)

lemma gi_M5_identity_application:
  "Elem p (pp_e_domain Prop) \<Longrightarrow> pp_e_closed_den pp_identity_operator \<acute> p = p"
  by (simp only: pp_e_closed_den_def pp_identity_operator_def pp_e_eval.simps Lambda_app extend_env.simps)

lemma gi_M5_negation_application_truth:
  assumes pm: "Elem p (pp_e_domain Prop)"
  shows "pp_e_holds (pp_e_closed_den pp_negation_operator \<acute> p) w \<longleftrightarrow> \<not> pp_e_holds p w"
proof -
  have beta: "pp_e_closed_den pp_negation_operator \<acute> p =
    pp_e_eval pp_e_default_constants (extend_env p pp_e_closed_env) (Neg (Var 0))"
    by (simp only: pp_e_closed_den_def pp_negation_operator_def pp_e_eval.simps(4) Lambda_app[OF pm])
  show ?thesis by (simp only: beta pp_e_eval_Neg_holds pp_e_eval.simps(1) extend_env.simps)
qed

lemma gi_M5_identity_at_root_implies_preserving:
  assumes related: "pp_e_eqv gb_unary [] X (pp_e_closed_den pp_identity_operator)"
  shows "\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow> (pp_e_holds (X \<acute> p) [] \<longleftrightarrow> pp_e_holds p [])"
proof (intro allI impI)
  fix p assume pm: "Elem p (pp_e_domain Prop)"
  have refl: "pp_e_eqv Prop [] p p" by (rule pp_e_eqv_reflexive[OF pm])
  have applications: "pp_e_eqv Prop [] (X \<acute> p) (pp_e_closed_den pp_identity_operator \<acute> p)"
    by (rule pp_e_app_respects[OF related pm pm refl])
  have truth: "pp_e_holds (X \<acute> p) [] \<longleftrightarrow> pp_e_holds (pp_e_closed_den pp_identity_operator \<acute> p) []"
    using pp_e_prop_eqv_at[OF applications, where v="[]"] by simp
  show "pp_e_holds (X \<acute> p) [] \<longleftrightarrow> pp_e_holds p []"
    using truth by (simp only: gi_M5_identity_application[OF pm])
qed

lemma gi_M5_negation_at_root_implies_flipping:
  assumes related: "pp_e_eqv gb_unary [] X (pp_e_closed_den pp_negation_operator)"
  shows "\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow> (pp_e_holds (X \<acute> p) [] \<longleftrightarrow> \<not> pp_e_holds p [])"
proof (intro allI impI)
  fix p assume pm: "Elem p (pp_e_domain Prop)"
  have refl: "pp_e_eqv Prop [] p p" by (rule pp_e_eqv_reflexive[OF pm])
  have applications: "pp_e_eqv Prop [] (X \<acute> p) (pp_e_closed_den pp_negation_operator \<acute> p)"
    by (rule pp_e_app_respects[OF related pm pm refl])
  have truth: "pp_e_holds (X \<acute> p) [] \<longleftrightarrow> pp_e_holds (pp_e_closed_den pp_negation_operator \<acute> p) []"
    using pp_e_prop_eqv_at[OF applications, where v="[]"] by simp
  show "pp_e_holds (X \<acute> p) [] \<longleftrightarrow> \<not> pp_e_holds p []"
    using truth by (simp only: gi_M5_negation_application_truth[OF pm])
qed

lemma gi_M5_Inv_root_classifies_group_member:
  assumes truth: "pp_e_holds (pp_e_eval C \<rho> pp_Inv) []"
    and xm: "Elem X (pp_e_domain gb_unary)"
    and group: "pp_e_holds (pp_e_eval C (extend_env X \<rho>) (pp_group_member (Var 0))) []"
  shows "pp_e_eqv gb_unary [] X (pp_e_closed_den pp_identity_operator) \<or>
    pp_e_eqv gb_unary [] X (pp_e_closed_den pp_negation_operator)"
  using truth xm group
  by (simp only: pp_Inv_def pp_unary_ty_def pp_e_eval_Forall_holds pp_e_eval_Conj_holds
    pp_e_eval_Imp_holds pp_e_eval_Disj_holds pp_e_eval_Eq_holds pp_e_eval.simps(1)
    extend_env.simps gi_M5_identity_value gi_M5_negation_value; blast)

theorem gi_exact_M5_rebuilt_Inv_false_at_root:
  "\<not> pp_e_holds (pp_e_eval (gi_M5_exotic_constants R) \<rho> pp_Inv) []"
proof
  assume truth: "pp_e_holds (pp_e_eval (gi_M5_exotic_constants R) \<rho> pp_Inv) []"
  interpret M: gi_exact_expanded_stock gi_M5_exotic_name "gi_exact_M5_exotic R"
    by (rule gi_exact_M5_exotic_expanded_stock)
  have involutive: "gi_exact_M5_exotic R \<acute> (gi_exact_M5_exotic R \<acute> p) = p"
    if "Elem p (pp_e_domain Prop)" for p by (rule gi_exact_M5_exotic_involution[OF that])
  have group: "pp_e_holds (pp_e_eval (gi_M5_exotic_constants R) (extend_env (gi_exact_M5_exotic R) \<rho>)
    (pp_group_member (Var 0))) []"
    by (rule M.gi_M5_rebuilt_involution_is_group_member[OF involutive])
  have classified: "pp_e_eqv gb_unary [] (gi_exact_M5_exotic R) (pp_e_closed_den pp_identity_operator) \<or>
    pp_e_eqv gb_unary [] (gi_exact_M5_exotic R) (pp_e_closed_den pp_negation_operator)"
    by (rule gi_M5_Inv_root_classifies_group_member[OF truth gi_exact_M5_exotic_member group])
  have uniform:
    "(\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
      (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> pp_e_holds p [])) \<or>
    (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
      (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> \<not> pp_e_holds p []))"
    using classified gi_M5_identity_at_root_implies_preserving[where X="gi_exact_M5_exotic R"]
      gi_M5_negation_at_root_implies_flipping[where X="gi_exact_M5_exotic R"] by blast
  show False using uniform gi_exact_M5_exotic_not_truth_uniform[of R] by blast
qed

lemma gi_M5_Inv_vocabulary:
  "consts_of pp_Inv \<subseteq> {pp_pure_name, pp_fun_name}"
  by (simp add: pp_Inv_def pp_group_member_def pp_reversible_def pp_compose_def
    pp_identity_operator_def pp_negation_operator_def pp_pure_def pp_Pure_def shift_def consts_of_rename)

theorem gi_exact_M5_native_Inv_false_at_root:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap" and typed: "book_env_typed gi_exact_domain G g"
  shows "\<not> gi_exact_valuation [] (gi_exact_goodman_denote (gi_M5_exotic_constants R) G g
    (gi_to_book G [] cmap pp_Inv))"
proof -
  have constants: "pp_e_constants (gi_M5_exotic_constants R)"
    by (rule gi_exact_expanded_stock.gi_M5_rebuilt_constants_locale[OF gi_exact_M5_exotic_expanded_stock])
  have denotation: "gi_exact_goodman_denote (gi_M5_exotic_constants R) G g (gi_to_book G [] cmap pp_Inv) =
    pp_e_eval (gi_M5_exotic_constants R) pp_e_closed_env pp_Inv"
    by (rule pp_e_constants.gi_exact_goodman_closed_denotation_translation[
      OF constants rich typed_pp_Inv typed names gi_M5_Inv_vocabulary])
  show ?thesis by (simp only: denotation gi_exact_valuation_def; rule gi_exact_M5_rebuilt_Inv_false_at_root)
qed

corollary gi_exact_M5_native_Inv_not_global:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap"
  shows "\<not> gi_exact_goodman_global_valid (gi_M5_exotic_constants R) G (gi_to_book G [] cmap pp_Inv)"
proof
  assume global: "gi_exact_goodman_global_valid (gi_M5_exotic_constants R) G (gi_to_book G [] cmap pp_Inv)"
  have at_root: "gi_exact_valuation [] (gi_exact_goodman_denote (gi_M5_exotic_constants R) G
    (gi_exact_default_assignment G) (gi_to_book G [] cmap pp_Inv))"
    using global gi_exact_default_assignment_typed[where G=G]
    unfolding gi_exact_goodman_global_valid_iff by blast
  have not_at_root: "\<not> gi_exact_valuation [] (gi_exact_goodman_denote (gi_M5_exotic_constants R) G
    (gi_exact_default_assignment G) (gi_to_book G [] cmap pp_Inv))"
    by (rule gi_exact_M5_native_Inv_false_at_root[OF rich names gi_exact_default_assignment_typed])
  show False by (rule notE[OF not_at_root at_root])
qed

theorem gi_M5_Inv_not_derivable_from_QLN_background:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap"
  shows "\<not> goodman_book_proves gb_signature G (gi_native_QLN_background G) (gi_to_book G [] cmap pp_Inv)"
proof
  assume derivation: "goodman_book_proves gb_signature G (gi_native_QLN_background G) (gi_to_book G [] cmap pp_Inv)"
  have constants: "pp_e_constants (gi_M5_exotic_constants {})"
    by (rule gi_exact_expanded_stock.gi_M5_rebuilt_constants_locale[OF gi_exact_M5_exotic_expanded_stock])
  have global: "gi_exact_goodman_global_valid (gi_M5_exotic_constants {}) G (gi_to_book G [] cmap pp_Inv)"
    by (rule pp_e_constants.gi_exact_goodman_extension_global_sound[OF constants rich derivation];
      rule gi_exact_M5_rebuilt_QLN_model[OF rich]; assumption)
  show False by (rule notE[OF gi_exact_M5_native_Inv_not_global[OF rich names] global])
qed

section \<open>WI implies TU as a theorem-level axiom-extension consequence\<close>

theorem gi_M5_WI_entails_TU:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap"
  shows "goodman_book_proves gb_signature G {gi_to_book G [] cmap pp_WI} (gi_to_book G [] cmap pp_TU)"
proof -
  have source: "[] ; {pp_WI} \<turnstile>\<^sub>CEV\<^sup>+ pp_TU"
    by (rule CEV_axiom_WI_implies_TU; simp)
  have closed: "\<And>A. A \<in> {pp_WI} \<Longrightarrow> [] \<turnstile> A : Prop"
    by (auto intro: typed_pp_WI)
  have admitted: "\<And>A. A \<in> {pp_WI} \<Longrightarrow> gi_constants_admitted cmap gb_signature A"
    by (auto intro: gi_WI_admitted[OF names])
  have transfer: "goodman_book_proves gb_signature G (image (gi_to_book G [] cmap) {pp_WI})
    (gi_to_book G [] cmap pp_TU)"
    by (rule gi_CEV_axiom_preservation_in_signature[OF rich source closed _ _ admitted gi_TU_admitted[OF names]]; simp)
  show ?thesis using transfer by (simp only: image_insert image_empty)
qed

theorem gi_M5_WI_not_derivable_from_QLN_background:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap"
  shows "\<not> goodman_book_proves gb_signature G (gi_native_QLN_background G) (gi_to_book G [] cmap pp_WI)"
proof
  assume derivation: "goodman_book_proves gb_signature G (gi_native_QLN_background G) (gi_to_book G [] cmap pp_WI)"
  have tu: "goodman_book_proves gb_signature G (gi_native_QLN_background G) (gi_to_book G [] cmap pp_TU)"
    by (rule goodman_book_cut[OF gi_M5_WI_entails_TU[OF rich names]]; use derivation in auto)
  show False by (rule notE[OF gi_M5_TU_not_derivable_from_QLN_background[OF rich names] tu])
qed

theorem gi_exact_M5_native_WI_not_global:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap"
  shows "\<not> gi_exact_goodman_global_valid (gi_M5_exotic_constants R) G (gi_to_book G [] cmap pp_WI)"
proof
  assume wi: "gi_exact_goodman_global_valid (gi_M5_exotic_constants R) G (gi_to_book G [] cmap pp_WI)"
  have constants: "pp_e_constants (gi_M5_exotic_constants R)"
    by (rule gi_exact_expanded_stock.gi_M5_rebuilt_constants_locale[OF gi_exact_M5_exotic_expanded_stock])
  have tu: "gi_exact_goodman_global_valid (gi_M5_exotic_constants R) G (gi_to_book G [] cmap pp_TU)"
    by (rule pp_e_constants.gi_exact_goodman_extension_global_sound[OF constants rich gi_M5_WI_entails_TU[OF rich names]];
      use wi in auto)
  show False by (rule notE[OF gi_exact_M5_native_TU_not_global[OF rich names] tu])
qed

text \<open>
  Inv is false at the root of the actual rebuilt exact interpretation:
  its classification would make the pure involution uniformly preserving
  or flipping, contrary to the checked certificate. WI's singleton-axiom
  consequence TU is transferred syntactically and used through native cut.
  This establishes WI nonderivability and failure of global validity, not
  a claim of root falsity from a merely root-true WI premise.

  Together with the preceding TU theorem, all three nonderivability results
  concern the explicit no-PP zeroary/unary QLN background. No Persistence,
  Purity of Fun, PP, or unproved implication Inv⇒TU is assumed. Statements
  remain about translated classification formulas; independent native
  definitions of those formulas are a separate syntactic identification.
\<close>

end
