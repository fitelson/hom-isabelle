theory Goodman_T9_Native_Purity
  imports Goodman_T9_Selector_Terms
begin

section \<open>Root-pure values obtained from the actual native axioms\<close>

definition gi_T9_root_pure where
  "gi_T9_root_pure C \<sigma> = {x. Elem x (pp_e_domain \<sigma>) \<and> gi_M1_exact_Pure C \<sigma> [] x}"

locale gi_T9_native_purity = pp_e_constants C for C +
  fixes G :: sgcontext
  assumes rich: "sg_rich G"
    and core_valid: "\<And>A. A \<in> gb_T6_core G \<Longrightarrow> gi_exact_goodman_global_valid C G A"
begin

lemma gi_T9_core_at_root:
  "A \<in> gb_T6_core G \<Longrightarrow>
    gi_exact_valuation [] (gi_exact_goodman_denote C G (gi_exact_default_assignment G) A)"
  using core_valid gi_exact_default_assignment_typed[where G=G]
  unfolding gi_exact_goodman_global_valid_iff by blast

lemma gi_T9_closed_logical_value_pure:
  assumes mt: "[] \<turnstile> M : \<sigma>" and logical: "pp_logical_vocabulary M"
  shows "pp_e_closed_den M \<in> gi_T9_root_pure C \<sigma>"
proof -
  obtain A where al: "gb_closed_logical G \<sigma> A"
    and denotation: "gi_exact_native_closed_den G A = pp_e_closed_den M"
    using gi_old_closed_logical_native_witness[OF rich mt logical] by blast
  have member: "gb_pure \<sigma> A \<in> gb_T6_core G"
    using al unfolding gb_T6_core_def gb_purity_schema_def by blast
  have truth: "gi_M1_exact_Pure C \<sigma> []
      (gi_exact_goodman_denote C G (gi_exact_default_assignment G) A)"
    using gi_T9_core_at_root[OF member] by (simp only: gi_M1_native_pure_clause)
  have actual: "gi_exact_goodman_denote C G (gi_exact_default_assignment G) A = pp_e_closed_den M"
    by (simp only: gi_exact_native_closed_den_independent[OF al] denotation)
  show ?thesis unfolding gi_T9_root_pure_def
    using pp_e_closed_den_in_domain[OF mt] truth actual by simp
qed

lemma gi_T9_closed_source_axiom_at_root:
  assumes mt: "[] \<turnstile> M : Prop" and names: "gi_goodman_names k"
    and vocabulary: "consts_of M \<subseteq> {pp_pure_name, pp_fun_name}"
    and member: "gi_to_book G [] k M \<in> gb_T6_core G"
  shows "pp_e_holds (pp_e_eval C pp_e_closed_env M) []"
  using gi_T9_core_at_root[OF member]
  by (simp only: gi_exact_valuation_def
    gi_exact_goodman_closed_denotation_translation[OF rich mt gi_exact_default_assignment_typed names vocabulary])

lemma gi_T9_root_application_closed:
  assumes f: "f \<in> gi_T9_root_pure C (Arr \<sigma> \<tau>)" and x: "x \<in> gi_T9_root_pure C \<sigma>"
  shows "f \<acute> x \<in> gi_T9_root_pure C \<tau>"
proof -
  have fm: "Elem f (pp_e_domain (Arr \<sigma> \<tau>))" and fp: "gi_M1_exact_Pure C (Arr \<sigma> \<tau>) [] f"
    using f unfolding gi_T9_root_pure_def by auto
  have xm: "Elem x (pp_e_domain \<sigma>)" and xp: "gi_M1_exact_Pure C \<sigma> [] x"
    using x unfolding gi_T9_root_pure_def by auto
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of (pp_application_closure \<sigma> \<tau>) \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_application_closure_def pp_pure_def pp_Pure_def)
  have member: "gi_to_book G [] k (pp_application_closure \<sigma> \<tau>) \<in> gb_T6_core G"
    by (simp only: gi_application_translation[OF names];
      auto simp: gb_T6_core_def gb_application_schema_def)
  have truth: "pp_e_holds (pp_e_eval C pp_e_closed_env (pp_application_closure \<sigma> \<tau>)) []"
    by (rule gi_T9_closed_source_axiom_at_root[OF typed_pp_application_closure names vocabulary member])
  have pure: "gi_M1_exact_Pure C \<tau> [] (f \<acute> x)"
    using truth fm xm fp xp
    unfolding pp_application_closure_def pp_pure_def pp_Pure_def gi_M1_exact_Pure_def
    by (simp only: pp_e_eval_Forall_holds pp_e_eval_Imp_holds pp_e_eval_Conj_holds
      pp_e_eval.simps(1,2,3) extend_env.simps One_nat_def; blast)
  show ?thesis unfolding gi_T9_root_pure_def using pure pp_e_app_closed[OF fm xm] by simp
qed

lemma gi_T9_root_Pure_pure:
  "C pp_pure_name gi_T9_pred \<in> gi_T9_root_pure C gi_T9_pred"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of pp_target_PP \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_target_PP_def pp_purity_of_pure_def pp_pure_def pp_Pure_def)
  have member: "gi_to_book G [] k pp_target_PP \<in> gb_T6_core G"
    by (simp add: gi_PP_translation[OF names] gb_T6_core_def)
  have truth: "pp_e_holds (pp_e_eval C pp_e_closed_env pp_target_PP) []"
    by (rule gi_T9_closed_source_axiom_at_root[OF typed_pp_target_PP names vocabulary member])
  show ?thesis using truth C_typed[of pp_pure_name gi_T9_pred]
    by (simp add: gi_T9_root_pure_def gi_M1_exact_Pure_def pp_target_PP_def
      pp_purity_of_pure_def pp_pure_def pp_Pure_def pp_unary_ty_def)
qed

theorem gi_T9_J_value_pure:
  "gi_T9_J_value C \<in> gi_T9_root_pure C gb_unary"
  unfolding gi_T9_J_value_def
  by (rule gi_T9_root_application_closed[
    OF gi_T9_closed_logical_value_pure[OF gi_T9_J_builder_type gi_T9_builders_logical(1)] gi_T9_root_Pure_pure])

theorem gi_T9_lower_value_pure:
  assumes hp: "H \<in> gi_T9_root_pure C gi_T9_pred"
  shows "gi_T9_lower_value C H \<in> gi_T9_root_pure C gb_unary"
proof -
  have builder: "pp_e_closed_den gi_T9_lower_builder \<in> gi_T9_root_pure C gi_T9_lower_type"
    by (rule gi_T9_closed_logical_value_pure[OF gi_T9_lower_builder_type gi_T9_builders_logical(2)])
  have first: "pp_e_closed_den gi_T9_lower_builder \<acute> C pp_pure_name gi_T9_pred \<in>
      gi_T9_root_pure C (Arr gi_T9_pred (Arr gb_unary gb_unary))"
    by (rule gi_T9_root_application_closed[OF builder gi_T9_root_Pure_pure])
  have second: "(pp_e_closed_den gi_T9_lower_builder \<acute> C pp_pure_name gi_T9_pred) \<acute> H \<in>
      gi_T9_root_pure C (Arr gb_unary gb_unary)"
    by (rule gi_T9_root_application_closed[OF first hp])
  show ?thesis unfolding gi_T9_lower_value_def by (rule gi_T9_root_application_closed[OF second gi_T9_J_value_pure])
qed

end

text \<open>
  Root purity of the lowered operator is derived from the actual native
  logical-purity/application/PP package, not assumed as an abstract counting
  premise. The higher-order selector H still has to be supplied by PC.
  This is conditional on the explicitly stated native axiom validity;
  our fixed generic interpretation is not asserted to validate PP.
\<close>

end
