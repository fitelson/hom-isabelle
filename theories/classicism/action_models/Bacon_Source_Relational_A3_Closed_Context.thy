theory Bacon_Source_Relational_A3_Closed_Context
  imports Bacon_Source_Relational_A3_Selector Bacon_Source_Relational_A2_MP_Environment_Syntax
begin

lemma paper_R_A3_environment_evaluation:
  assumes fresh: "x \<notin> set ns" and covered: "named_fv B \<subseteq> set ns"
  shows "paper_R_environment_subst (Map.empty(x := Some K)) (paper_R_A3_vector_context ns B (NVar x)) =
    paper_R_A3_vector_context ns B K"
proof -
  let ?r = "Map.empty(x := Some K)"
  have inactive: "?r n = None" if "n \<in> set ns" for n using fresh that by auto
  have fixed_B: "paper_R_environment_subst ?r B = B"
    by (rule paper_R_environment_inactive_fixed; rule inactive; use covered in blast)
  have arguments: "map (paper_R_environment_subst ?r) (map NVar ns) = map NVar ns"
    by (rule paper_R_environment_vector_variables[OF inactive])
  show ?thesis by (simp only: paper_R_A3_vector_context_def paper_R_environment_lam_vec_inactive[OF inactive]
    paper_R_A3_selector_def named_paper_or_def named_paper_and_def named_paper_not_def
    paper_R_environment_subst.simps fixed_B paper_R_environment_app_vec arguments; simp)
qed

section \<open>Transport the closed biconditional abstraction inside the selector\<close>

text \<open>
  K=T, for closed K,T, permits their replacement in
  λv⃗.((B∧Xv⃗)∨(¬B∧¬Xv⃗)). The coordinate X has
  the vector function type and is fresh for v⃗. FV(B)⊆v⃗
  ensures that the environment leaves B untouched.
  Source: Appendix A.3, p.67. This is a proved closed-payload
  LL/β instance, not general abstraction congruence.
\<close>

theorem paper_R_A3_closed_context_identity:
  assumes rich: "paper_R_rich G" and bl: "paper_R_in_language \<Sigma> G B Prop"
    and binders: "list_all paper_R_type (map G ns)" and covered: "named_fv B \<subseteq> set ns"
    and first: "K \<in> paper_R_closed_terms \<Sigma> G (paper_type_vector (map G ns) Prop)"
    and second: "T \<in> paper_R_closed_terms \<Sigma> G (paper_type_vector (map G ns) Prop)"
    and equality: "paper_R_named_derivable \<Sigma> G S
      (named_paper_eq (paper_type_vector (map G ns) Prop) K T)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq (paper_type_vector (map G ns) Prop)
    (paper_R_A3_vector_context ns B K) (paper_R_A3_vector_context ns B T))"
proof -
  let ?\<tau> = "paper_type_vector (map G ns) Prop"
  have rt: "paper_R_type ?\<tau>" by (rule paper_R_result_type[OF paper_R_closed_terms_type[OF first]])
  obtain x where xt: "G x = ?\<tau>" and fresh: "x \<notin> set ns"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>="?\<tau>" and S="set ns", OF rich rt finite_set])
  have vx: "paper_R_in_language \<Sigma> G (NVar x) ?\<tau>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=x, OF xt rt])
  have template: "paper_R_in_language \<Sigma> G (paper_R_A3_vector_context ns B (NVar x)) ?\<tau>"
    by (rule paper_R_A3_vector_language[OF bl vx binders])
  have empty_typed: "paper_R_closed_term_assignment \<Sigma> G Map.empty"
    by (simp add: paper_R_closed_term_assignment_def)
  have kx: "K \<in> paper_R_closed_terms \<Sigma> G (G x)" by (simp only: xt; rule first)
  have tx: "T \<in> paper_R_closed_terms \<Sigma> G (G x)" by (simp only: xt; rule second)
  have coordinate: "paper_R_named_derivable \<Sigma> G S (named_paper_eq (G x) K T)"
    by (simp only: xt; rule equality)
  have changed: "paper_R_named_derivable \<Sigma> G S (named_paper_eq ?\<tau>
    (paper_R_environment_subst (Map.empty(x := Some K)) (paper_R_A3_vector_context ns B (NVar x)))
    (paper_R_environment_subst (Map.empty(x := Some T)) (paper_R_A3_vector_context ns B (NVar x))))"
    by (rule paper_R_environment_subst_update_identity[OF rich template empty_typed kx tx coordinate])
  show ?thesis using changed by (simp only: paper_R_A3_environment_evaluation[OF fresh covered])
qed

end
