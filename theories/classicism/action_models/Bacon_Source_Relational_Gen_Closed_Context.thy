theory Bacon_Source_Relational_Gen_Closed_Context
  imports Bacon_Source_Relational_A2_MP_Environment_Syntax Bacon_Source_Relational_Universal_Proof_Basics
begin

section \<open>Evaluate one closed operator inside the exact Gen context\<close>

lemma paper_R_Gen_environment_evaluation:
  assumes fresh: "x \<notin> set (ns @ [u])"
  shows "paper_R_environment_subst (Map.empty(x := Some K))
      (named_lam_vec ns (named_paper_all \<sigma> (NLam u (named_app_vec (NVar x) (map NVar (ns @ [u])))))) =
    named_lam_vec ns (named_paper_all \<sigma> (NLam u (named_app_vec K (map NVar (ns @ [u])))))"
proof -
  let ?r = "Map.empty(x := Some K)"
  have inactive: "?r n = None" if "n \<in> set (ns @ [u])" for n using fresh that by auto
  have inactive_ns: "?r n = None" if "n \<in> set ns" for n by (rule inactive; use that in simp)
  have at_u: "?r u = None" by (rule inactive; simp)
  have deletion: "?r(u := None) = ?r" by (rule ext; use fresh in auto)
  have arguments: "map (paper_R_environment_subst ?r) (map NVar (ns @ [u])) = map NVar (ns @ [u])"
    by (rule paper_R_environment_vector_variables[OF inactive])
  show ?thesis by (simp only: paper_R_environment_lam_vec_inactive[OF inactive_ns]
    named_paper_all_def paper_R_environment_subst.simps deletion paper_R_environment_app_vec arguments; simp)
qed

lemma paper_R_all_vector_application_language:
  assumes head: "paper_R_in_language \<Sigma> G K (paper_type_vector (map G (ns @ [u])) Prop)"
    and binders: "list_all paper_R_type (map G ns)" and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_R_in_language \<Sigma> G
    (named_lam_vec ns (named_paper_all \<sigma> (NLam u (named_app_vec K (map NVar (ns @ [u]))))))
    (paper_type_vector (map G ns) Prop)"
proof -
  have combined: "list_all paper_R_type (map G (ns @ [u]))" using binders rt by (simp add: variable)
  have arguments: "list_all2 (\<lambda>A \<rho>. paper_R_in_language \<Sigma> G A \<rho>)
    (map NVar (ns @ [u])) (map G (ns @ [u]))"
    by (rule paper_R_named_vector_variables_language[OF combined])
  have body: "paper_R_in_language \<Sigma> G (named_app_vec K (map NVar (ns @ [u]))) Prop"
    by (rule paper_R_named_app_vec_language[OF arguments head])
  show ?thesis by (rule paper_R_named_lam_vec_prop_language[
    OF paper_R_named_all_binder_language[OF body variable rt] binders])
qed

section \<open>Replace only closed premise abstractions under the quantifier\<close>

text \<open>
  For closed K,T of type type(v⃗u)→t, K=T permits replacement
  in λv⃗.∀u.(Xv⃗u). Choose X at a fresh coordinate outside
  v⃗u and apply the checked closed-payload environment-update theorem.
  Its exact raw environment equations give the displayed conclusion.
  Source: the central IH replacement in Appendix A.2's Gen case, p.66.
  This is not a general abstraction congruence rule; closedness and the
  fresh coordinate are explicit. Repeated requested binders are allowed.
\<close>

theorem paper_R_closed_forall_vector_transport:
  assumes rich: "paper_R_rich G"
    and first: "K \<in> paper_R_closed_terms \<Sigma> G (paper_type_vector (map G (ns @ [u])) Prop)"
    and second: "T \<in> paper_R_closed_terms \<Sigma> G (paper_type_vector (map G (ns @ [u])) Prop)"
    and binders: "list_all paper_R_type (map G ns)" and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>"
    and equality: "paper_R_named_derivable \<Sigma> G S
      (named_paper_eq (paper_type_vector (map G (ns @ [u])) Prop) K T)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns (named_paper_all \<sigma> (NLam u (named_app_vec K (map NVar (ns @ [u]))))))
    (named_lam_vec ns (named_paper_all \<sigma> (NLam u (named_app_vec T (map NVar (ns @ [u])))))))"
proof -
  let ?\<kappa> = "paper_type_vector (map G (ns @ [u])) Prop"
  let ?\<tau> = "paper_type_vector (map G ns) Prop"
  have kr: "paper_R_type ?\<kappa>" by (rule paper_R_result_type[OF paper_R_closed_terms_type[OF first]])
  obtain x where xt: "G x = ?\<kappa>" and fresh: "x \<notin> set (ns @ [u])"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>="?\<kappa>" and S="set (ns @ [u])", OF rich kr finite_set])
  let ?Template = "named_lam_vec ns (named_paper_all \<sigma>
    (NLam u (named_app_vec (NVar x) (map NVar (ns @ [u])))))"
  have vx: "paper_R_in_language \<Sigma> G (NVar x) ?\<kappa>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=x, OF xt kr])
  have template: "paper_R_in_language \<Sigma> G ?Template ?\<tau>"
    by (rule paper_R_all_vector_application_language[OF vx binders variable rt])
  have empty_typed: "paper_R_closed_term_assignment \<Sigma> G Map.empty"
    by (simp add: paper_R_closed_term_assignment_def)
  have kx: "K \<in> paper_R_closed_terms \<Sigma> G (G x)" by (simp only: xt; rule first)
  have tx: "T \<in> paper_R_closed_terms \<Sigma> G (G x)" by (simp only: xt; rule second)
  have coordinate: "paper_R_named_derivable \<Sigma> G S (named_paper_eq (G x) K T)"
    by (simp only: xt; rule equality)
  have changed: "paper_R_named_derivable \<Sigma> G S (named_paper_eq ?\<tau>
    (paper_R_environment_subst (Map.empty(x := Some K)) ?Template)
    (paper_R_environment_subst (Map.empty(x := Some T)) ?Template))"
    by (rule paper_R_environment_subst_update_identity[OF rich template empty_typed kx tx coordinate])
  show ?thesis using changed by (simp only: paper_R_Gen_environment_evaluation[OF fresh])
qed

end
