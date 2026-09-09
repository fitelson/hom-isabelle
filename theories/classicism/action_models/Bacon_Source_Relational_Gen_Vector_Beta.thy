theory Bacon_Source_Relational_Gen_Vector_Beta
  imports Bacon_Source_Relational_Gen_Closed_Context Bacon_Source_Relational_Conversion_Congruence
begin

section \<open>Self-β under the explicit universal and outer vector\<close>

theorem paper_R_named_H_all_vector_self_identity:
  fixes A :: "'c paper_named_term"
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G A Prop"
    and binders: "list_all paper_R_type (map G ns)" and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_R_named_H \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns (named_paper_all \<sigma> (NLam u
      (named_app_vec (named_lam_vec (ns @ [u]) A) (map NVar (ns @ [u]))))))
    (named_lam_vec ns (named_paper_all \<sigma> (NLam u A))))"
proof -
  let ?K = "named_lam_vec (ns @ [u]) A"
  let ?B = "named_app_vec ?K (map NVar (ns @ [u]))"
  have ur: "paper_R_type (G u)" by (simp only: variable; rule rt)
  have combined: "list_all paper_R_type (map G (ns @ [u]))" using binders rt by (simp add: variable)
  have body: "paper_R_raw_beta_eta G Prop ?B A"
    by (rule paper_R_named_lam_vec_self_beta[OF language combined]; simp)
  have abstraction: "paper_R_raw_beta_eta G (Arr (G u) Prop) (NLam u ?B) (NLam u A)"
    by (rule paper_R_raw_beta_eta_Lam[OF body ur]; simp)
  have predicates: "paper_R_raw_beta_eta G (Arr \<sigma> Prop) (NLam u ?B) (NLam u A)"
    using abstraction by (simp only: variable)
  have quantifier: "paper_R_has_type G (NLogical (SAll \<sigma>) :: 'c paper_named_term) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_R_has_type.Logical[where G=G and l="SAll \<sigma>"] rt by simp
  have quantified: "paper_R_raw_beta_eta G Prop (named_paper_all \<sigma> (NLam u ?B)) (named_paper_all \<sigma> (NLam u A))"
    unfolding named_paper_all_def by (rule paper_R_raw_beta_eta_App_right[OF predicates quantifier])
  have conversion: "paper_R_raw_beta_eta G (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns (named_paper_all \<sigma> (NLam u ?B)))
    (named_lam_vec ns (named_paper_all \<sigma> (NLam u A)))"
    by (rule paper_R_raw_beta_eta_lam_vec[OF quantified binders]; simp)
  have kl: "paper_R_in_language \<Sigma> G ?K (paper_type_vector (map G (ns @ [u])) Prop)"
    by (rule paper_R_named_lam_vec_prop_language[OF language combined])
  have left: "paper_R_in_language \<Sigma> G (named_lam_vec ns (named_paper_all \<sigma> (NLam u ?B)))
    (paper_type_vector (map G ns) Prop)"
    by (rule paper_R_all_vector_application_language[OF kl binders variable rt])
  have right: "paper_R_in_language \<Sigma> G (named_lam_vec ns (named_paper_all \<sigma> (NLam u A)))
    (paper_type_vector (map G ns) Prop)"
    by (rule paper_R_named_lam_vec_prop_language[OF paper_R_named_all_binder_language[OF language variable rt] binders])
  show ?thesis by (rule paper_R_named_H_raw_conversion_identity[OF rich conversion left right])
qed

text \<open>
  Every β intermediate remains R-typed. The outer prefix may repeat
  u or other names: the same-variable self-application proof preserves
  the literal shadowing behavior. Source: Appendix A.2, p.66.
  This proof has no C-rule or semantic premise.
\<close>

end
