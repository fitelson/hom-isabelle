theory Bacon_Source_Relational_Classicism_A2_Gen_Closed
  imports Bacon_Source_Relational_Gen_Distribution_Proof Bacon_Source_Relational_Gen_Vector_Beta
begin

section \<open>Gen preservation at a prefix closing the premise operators\<close>

text \<open>
  The IH identifies K=λv⃗u.(P→Q) with T=λv⃗u.⊤.
  With both operators closed, replace K by T in λv⃗.∀u.(Xv⃗u).
  Actual self-β connects the two sides to λv⃗.∀u.(P→Q)
  and λv⃗.∀u.⊤. The H distribution certificate supplies the
  Gen conclusion on the first side; H proves ∀u.⊤ on the second.
  Source: Appendix A.2, p.66. No open-identity abstraction,
  Equivalence rule, semantic premise or arbitrary quantifier operation
  is assumed.
\<close>

theorem paper_R_classicism_A2_Gen_closed:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>" and fresh: "u \<notin> named_fv P"
    and binders: "list_all paper_R_type (map G ns)"
    and covered: "named_fv P \<union> named_fv Q \<subseteq> set ns"
    and premise: "paper_R_classicism_proves \<Sigma> G
      (named_paper_eq (paper_type_vector (map G (ns @ [u])) Prop)
        (named_lam_vec (ns @ [u]) (named_paper_imp G P Q))
        (named_lam_vec (ns @ [u]) (paper_R_named_top G)))"
  shows "paper_R_classicism_proves \<Sigma> G
    (named_paper_eq (paper_type_vector (map G ns) Prop)
      (named_lam_vec ns (named_paper_imp G P (named_paper_all \<sigma> (NLam u Q))))
      (named_lam_vec ns (paper_R_named_top G)))"
proof -
  let ?I = "named_paper_imp G P Q"
  let ?R = "named_paper_imp G P (named_paper_all \<sigma> (NLam u Q))"
  let ?D = "named_paper_all \<sigma> (NLam u ?I)"
  let ?AllTop = "named_paper_all \<sigma> (NLam u (paper_R_named_top G))"
  let ?K = "named_lam_vec (ns @ [u]) ?I"
  let ?T = "named_lam_vec (ns @ [u]) (paper_R_named_top G)"
  let ?E = "\<lambda>X. named_lam_vec ns (named_paper_all \<sigma> (NLam u (named_app_vec X (map NVar (ns @ [u])))))"
  let ?\<kappa> = "paper_type_vector (map G (ns @ [u])) Prop"
  let ?\<tau> = "paper_type_vector (map G ns) Prop"
  let ?S = "{A. paper_R_classicism_proves \<Sigma> G A}"
  have combined: "list_all paper_R_type (map G (ns @ [u]))" using binders rt by (simp add: variable)
  have il: "paper_R_in_language \<Sigma> G ?I Prop" by (rule paper_R_named_paper_imp_language[OF rich pl ql])
  have top: "paper_R_in_language \<Sigma> G (paper_R_named_top G) Prop" by (rule paper_R_named_top_language[OF rich])
  have kl: "paper_R_in_language \<Sigma> G ?K ?\<kappa>" by (rule paper_R_named_lam_vec_prop_language[OF il combined])
  have tl: "paper_R_in_language \<Sigma> G ?T ?\<kappa>" by (rule paper_R_named_lam_vec_prop_language[OF top combined])
  have cover_I: "named_fv ?I \<subseteq> set (ns @ [u])" using covered by (auto simp: named_paper_defined_fv)
  have kc: "?K \<in> paper_R_closed_terms \<Sigma> G ?\<kappa>"
    by (rule paper_R_closed_termsI[OF kl named_lam_vec_closed[OF cover_I]])
  have tc: "?T \<in> paper_R_closed_terms \<Sigma> G ?\<kappa>"
    by (rule paper_R_closed_termsI[OF tl]; simp only: named_lam_vec_fv paper_R_named_top_closed; simp)
  have premise_member: "named_paper_eq ?\<kappa> ?K ?T \<in> ?S" using premise by simp
  have premise_local: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<kappa> ?K ?T)"
    by (rule paper_R_named_derivable.Assumption[OF premise_member paper_R_named_identity_language[OF kl tl]])
  have replacement: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> (?E ?K) (?E ?T))"
    by (rule paper_R_closed_forall_vector_transport[OF rich kc tc binders variable rt premise_local])
  have rl: "paper_R_in_language \<Sigma> G ?R Prop"
    by (rule paper_R_named_paper_imp_language[OF rich pl paper_R_named_all_binder_language[OF ql variable rt]])
  have dl: "paper_R_in_language \<Sigma> G ?D Prop" by (rule paper_R_named_all_binder_language[OF il variable rt])
  have atl: "paper_R_in_language \<Sigma> G ?AllTop Prop" by (rule paper_R_named_all_binder_language[OF top variable rt])
  have lr: "paper_R_in_language \<Sigma> G (named_lam_vec ns ?R) ?\<tau>"
    by (rule paper_R_named_lam_vec_prop_language[OF rl binders])
  have ld: "paper_R_in_language \<Sigma> G (named_lam_vec ns ?D) ?\<tau>"
    by (rule paper_R_named_lam_vec_prop_language[OF dl binders])
  have lat: "paper_R_in_language \<Sigma> G (named_lam_vec ns ?AllTop) ?\<tau>"
    by (rule paper_R_named_lam_vec_prop_language[OF atl binders])
  have ltop: "paper_R_in_language \<Sigma> G (named_lam_vec ns (paper_R_named_top G)) ?\<tau>"
    by (rule paper_R_named_lam_vec_prop_language[OF top binders])
  have ek: "paper_R_in_language \<Sigma> G (?E ?K) ?\<tau>" by (rule paper_R_all_vector_application_language[OF kl binders variable rt])
  have et: "paper_R_in_language \<Sigma> G (?E ?T) ?\<tau>" by (rule paper_R_all_vector_application_language[OF tl binders variable rt])
  have distribution: "paper_R_named_H \<Sigma> G (named_paper_iff G ?R ?D)"
    by (rule paper_R_named_H_Gen_distribution[OF rich pl ql variable rt fresh])
  have start_C: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> (named_lam_vec ns ?R) (named_lam_vec ns ?D))"
    by (rule paper_R_classicism_proves.Logical_Equivalence[OF distribution rl dl binders])
  have start_member: "named_paper_eq ?\<tau> (named_lam_vec ns ?R) (named_lam_vec ns ?D) \<in> ?S" using start_C by simp
  have start_local: "paper_R_named_derivable \<Sigma> G ?S
    (named_paper_eq ?\<tau> (named_lam_vec ns ?R) (named_lam_vec ns ?D))"
    by (rule paper_R_named_derivable.Assumption[OF start_member paper_R_named_identity_language[OF lr ld]])
  have first_beta: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> (?E ?K) (named_lam_vec ns ?D))"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_all_vector_self_identity[OF rich il binders variable rt]])
  have reverse_beta: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> (named_lam_vec ns ?D) (?E ?K))"
    by (rule paper_R_named_identity_sym[OF rich ek ld first_beta])
  have second_beta: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> (?E ?T) (named_lam_vec ns ?AllTop))"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_all_vector_self_identity[OF rich top binders variable rt]])
  have end_C: "paper_R_classicism_proves \<Sigma> G
    (named_paper_eq ?\<tau> (named_lam_vec ns ?AllTop) (named_lam_vec ns (paper_R_named_top G)))"
    by (rule paper_R_classicism_A2_H[OF rich paper_R_named_H_all_top[OF rich rt variable] binders])
  have end_member: "named_paper_eq ?\<tau> (named_lam_vec ns ?AllTop) (named_lam_vec ns (paper_R_named_top G)) \<in> ?S"
    using end_C by simp
  have end_local: "paper_R_named_derivable \<Sigma> G ?S
    (named_paper_eq ?\<tau> (named_lam_vec ns ?AllTop) (named_lam_vec ns (paper_R_named_top G)))"
    by (rule paper_R_named_derivable.Assumption[OF end_member paper_R_named_identity_language[OF lat ltop]])
  have chain1: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> (named_lam_vec ns ?R) (?E ?K))"
    by (rule paper_R_named_identity_trans[OF rich lr ld ek start_local reverse_beta])
  have chain2: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> (named_lam_vec ns ?R) (?E ?T))"
    by (rule paper_R_named_identity_trans[OF rich lr ek et chain1 replacement])
  have chain3: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> (named_lam_vec ns ?R) (named_lam_vec ns ?AllTop))"
    by (rule paper_R_named_identity_trans[OF rich lr et lat chain2 second_beta])
  have final_local: "paper_R_named_derivable \<Sigma> G ?S
    (named_paper_eq ?\<tau> (named_lam_vec ns ?R) (named_lam_vec ns (paper_R_named_top G)))"
    by (rule paper_R_named_identity_trans[OF rich lr lat ltop chain3 end_local])
  show ?thesis by (rule paper_R_local_H_in_classicism[OF final_local]; simp)
qed

end
