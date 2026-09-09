theory Bacon_Source_Relational_Classicism_A2_MP
  imports Bacon_Source_Relational_Classicism_A2_MP_Closed
begin

section \<open>Cover residual variables, preserve MP, and recover the original prefix\<close>

text \<open>
  The induction hypotheses apply to EVERY R prefix. For the requested
  n⃗, choose a distinct z⃗ covering the residual free variables of
  λn⃗.P and λn⃗.Q. At z⃗@n⃗, the premise abstractions are
  closed, so the preceding closed-prefix MP theorem applies.
  Applying its resulting identity to z⃗ recovers the n⃗ identity.
  Source: Appendix A.2's MP step, p.66.

  The extra prefix binds residual variables rather than being fresh
  for the bodies. The requested prefix may be empty or repeat names.
  Every introduced type is in R. No open-identity abstraction rule,
  Equivalence rule or semantic premise is assumed.
\<close>

theorem paper_R_classicism_A2_MP:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and first: "\<And>ms. list_all paper_R_type (map G ms) \<Longrightarrow>
      paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ms) Prop)
        (named_lam_vec ms Q) (named_lam_vec ms (paper_R_named_top G)))"
    and second: "\<And>ms. list_all paper_R_type (map G ms) \<Longrightarrow>
      paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ms) Prop)
        (named_lam_vec ms (named_paper_imp G Q P)) (named_lam_vec ms (paper_R_named_top G)))"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns P) (named_lam_vec ns (paper_R_named_top G)))"
proof -
  let ?P = "named_lam_vec ns P"
  let ?Q = "named_lam_vec ns Q"
  let ?T = "named_lam_vec ns (paper_R_named_top G)"
  let ?\<tau> = "paper_type_vector (map G ns) Prop"
  have lp: "paper_R_in_language \<Sigma> G ?P ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF pl binders])
  have lq: "paper_R_in_language \<Sigma> G ?Q ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF ql binders])
  have lt: "paper_R_in_language \<Sigma> G ?T ?\<tau>"
    by (rule paper_R_named_lam_vec_prop_language[OF paper_R_named_top_language[OF rich] binders])
  obtain zs where distinct: "distinct zs" and cover: "set zs = named_fv ?P \<union> named_fv ?Q"
    and extra: "list_all paper_R_type (map G zs)"
    by (rule paper_R_typed_covering_prefix[OF lp lq])
  have combined: "list_all paper_R_type (map G (zs @ ns))" using extra binders by simp
  have covered: "named_fv P \<union> named_fv Q \<subseteq> set (zs @ ns)"
    using cover by (auto simp: named_lam_vec_fv)
  have enlarged: "paper_R_classicism_proves \<Sigma> G
    (named_paper_eq (paper_type_vector (map G (zs @ ns)) Prop)
      (named_lam_vec (zs @ ns) P) (named_lam_vec (zs @ ns) (paper_R_named_top G)))"
    by (rule paper_R_classicism_A2_MP_closed[OF rich pl ql combined covered first[OF combined] second[OF combined]])
  let ?E = "named_paper_eq (paper_type_vector (map G zs) ?\<tau>) (named_lam_vec zs ?P) (named_lam_vec zs ?T)"
  have outer_identity: "paper_R_classicism_proves \<Sigma> G ?E"
    using enlarged by (simp only: map_append paper_type_vector_append paper_R_named_lam_vec_append)
  let ?S = "{A. paper_R_classicism_proves \<Sigma> G A}"
  have member: "?E \<in> ?S" using outer_identity by simp
  have language: "paper_R_in_language \<Sigma> G ?E Prop"
    by (rule paper_R_classicism_proves_language[OF outer_identity])
  have premise: "paper_R_named_derivable \<Sigma> G ?S ?E"
    by (rule paper_R_named_derivable.Assumption[OF member language])
  have result: "?\<tau> \<noteq> Ind" by simp
  have recovered: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?P ?T)"
    by (rule paper_R_named_identity_from_lam_vec[OF rich lp lt extra result premise])
  show ?thesis by (rule paper_R_local_H_in_classicism[OF recovered]; simp)
qed

end
