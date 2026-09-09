theory Bacon_Source_Relational_Classicism_A2_Gen
  imports Bacon_Source_Relational_Classicism_A2_Gen_Closed
begin

section \<open>Gen preservation at every requested R prefix\<close>

text \<open>
  Extend n⃗ by a distinct prefix z⃗ covering the residual free
  variables of λn⃗.P and λn⃗.Q. Use the IH at z⃗@n⃗@[u].
  The closed-prefix calculation yields the Gen conclusion at z⃗@n⃗;
  native application congruence and self-β then recover n⃗.
  Source: Appendix A.2, p.66. Prefixes may be empty or repeat names.
  The IH is uniform over R prefixes, and u∉FV(P) is retained
  exactly as in the native Gen rule. No unrestricted abstraction of
  an open identity or semantic premise is used.
\<close>

theorem paper_R_classicism_A2_Gen:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>" and fresh: "u \<notin> named_fv P"
    and binders: "list_all paper_R_type (map G ns)"
    and premise: "\<And>ms. list_all paper_R_type (map G ms) \<Longrightarrow>
      paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ms) Prop)
        (named_lam_vec ms (named_paper_imp G P Q)) (named_lam_vec ms (paper_R_named_top G)))"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns (named_paper_imp G P (named_paper_all \<sigma> (NLam u Q))))
    (named_lam_vec ns (paper_R_named_top G)))"
proof -
  let ?R = "named_paper_imp G P (named_paper_all \<sigma> (NLam u Q))"
  let ?\<tau> = "paper_type_vector (map G ns) Prop"
  have lp: "paper_R_in_language \<Sigma> G (named_lam_vec ns P) ?\<tau>"
    by (rule paper_R_named_lam_vec_prop_language[OF pl binders])
  have lq: "paper_R_in_language \<Sigma> G (named_lam_vec ns Q) ?\<tau>"
    by (rule paper_R_named_lam_vec_prop_language[OF ql binders])
  obtain zs where distinct: "distinct zs"
    and cover: "set zs = named_fv (named_lam_vec ns P) \<union> named_fv (named_lam_vec ns Q)"
    and extra: "list_all paper_R_type (map G zs)"
    by (rule paper_R_typed_covering_prefix[OF lp lq])
  have combined: "list_all paper_R_type (map G (zs @ ns))" using extra binders by simp
  have extended: "list_all paper_R_type (map G ((zs @ ns) @ [u]))"
    using combined rt by (simp add: variable)
  have covered: "named_fv P \<union> named_fv Q \<subseteq> set (zs @ ns)"
    using cover by (auto simp: named_lam_vec_fv)
  have enlarged: "paper_R_classicism_proves \<Sigma> G
    (named_paper_eq (paper_type_vector (map G (zs @ ns)) Prop)
      (named_lam_vec (zs @ ns) ?R) (named_lam_vec (zs @ ns) (paper_R_named_top G)))"
    by (rule paper_R_classicism_A2_Gen_closed[
      OF rich pl ql variable rt fresh combined covered premise[OF extended]])
  let ?E = "named_paper_eq (paper_type_vector (map G zs) ?\<tau>)
    (named_lam_vec zs (named_lam_vec ns ?R)) (named_lam_vec zs (named_lam_vec ns (paper_R_named_top G)))"
  have outer: "paper_R_classicism_proves \<Sigma> G ?E"
    using enlarged by (simp only: map_append paper_type_vector_append paper_R_named_lam_vec_append)
  let ?S = "{A. paper_R_classicism_proves \<Sigma> G A}"
  have member: "?E \<in> ?S" using outer by simp
  have local: "paper_R_named_derivable \<Sigma> G ?S ?E"
    by (rule paper_R_named_derivable.Assumption[OF member paper_R_classicism_proves_language[OF outer]])
  have rl: "paper_R_in_language \<Sigma> G ?R Prop"
    by (rule paper_R_named_paper_imp_language[OF rich pl paper_R_named_all_binder_language[OF ql variable rt]])
  have lr: "paper_R_in_language \<Sigma> G (named_lam_vec ns ?R) ?\<tau>"
    by (rule paper_R_named_lam_vec_prop_language[OF rl binders])
  have lt: "paper_R_in_language \<Sigma> G (named_lam_vec ns (paper_R_named_top G)) ?\<tau>"
    by (rule paper_R_named_lam_vec_prop_language[OF paper_R_named_top_language[OF rich] binders])
  have result: "?\<tau> \<noteq> Ind" by simp
  have recovered: "paper_R_named_derivable \<Sigma> G ?S
    (named_paper_eq ?\<tau> (named_lam_vec ns ?R) (named_lam_vec ns (paper_R_named_top G)))"
    by (rule paper_R_named_identity_from_lam_vec[OF rich lr lt extra result local])
  show ?thesis by (rule paper_R_local_H_in_classicism[OF recovered]; simp)
qed

end
