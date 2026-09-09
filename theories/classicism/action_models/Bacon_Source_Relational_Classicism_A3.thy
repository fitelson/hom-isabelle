theory Bacon_Source_Relational_Classicism_A3
  imports Bacon_Source_Relational_Classicism_A3_Closed
begin

section \<open>Source-defined C is closed under Equivalence\<close>

text \<open>
  From ⊢C A↔B infer ⊢C(λn⃗.A)=(λn⃗.B).
  Choose a distinct prefix z⃗ covering the residual free variables
  of λn⃗.A and λn⃗.B. The p.67 selector calculation applies
  at z⃗@n⃗, where its substituted premise operators are closed.
  Apply the resulting identity to z⃗ and use native self-β to
  recover the originally requested n⃗.

  This is Appendix A.3 for the independent native p.12 judgment.
  Neither the recursive Equivalence presentation nor a model/completeness
  theorem is a premise. The requested prefix may be empty, contain
  repeated names, and leave free variables unbound. This does not
  itself prove the separate finite Figures 3–4 axiomatization.
\<close>

theorem paper_R_classicism_A3:
  assumes rich: "paper_R_rich G"
    and premise: "paper_R_classicism_proves \<Sigma> G (named_paper_iff G A B)"
    and al: "paper_R_in_language \<Sigma> G A Prop" and bl: "paper_R_in_language \<Sigma> G B Prop"
    and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns A) (named_lam_vec ns B))"
proof -
  let ?\<tau> = "paper_type_vector (map G ns) Prop"
  have la: "paper_R_in_language \<Sigma> G (named_lam_vec ns A) ?\<tau>"
    by (rule paper_R_named_lam_vec_prop_language[OF al binders])
  have lb: "paper_R_in_language \<Sigma> G (named_lam_vec ns B) ?\<tau>"
    by (rule paper_R_named_lam_vec_prop_language[OF bl binders])
  obtain zs where distinct: "distinct zs"
    and cover: "set zs = named_fv (named_lam_vec ns A) \<union> named_fv (named_lam_vec ns B)"
    and extra: "list_all paper_R_type (map G zs)"
    by (rule paper_R_typed_covering_prefix[OF la lb])
  have combined: "list_all paper_R_type (map G (zs @ ns))" using extra binders by simp
  have covered: "named_fv A \<union> named_fv B \<subseteq> set (zs @ ns)"
    using cover by (auto simp: named_lam_vec_fv)
  have enlarged: "paper_R_classicism_proves \<Sigma> G
    (named_paper_eq (paper_type_vector (map G (zs @ ns)) Prop)
      (named_lam_vec (zs @ ns) A) (named_lam_vec (zs @ ns) B))"
    by (rule paper_R_classicism_A3_closed[OF rich al bl combined covered premise])
  let ?E = "named_paper_eq (paper_type_vector (map G zs) ?\<tau>)
    (named_lam_vec zs (named_lam_vec ns A)) (named_lam_vec zs (named_lam_vec ns B))"
  have outer: "paper_R_classicism_proves \<Sigma> G ?E"
    using enlarged by (simp only: map_append paper_type_vector_append paper_R_named_lam_vec_append)
  let ?S = "{P. paper_R_classicism_proves \<Sigma> G P}"
  have member: "?E \<in> ?S" using outer by simp
  have local: "paper_R_named_derivable \<Sigma> G ?S ?E"
    by (rule paper_R_named_derivable.Assumption[OF member paper_R_classicism_proves_language[OF outer]])
  have result: "?\<tau> \<noteq> Ind" by simp
  have recovered: "paper_R_named_derivable \<Sigma> G ?S
    (named_paper_eq ?\<tau> (named_lam_vec ns A) (named_lam_vec ns B))"
    by (rule paper_R_named_identity_from_lam_vec[OF rich la lb extra result local])
  show ?thesis by (rule paper_R_local_H_in_classicism[OF recovered]; simp)
qed

corollary paper_R_classicism_propositional_equivalence:
  assumes rich: "paper_R_rich G"
    and premise: "paper_R_classicism_proves \<Sigma> G (named_paper_iff G A B)"
    and al: "paper_R_in_language \<Sigma> G A Prop" and bl: "paper_R_in_language \<Sigma> G B Prop"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_eq Prop A B)"
proof -
  have empty: "list_all paper_R_type (map G [])" by simp
  have identity: "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G []) Prop)
    (named_lam_vec [] A) (named_lam_vec [] B))"
    by (rule paper_R_classicism_A3[OF rich premise al bl empty])
  show ?thesis using identity by simp
qed

end
