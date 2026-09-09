theory Bacon_Source_Relational_Closed_LE_Generators
  imports Bacon_Source_Relational_Vector_Identity_Recovery Bacon_Source_Relational_Classicism_Presentation
    Bacon_Source_Relational_Assignment_Extension
begin

section \<open>Native local H consequences remain available in source-defined C\<close>

theorem paper_R_local_H_in_classicism:
  assumes derivation: "paper_R_named_derivable \<Sigma> G S A"
    and source_premises: "\<And>B. B \<in> S \<Longrightarrow> paper_R_in_language \<Sigma> G B Prop \<Longrightarrow>
      paper_R_classicism_proves \<Sigma> G B"
  shows "paper_R_classicism_proves \<Sigma> G A"
  using derivation source_premises
proof (induction rule: paper_R_named_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.prems[OF Assumption.hyps])
next
  case Theorem
  show ?case by (rule paper_R_classicism_proves.H[OF Theorem.hyps])
next
  case MP
  show ?case by (rule paper_R_classicism_proves.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
qed

section \<open>A distinct prefix binds exactly the residual free-variable set\<close>

lemma paper_R_typed_covering_prefix:
  assumes left: "paper_R_in_language \<Sigma> G K \<tau>" and right: "paper_R_in_language \<Sigma> G L \<tau>"
  obtains zs where "distinct zs" "set zs = named_fv K \<union> named_fv L"
    "list_all paper_R_type (map G zs)"
proof -
  have finite: "finite (named_fv K \<union> named_fv L)" by (rule finite_UnI[OF named_fv_finite named_fv_finite])
  obtain zs where cover: "set zs = named_fv K \<union> named_fv L" and distinct: "distinct zs"
    using finite_distinct_list[OF finite] by blast
  have binder_types: "paper_R_type (G n)" if member: "n \<in> set zs" for n
  proof -
    have alternatives: "n \<in> named_fv K \<or> n \<in> named_fv L" using member by (simp only: cover; blast)
    show ?thesis using alternatives paper_R_language_fv_type[OF left] paper_R_language_fv_type[OF right] by blast
  qed
  have binders: "list_all paper_R_type (map G zs)" using binder_types by (simp add: list_all_iff)
  show thesis by (rule that[OF distinct cover binders])
qed

section \<open>Each open Logical Equivalence instance has one closed generator\<close>

text \<open>
  Put K=λn⃗.P and L=λn⃗.Q, and enumerate FV(K)∪FV(L)
  by a distinct prefix z⃗. Logical Equivalence at z⃗@n⃗ gives the
  CLOSED identity (λz⃗.K)=(λz⃗.L), using the original H certificate
  P↔Q. Applying it to z⃗ and using native self-β recovers K=L.
  Source role: the closed-identity base case of Appendix A.2, pp.65–66,
  for the p.12 presentation that permits residual free variables.

  z⃗ is not fresh for K or L: it deliberately binds their free names.
  The original n⃗ may be empty or contain repeated binders. The recovery
  is a local H consequence of ONE closed identity, not an invocation of
  the Equivalence rule, general λ-congruence, F conversion, or semantic
  completeness. This lemma alone does not prove reverse presentation
  inclusion; the subsequent Classicism_A2/A3 leaves supply that
  induction and closure, without assuming them here.
\<close>

theorem paper_R_classicism_LE_closed_generator:
  assumes rich: "paper_R_rich G"
    and certificate: "paper_R_named_H \<Sigma> G (named_paper_iff G P Q)"
    and left: "paper_R_in_language \<Sigma> G P Prop" and right: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
  obtains \<rho> U V where "paper_R_in_language \<Sigma> G U \<rho>" "paper_R_in_language \<Sigma> G V \<rho>"
    "named_fv U = {}" "named_fv V = {}"
    "paper_R_classicism_proves \<Sigma> G (named_paper_eq \<rho> U V)"
    "paper_R_named_derivable \<Sigma> G {named_paper_eq \<rho> U V}
      (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q))"
proof -
  let ?K = "named_lam_vec ns P"
  let ?L = "named_lam_vec ns Q"
  let ?\<tau> = "paper_type_vector (map G ns) Prop"
  have kl: "paper_R_in_language \<Sigma> G ?K ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF left binders])
  have ll: "paper_R_in_language \<Sigma> G ?L ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF right binders])
  obtain zs where distinct: "distinct zs" and cover: "set zs = named_fv ?K \<union> named_fv ?L"
    and extra: "list_all paper_R_type (map G zs)"
    by (rule paper_R_typed_covering_prefix[OF kl ll])
  let ?F = "named_lam_vec zs ?K"
  let ?H = "named_lam_vec zs ?L"
  let ?\<rho> = "paper_type_vector (map G zs) ?\<tau>"
  let ?E = "named_paper_eq ?\<rho> ?F ?H"
  have result: "?\<tau> \<noteq> Ind" by simp
  have fl: "paper_R_in_language \<Sigma> G ?F ?\<rho>" by (rule paper_R_named_lam_vec_language[OF kl extra result])
  have hl: "paper_R_in_language \<Sigma> G ?H ?\<rho>" by (rule paper_R_named_lam_vec_language[OF ll extra result])
  have el: "paper_R_in_language \<Sigma> G ?E Prop" by (rule paper_R_named_identity_language[OF fl hl])
  have cover_K: "named_fv ?K \<subseteq> set zs" and cover_L: "named_fv ?L \<subseteq> set zs"
    using cover by blast+
  have fc: "named_fv ?F = {}" by (rule named_lam_vec_closed[OF cover_K])
  have hc: "named_fv ?H = {}" by (rule named_lam_vec_closed[OF cover_L])
  have combined: "list_all paper_R_type (map G (zs @ ns))" using extra binders by simp
  have source_identity: "paper_R_classicism_proves \<Sigma> G
    (named_paper_eq (paper_type_vector (map G (zs @ ns)) Prop)
      (named_lam_vec (zs @ ns) P) (named_lam_vec (zs @ ns) Q))"
    by (rule paper_R_classicism_proves.Logical_Equivalence[OF certificate left right combined])
  have generator: "paper_R_classicism_proves \<Sigma> G ?E"
    using source_identity by (simp only: map_append paper_type_vector_append paper_R_named_lam_vec_append)
  have premise: "paper_R_named_derivable \<Sigma> G {?E} ?E"
    by (rule paper_R_named_derivable.Assumption; (rule singletonI | rule el))
  have recovered: "paper_R_named_derivable \<Sigma> G {?E} (named_paper_eq ?\<tau> ?K ?L)"
    by (rule paper_R_named_identity_from_lam_vec[OF rich kl ll extra result premise])
  show thesis by (rule that[OF fl hl fc hc generator recovered])
qed

end
