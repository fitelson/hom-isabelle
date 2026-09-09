theory Bacon_Source_Relational_Common_Equivalence
  imports Bacon_Source_Relational_Intensional_Abstraction
    Bacon_Source_Relational_Common_Propositional_Equivalence
begin

section \<open>Full vector Equivalence in the common R theory\<close>

text \<open>
  If P↔Q belongs to the common theory of an intensional R category,
  then (λn₁…nₖ.P)=(λn₁…nₖ.Q) belongs to it as well.
  Source: Equivalence on p.14 and Theorem 3.12, pp.51–52.

  The bodies may be open and the vector need not bind all their free
  variables. The empty vector gives Propositional Equivalence. The
  sequential-update proof also covers repeated raw binders; this is
  an explicit formal guarantee, not a distinctness-free claim about
  the alternative ζ-style rule with repeated test variables.

  Each target-domain tuple is tested after transporting the original
  assignment. Common biconditional truth gives equal abstraction
  intensions, injectivity gives equal denotations, and actual-identity
  truth yields the conclusion. No C proof judgment or axiom-based
  presentation equivalence is assumed in this semantic rule.
\<close>

theorem paper_R_common_Equivalence:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows"
    and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and common: "named_paper_iff G P Q \<in> paper_R_common_theory \<Sigma> G Obj"
  shows "named_paper_eq (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns P) (named_lam_vec ns Q) \<in> paper_R_common_theory \<Sigma> G Obj"
proof -
  let ?LP = "named_lam_vec ns P"
  let ?LQ = "named_lam_vec ns Q"
  let ?t = "paper_type_vector (map G ns) Prop"
  have models: "paper_R_bbk_data_valid \<Sigma> G M" if "M \<in> Obj" for M
    by (rule paper_R_bbk_subcategory_models[OF category that])
  have lpl: "paper_R_in_language \<Sigma> G ?LP ?t"
    by (rule paper_R_named_lam_vec_prop_language[OF pl binders])
  have lql: "paper_R_in_language \<Sigma> G ?LQ ?t"
    by (rule paper_R_named_lam_vec_prop_language[OF ql binders])
  have common_values: "paper_bbk_valuation N (paper_bbk_denote N k P) =
      paper_bbk_valuation N (paper_bbk_denote N k Q)"
    if object: "N \<in> Obj" and typed: "named_env_typed (paper_bbk_domain N) G k"
      and pa: "named_adequate k P" and qa: "named_adequate k Q" for N k
  proof -
    interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain N"
      "paper_bbk_denote N" "paper_bbk_valuation N"
      by (rule paper_R_bbk_data_model[OF models[OF object]])
    have adequate: "named_adequate k (named_paper_iff G P Q)"
      using pa qa by (auto simp: named_adequate_def named_paper_defined_fv)
    have truth: "paper_bbk_valuation N (paper_bbk_denote N k (named_paper_iff G P Q))"
      by (rule paper_R_common_theory_truth[OF common object typed adequate])
    show ?thesis using truth
      by (simp only: Model.paper_R_named_paper_iff_truth[OF pl ql typed pa qa])
  qed
  show ?thesis unfolding named_paper_eq_def
  proof (rule paper_R_common_theoryI[OF paper_R_identity_language[OF lpl lql]])
    fix M g
    assume object: "M \<in> Obj" and typed: "named_env_typed (paper_bbk_domain M) G g"
      and adequate: "named_adequate g (NApp (NApp (NLogical (SEq ?t)) ?LP) ?LQ)"
    have pa: "named_adequate g ?LP" and qa: "named_adequate g ?LQ"
      using adequate by (auto simp only: paper_R_identity_adequate_iff)
    have equal: "paper_bbk_denote M g ?LP = paper_bbk_denote M g ?LQ"
      by (rule paper_R_intensional_abstraction_denotation[
        OF category intensional pl ql binders common_values object typed pa qa])
    interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
      "paper_bbk_denote M" "paper_bbk_valuation M"
      by (rule paper_R_bbk_data_model[OF models[OF object]])
    show "paper_bbk_valuation M (paper_bbk_denote M g (NApp (NApp (NLogical (SEq ?t)) ?LP) ?LQ))"
      using Model.valuation_identity[OF lpl lql typed pa qa] equal by simp
  qed
qed

end
