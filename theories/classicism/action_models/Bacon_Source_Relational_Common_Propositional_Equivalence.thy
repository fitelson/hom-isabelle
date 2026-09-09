theory Bacon_Source_Relational_Common_Propositional_Equivalence
  imports Bacon_Source_Relational_Common_Theory Bacon_Source_Relational_Logical_Truth
begin

section \<open>Propositional Equivalence in the common theory\<close>

text \<open>
  If P↔Q∈T𝒞, then P=Q∈T𝒞 for a quasi-Fregean R
  BBK category. Source: Theorem 3.12, p.51.

  The biconditional is the literal λ-defined Figure 1 operator.
  Its truth theorem first gives common truth equivalence. The
  outgoing-homomorphism argument then gives common denotation
  equality, and identity truth supplies the conclusion formula.
  This is closure of the common theory, not the Fregean Axiom
  in each individual model. No syntactic C theorem is assumed.
\<close>

theorem paper_R_common_Propositional_Equivalence:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and fregean: "paper_bbk_quasi_fregean_on Obj Arrows"
    and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and common: "named_paper_iff G P Q \<in> paper_R_common_theory \<Sigma> G Obj"
  shows "named_paper_eq Prop P Q \<in> paper_R_common_theory \<Sigma> G Obj"
proof -
  have models: "paper_R_bbk_data_valid \<Sigma> G M" if "M \<in> Obj" for M
    by (rule paper_R_bbk_subcategory_models[OF category that])
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
  proof (rule paper_R_common_theoryI[OF paper_R_identity_language[OF pl ql]])
    fix M g
    assume object: "M \<in> Obj" and typed: "named_env_typed (paper_bbk_domain M) G g"
      and adequate: "named_adequate g (NApp (NApp (NLogical (SEq Prop)) P) Q)"
    have pa: "named_adequate g P" and qa: "named_adequate g Q"
      using adequate by (auto simp only: paper_R_identity_adequate_iff)
    have equal: "paper_bbk_denote M g P = paper_bbk_denote M g Q"
      by (rule paper_R_quasi_fregean_denotation[
        OF category fregean pl ql common_values object typed pa qa])
    interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
      "paper_bbk_denote M" "paper_bbk_valuation M"
      by (rule paper_R_bbk_data_model[OF models[OF object]])
    show "paper_bbk_valuation M (paper_bbk_denote M g (NApp (NApp (NLogical (SEq Prop)) P) Q))"
      using Model.valuation_identity[OF pl ql typed pa qa] equal by simp
  qed
qed

end
