theory Bacon_Source_ZF_Model_Vector_Identity
  imports Bacon_Source_ZF_Model_Vector_Equality Bacon_Source_ZF_Action_BBK_Identity_Truth
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Equivalence_Presentation
begin

section \<open>Uniform truth agreement validates the vector identity\<close>

text \<open>
  If P and Q agree in truth at every typed adequate root input,
  then (λn⃗.P)=(λn⃗.Q) holds at every adequate root input.
  Source role: the semantic part of Proposition C.7, p.71.
  Proposition-value separation and compatible-context equality prove
  equality of the complete abstraction values; the independently checked
  identity truth clause then gives the displayed object-language formula.

  This theorem has no H or C proof premise. The later Logical
  Equivalence theorem supplies uniform truth from an H derivation.
  Empty vectors and repeated raw binders retain their literal meaning.
\<close>

theorem paper_ZF_action_model_uniform_truth_vector_identity:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and left: "paper_R_in_language \<Sigma> G P Prop" and right: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and uniform: "\<And>k u. k \<in> explode Ar \<Longrightarrow> source k = root \<Longrightarrow>
      paper_ZF_action_env_typed D G (target k) u \<Longrightarrow>
      named_adequate u P \<Longrightarrow> named_adequate u Q \<Longrightarrow>
      paper_ZF_action_holds Ar source target compose identity D T I G k u P =
      paper_ZF_action_holds Ar source target compose identity D T I G k u Q"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g (named_lam_vec ns P)"
    and adequate_right: "named_adequate g (named_lam_vec ns Q)"
  shows "paper_ZF_action_holds Ar source target compose identity D T I G h g
    (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q))"
proof -
  let ?LP = "named_lam_vec ns P"
  let ?LQ = "named_lam_vec ns Q"
  let ?r = "paper_type_vector (map G ns) Prop"
  let ?E = "named_paper_eq ?r ?LP ?LQ"
  let ?J = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h"
  let ?V = "paper_ZF_action_bbk_valuation target identity h"
  have lp: "paper_R_in_language \<Sigma> G ?LP ?r"
    by (rule paper_R_named_lam_vec_prop_language[OF left binders])
  have lq: "paper_R_in_language \<Sigma> G ?LQ ?r"
    by (rule paper_R_named_lam_vec_prop_language[OF right binders])
  have language: "paper_R_in_language \<Sigma> G ?E Prop"
    by (rule paper_R_equivalence_identity_language[OF lp lq])
  have adequate: "named_adequate g ?E"
    using adequate_left adequate_right by (auto simp: named_adequate_def named_paper_primitive_fv)
  have bt: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    by (simp only: paper_ZF_action_bbk_env_iff; rule typed)
  have evaluations: "paper_ZF_action_eval Ar source target compose identity D T I G ?LP h g =
    paper_ZF_action_eval Ar source target compose identity D T I G ?LQ h g"
    by (rule paper_ZF_action_model_uniform_truth_vector_equal[
      OF model left right binders uniform arrow origin typed adequate_left adequate_right])
  have denotations: "?J g ?LP = ?J g ?LQ"
    by (simp only: paper_ZF_action_bbk_denote_def evaluations)
  have identity_truth: "?V (?J g ?E) = (?J g ?LP = ?J g ?LQ)"
    unfolding named_paper_eq_def
    by (rule paper_ZF_action_bbk_valuation_identity[OF model arrow origin lp lq bt adequate_left adequate_right])
  have truth: "?V (?J g ?E)" by (simp only: identity_truth denotations)
  show ?thesis
    by (rule iffD2[OF paper_ZF_action_bbk_holds_iff[OF model language arrow origin bt adequate] truth])
qed

end
