theory Bacon_Source_ZF_Action_Classicism_Soundness
  imports Bacon_Source_ZF_Action_BBK_Representation
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Classicism_BBK_Soundness
begin

section \<open>Native Classicism is valid at every root-arrow BBK interpretation\<close>

text \<open>
  The constructed Mₕ is an independent R-BBK model, and C.7 proves
  validity of its H-certified Logical Equivalence instances. The direct
  five-constructor C soundness theorem then applies to Mₕ. No general
  Equivalence-rule closure or presentation inclusion is used.

  Source: the soundness direction of Theorem 3.23, p.57, as concluded
  after Proposition C.7, pp.71–72. Completeness is not asserted here.
  The supplied generic action model is the only model premise; no
  category of BBK models, empty theory, F model or representability
  condition from the opposite construction is assumed.
\<close>

theorem paper_ZF_action_classicism_BBK_valid:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and derivation: "paper_R_classicism_proves \<Sigma> G A"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
  shows "paper_R_bbk_model.paper_R_valid \<Sigma> G (paper_ZF_action_bbk_domain D (target h))
    (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h)
    (paper_ZF_action_bbk_valuation target identity h) A"
proof -
  let ?D = "paper_ZF_action_bbk_domain D (target h)"
  let ?J = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h"
  let ?V = "paper_ZF_action_bbk_valuation target identity h"
  interpret M: paper_R_bbk_model \<Sigma> G ?D ?J ?V
    by (rule paper_ZF_action_to_R_bbk_model[OF model arrow origin])
  show ?thesis
  proof (rule M.paper_R_classicism_BBK_soundness[OF _ derivation])
    fix P Q ns
    assume certificate: "paper_R_named_H \<Sigma> G (named_paper_iff G P Q)"
      and left: "paper_R_in_language \<Sigma> G P Prop" and right: "paper_R_in_language \<Sigma> G Q Prop"
      and binders: "list_all paper_R_type (map G ns)"
    show "M.paper_R_valid (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q))"
      by (rule paper_ZF_action_bbk_logical_equivalence_valid[OF model arrow origin certificate left right binders])
  qed
qed

theorem paper_ZF_action_classicism_truth:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and derivation: "paper_R_classicism_proves \<Sigma> G A"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and typed: "paper_ZF_action_env_typed D G (target h) g" and adequate: "named_adequate g A"
  shows "paper_ZF_action_holds Ar source target compose identity D T I G h g A"
proof -
  let ?D = "paper_ZF_action_bbk_domain D (target h)"
  let ?J = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h"
  let ?V = "paper_ZF_action_bbk_valuation target identity h"
  interpret M: paper_R_bbk_model \<Sigma> G ?D ?J ?V
    by (rule paper_ZF_action_to_R_bbk_model[OF model arrow origin])
  have language: "paper_R_in_language \<Sigma> G A Prop" by (rule paper_R_classicism_proves_language[OF derivation])
  have named_typed: "named_env_typed ?D G g" by (simp only: paper_ZF_action_bbk_env_iff; rule typed)
  have valid: "M.paper_R_valid A" by (rule paper_ZF_action_classicism_BBK_valid[OF model derivation arrow origin])
  have truth: "?V (?J g A)" by (rule M.paper_R_validE[OF valid named_typed adequate])
  show ?thesis by (rule iffD2[OF paper_ZF_action_bbk_holds_iff[OF model language arrow origin named_typed adequate] truth])
qed

corollary paper_ZF_action_classicism_soundness:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and derivation: "paper_R_classicism_proves \<Sigma> G A"
  shows "\<forall>g. paper_ZF_action_env_typed D G Root g \<longrightarrow> named_adequate g A \<longrightarrow>
    paper_ZF_action_holds Ar source target compose identity D T I G (identity Root) g A"
proof -
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity Root"
    using model unfolding paper_ZF_action_model_def paper_ZF_action_premodel_def by blast
  interpret C: paper_rooted_category Obj "explode Ar" source target compose identity Root by (rule rooted)
  have arrow: "identity Root \<in> explode Ar" by (rule C.identity_arrow[OF C.root_object])
  have origin: "source (identity Root) = Root" by (rule C.identity_source[OF C.root_object])
  have target: "target (identity Root) = Root" by (rule C.identity_target[OF C.root_object])
  show ?thesis
  proof (intro allI impI)
    fix g
    assume typed: "paper_ZF_action_env_typed D G Root g" and adequate: "named_adequate g A"
    have at_target: "paper_ZF_action_env_typed D G (target (identity Root)) g"
      by (simp only: target; rule typed)
    show "paper_ZF_action_holds Ar source target compose identity D T I G (identity Root) g A"
      by (rule paper_ZF_action_classicism_truth[OF model derivation arrow origin at_target adequate])
  qed
qed

end
