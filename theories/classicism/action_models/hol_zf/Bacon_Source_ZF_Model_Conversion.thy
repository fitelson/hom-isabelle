theory Bacon_Source_ZF_Model_Conversion
  imports Bacon_Source_ZF_Model_Signature_Conversion Bacon_Source_ZF_Action_Model_Nonempty
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Signature_Conservativity
begin

section \<open>A derived R completion preserves the original partial assignment\<close>

lemma paper_ZF_action_model_complete_assignment:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and object: "W \<in> Obj" and typed: "paper_ZF_action_env_typed D G W g"
  shows "paper_ZF_action_env_typed D G W (paper_R_complete_assignment (\<lambda>\<rho>. explode (D \<rho> W)) G g)"
    and "dom (paper_R_complete_assignment (\<lambda>\<rho>. explode (D \<rho> W)) G g) = {n. paper_R_type (G n)}"
proof -
  let ?u = "paper_R_complete_assignment (\<lambda>\<rho>. explode (D \<rho> W)) G g"
  have inhabited: "explode (D \<rho> W) \<noteq> {}" if rt: "paper_R_type \<rho>" for \<rho>
    by (rule paper_ZF_action_model_R_domain_nonempty[OF model object rt])
  have old_typed: "named_env_typed (\<lambda>\<rho>. explode (D \<rho> W)) G g"
    by (rule paper_ZF_action_env_named[OF typed])
  have completed_typed: "named_env_typed (\<lambda>\<rho>. explode (D \<rho> W)) G ?u"
    by (rule paper_R_complete_assignment_typed[OF inhabited old_typed])
  have support: "dom g \<subseteq> {n. paper_R_type (G n)}"
    using typed unfolding paper_ZF_action_env_typed_def by blast
  have exact: "dom ?u = {n. paper_R_type (G n)}"
    using support by (auto simp only: paper_R_complete_assignment_domain)
  show "paper_ZF_action_env_typed D G W ?u"
    by (rule paper_ZF_action_envI[where D=D and W=W and G=G, OF completed_typed]; simp only: exact; simp)
  show "dom ?u = {n. paper_R_type (G n)}" by (rule exact)
qed

section \<open>C.6 for endpoint-adequate partial assignments\<close>

text \<open>
  βη-convertible R terms have equal interpretations in every action
  model. Source: Proposition C.6, p.71. The auxiliary completion below
  is derived from nonemptiness at R types; it preserves every existing
  value and leaves non-R names undefined. It is not an added model
  field or a full-F completion assumption.

  Every intermediate term of the signature-guarded chain is adequate
  under that completion. Raw evaluator locality then restores the
  original assignment at both endpoints. Thus the conclusion assumes
  adequacy only for the endpoints, not for all intermediate syntax.
\<close>

theorem paper_ZF_action_model_signature_conversion:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and conversion: "paper_R_beta_eta_in_signature \<Sigma> G \<rho> A B"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g A" and adequate_right: "named_adequate g B"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
    paper_ZF_action_eval Ar source target compose identity D T I G B h g"
proof -
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by blast
  interpret Cat: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  have object: "target h \<in> Obj" by (rule Cat.target_object[OF arrow])
  let ?u = "paper_R_complete_assignment (\<lambda>\<rho>. explode (D \<rho> (target h))) G g"
  have completed_typed: "paper_ZF_action_env_typed D G (target h) ?u"
    and total: "dom ?u = {n. paper_R_type (G n)}"
    by (rule paper_ZF_action_model_complete_assignment[OF model object typed])+
  have converted:
    "paper_ZF_action_eval Ar source target compose identity D T I G A h ?u =
      paper_ZF_action_eval Ar source target compose identity D T I G B h ?u"
    by (rule paper_ZF_action_model_signature_conversion_total[
      OF model conversion arrow origin completed_typed total])
  have left_local:
    "paper_ZF_action_eval Ar source target compose identity D T I G A h ?u =
      paper_ZF_action_eval Ar source target compose identity D T I G A h g"
    by (rule paper_ZF_action_eval_locality; rule paper_R_complete_assignment_agrees[OF adequate_left]; assumption)
  have right_local:
    "paper_ZF_action_eval Ar source target compose identity D T I G B h ?u =
      paper_ZF_action_eval Ar source target compose identity D T I G B h g"
    by (rule paper_ZF_action_eval_locality; rule paper_R_complete_assignment_agrees[OF adequate_right]; assumption)
  show ?thesis by (rule trans[OF left_local[symmetric] trans[OF converted right_local]])
qed

section \<open>Raw R conversion is first retracted into the declared signature\<close>

text \<open>
  Raw conversion can use undeclared constants at intermediate nodes.
  The independent R signature-conservativity theorem replaces those
  occurrences by fresh R-typed names before the semantic induction.
  No appeal to an F conversion chain or F model is made.
\<close>

theorem paper_ZF_action_model_raw_conversion:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and conversion: "paper_R_raw_beta_eta G \<rho> A B"
    and left: "paper_R_in_language \<Sigma> G A \<rho>" and right: "paper_R_in_language \<Sigma> G B \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g A" and adequate_right: "named_adequate g B"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
    paper_ZF_action_eval Ar source target compose identity D T I G B h g"
proof -
  have rich: "paper_R_rich G" using model unfolding paper_ZF_action_model_def by (rule conjunct1)
  have guarded: "paper_R_beta_eta_in_signature \<Sigma> G \<rho> A B"
    by (rule paper_R_raw_to_signature[OF rich conversion left right])
  show ?thesis by (rule paper_ZF_action_model_signature_conversion[
    OF model guarded arrow origin typed adequate_left adequate_right])
qed

end
