theory Bacon_Source_ZF_Model_Truth_Separation
  imports Bacon_Source_ZF_Model_Evaluation_Naturality Bacon_Source_ZF_Proposition_Transport
begin

section \<open>Naturality converts outgoing membership into a truth test\<close>

lemma paper_ZF_action_model_formula_outgoing_truth:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and language: "paper_R_in_language \<Sigma> G P Prop"
    and first: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g" and adequate: "named_adequate g P"
    and returned: "paper_ZF_action_eval Ar source target compose identity D T I G P h g = Some p"
    and second: "i \<in> explode Ar" and meeting: "target h = source i"
  shows "paper_ZF_action_holds Ar source target compose identity D T I G (compose i h)
      (paper_ZF_action_transport_assignment G T i g) P \<longleftrightarrow> Elem i p"
proof -
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by blast
  interpret Cat: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  have member: "p \<in> explode (D Prop (target h))"
    by (rule paper_ZF_action_model_eval_member[OF model language first origin typed adequate returned])
  have source_member: "p \<in> explode (D Prop (source i))" using member by (simp only: meeting)
  have transported:
    "paper_ZF_action_eval Ar source target compose identity D T I G P (compose i h)
      (paper_ZF_action_transport_assignment G T i g) = Some (T Prop i p)"
    by (rule paper_ZF_action_model_eval_naturality[
      OF model language first origin second meeting typed adequate returned])
  have tested: "Elem (identity (target i)) (T Prop i p) \<longleftrightarrow> Elem i p"
    by (rule paper_ZF_premodel_proposition_transport_test[OF premodel second source_member])
  show ?thesis
    by (simp only: paper_ZF_action_holds_def transported option.inject Cat.compose_target[OF first second meeting];
      simp add: tested)
qed

section \<open>Uniform truth agreement separates proposition values\<close>

text \<open>
  The crucial middle step of C.7 (p.71) is semantic: uniform truth
  agreement of P and Q implies ⟦P⟧ᵍh=⟦Q⟧ᵍh. For each outgoing
  i, transport g and use truth agreement at i∘h. The preceding lemma
  identifies this truth test with membership of i in the original
  proposition values. Both values contain only outgoing arrows, so
  set extensionality proves their equality.

  The premise quantifies over EVERY root arrow and every typed
  assignment adequate for both formulas. Agreement at one world or
  one assignment is not asserted to suffice. This ingredient uses no
  H proof, BBK-model predicate or constructed representation.
\<close>

theorem paper_ZF_action_model_uniform_truth_equal:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and left: "paper_R_in_language \<Sigma> G P Prop" and right: "paper_R_in_language \<Sigma> G Q Prop"
    and uniform: "\<And>k u. k \<in> explode Ar \<Longrightarrow> source k = root \<Longrightarrow>
      paper_ZF_action_env_typed D G (target k) u \<Longrightarrow>
      named_adequate u P \<Longrightarrow> named_adequate u Q \<Longrightarrow>
      paper_ZF_action_holds Ar source target compose identity D T I G k u P =
      paper_ZF_action_holds Ar source target compose identity D T I G k u Q"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g P" and adequate_right: "named_adequate g Q"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G P h g =
    paper_ZF_action_eval Ar source target compose identity D T I G Q h g"
proof -
  obtain p where pe: "paper_ZF_action_eval Ar source target compose identity D T I G P h g = Some p"
    and pm: "p \<in> explode (D Prop (target h))"
    by (rule paper_ZF_action_model_eval_value[OF model left arrow origin typed adequate_left])
  obtain q where qe: "paper_ZF_action_eval Ar source target compose identity D T I G Q h g = Some q"
    and qm: "q \<in> explode (D Prop (target h))"
    by (rule paper_ZF_action_model_eval_value[OF model right arrow origin typed adequate_right])
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by blast
  interpret Cat: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  have object: "target h \<in> Obj" by (rule Cat.target_object[OF arrow])
  have tests: "Elem i p \<longleftrightarrow> Elem i q"
    if ia: "i \<in> explode Ar" and isource: "source i = target h" for i
  proof -
    let ?k = "compose i h"
    let ?u = "paper_ZF_action_transport_assignment G T i g"
    have meeting: "target h = source i" by (rule isource[symmetric])
    have ka: "?k \<in> explode Ar" by (rule Cat.compose_arrow[OF arrow ia meeting])
    have ko: "source ?k = root" by (simp only: Cat.compose_source[OF arrow ia meeting] origin)
    have source_typed: "paper_ZF_action_env_typed D G (source i) g" by (simp only: isource; rule typed)
    have ut: "paper_ZF_action_env_typed D G (target ?k) ?u"
      by (simp only: Cat.compose_target[OF arrow ia meeting];
        rule paper_ZF_premodel_transport_env_typed[OF premodel ia source_typed])
    have up: "named_adequate ?u P" by (simp only: paper_ZF_action_transport_adequate_iff; rule adequate_left)
    have uq: "named_adequate ?u Q" by (simp only: paper_ZF_action_transport_adequate_iff; rule adequate_right)
    have agreed:
      "paper_ZF_action_holds Ar source target compose identity D T I G ?k ?u P =
        paper_ZF_action_holds Ar source target compose identity D T I G ?k ?u Q"
      by (rule uniform[OF ka ko ut up uq])
    have p_test:
      "paper_ZF_action_holds Ar source target compose identity D T I G ?k ?u P \<longleftrightarrow> Elem i p"
      by (rule paper_ZF_action_model_formula_outgoing_truth[
        OF model left arrow origin typed adequate_left pe ia meeting])
    have q_test:
      "paper_ZF_action_holds Ar source target compose identity D T I G ?k ?u Q \<longleftrightarrow> Elem i q"
      by (rule paper_ZF_action_model_formula_outgoing_truth[
        OF model right arrow origin typed adequate_right qe ia meeting])
    show ?thesis using agreed p_test q_test by blast
  qed
  have equal: "p = q"
  proof (rule iffD2[OF Ext], intro allI)
    fix i
    show "Elem i p \<longleftrightarrow> Elem i q"
    proof (cases "i \<in> explode Ar \<and> source i = target h")
      case True
      show ?thesis by (rule tests[OF conjunct1[OF True] conjunct2[OF True]])
    next
      case False
      have not_p: "\<not> Elem i p"
        using paper_ZF_premodel_proposition_member[OF premodel object pm] False by blast
      have not_q: "\<not> Elem i q"
        using paper_ZF_premodel_proposition_member[OF premodel object qm] False by blast
      show ?thesis using not_p not_q by simp
    qed
  qed
  show ?thesis by (simp only: pe qe equal)
qed

end
