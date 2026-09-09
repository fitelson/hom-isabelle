theory Bacon_Source_ZF_Substitution_Abstraction
  imports Bacon_Source_ZF_Substitution_Support
begin

section \<open>Substitution beneath a different, capture-safe binder\<close>

text \<open>
  At an outgoing pair ⟨i,a⟩, C.1 transports the value of C.
  Since n is not free in C, the subsequent n-update does not change
  that value. The two distinct updates commute. The body induction
  hypothesis therefore identifies the partial values at every pair.
  Source: the abstraction case of C.3, p.71.

  No values are chosen for unassigned variables. The input need cover
  only FV(λx.λn.B) and FV(C); the pair supplies the value of n.
\<close>

lemma paper_ZF_action_model_eval_subst_Lam:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and payload: "paper_R_in_language \<Sigma> G C (G x)"
    and binder_type: "paper_R_type (G n)"
    and different: "n \<noteq> x" and fresh: "n \<notin> named_fv C"
    and first: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and body_adequate: "named_adequate g (NLam x (NLam n B))"
    and payload_adequate: "named_adequate g C"
    and returned: "paper_ZF_action_eval Ar source target compose identity D T I G C h g = Some c"
    and body_IH: "\<And>k u b. k \<in> explode Ar \<Longrightarrow> source k = root \<Longrightarrow>
      paper_ZF_action_env_typed D G (target k) u \<Longrightarrow>
      named_adequate u (NLam x B) \<Longrightarrow> named_adequate u C \<Longrightarrow>
      paper_ZF_action_eval Ar source target compose identity D T I G C k u = Some b \<Longrightarrow>
      paper_ZF_action_eval Ar source target compose identity D T I G (named_subst x C B) k u =
      paper_ZF_action_eval Ar source target compose identity D T I G B k (u(x := Some b))"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (NLam n (named_subst x C B)) h g =
    paper_ZF_action_eval Ar source target compose identity D T I G (NLam n B) h (g(x := Some c))"
proof -
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity root"
    using premodel unfolding paper_ZF_action_premodel_def by blast
  interpret Cat: paper_rooted_category Obj "explode Ar" source target compose identity root by (rule rooted)
  have points:
    "paper_ZF_action_abstraction_body compose T G n
        (paper_ZF_action_eval Ar source target compose identity D T I G (named_subst x C B)) h g z =
      paper_ZF_action_abstraction_body compose T G n
        (paper_ZF_action_eval Ar source target compose identity D T I G B) h (g(x := Some c)) z"
    if pair: "Elem z (paper_ZF_pair_code Ar source target (D (G n)) (target h))" for z
  proof -
    let ?i = "Fst z"
    let ?a = "Snd z"
    let ?k = "compose ?i h"
    let ?tg = "paper_ZF_action_transport_assignment G T ?i g"
    let ?u = "?tg(n := Some ?a)"
    let ?b = "T (G x) ?i c"
    have arrow: "?i \<in> explode Ar" and source_eq: "source ?i = target h"
      and member: "?a \<in> explode (D (G n) (target ?i))"
      using paper_ZF_pair_code_projections[OF pair] by blast+
    have meeting: "target h = source ?i" by (rule source_eq[symmetric])
    have composite: "?k \<in> explode Ar" by (rule Cat.compose_arrow[OF first arrow meeting])
    have composite_source: "source ?k = root"
      by (simp only: Cat.compose_source[OF first arrow meeting] origin)
    have composite_target: "target ?k = target ?i" by (rule Cat.compose_target[OF first arrow meeting])
    have source_typed: "paper_ZF_action_env_typed D G (source ?i) g"
      by (simp only: source_eq; rule typed)
    have transported_typed: "paper_ZF_action_env_typed D G (target ?i) ?tg"
      by (rule paper_ZF_premodel_transport_env_typed[OF premodel arrow source_typed])
    have updated_typed: "paper_ZF_action_env_typed D G (target ?i) ?u"
      by (rule paper_ZF_action_env_update[where n=n and \<sigma>="G n",
        OF transported_typed refl binder_type member])
    have input_typed: "paper_ZF_action_env_typed D G (target ?k) ?u"
      by (simp only: composite_target; rule updated_typed)
    have input_body: "named_adequate ?u (NLam x B)"
      using body_adequate
      by (auto simp: named_adequate_def named_assignment_update_domain paper_ZF_action_transport_domain)
    have input_payload: "named_adequate ?u C"
      using payload_adequate
      by (auto simp: named_adequate_def named_assignment_update_domain paper_ZF_action_transport_domain)
    have transported_value:
      "paper_ZF_action_eval Ar source target compose identity D T I G C ?k ?tg = Some ?b"
      by (rule paper_ZF_action_model_eval_naturality[
        OF model payload first origin arrow meeting typed payload_adequate returned])
    have updated_value:
      "paper_ZF_action_eval Ar source target compose identity D T I G C ?k ?u = Some ?b"
      by (simp only: paper_ZF_action_eval_update_fresh[OF fresh]; rule transported_value)
    have body_equal:
      "paper_ZF_action_eval Ar source target compose identity D T I G (named_subst x C B) ?k ?u =
        paper_ZF_action_eval Ar source target compose identity D T I G B ?k (?u(x := Some ?b))"
      by (rule body_IH[OF composite composite_source input_typed input_body input_payload updated_value])
    have assignments: "?u(x := Some ?b) =
      (paper_ZF_action_transport_assignment G T ?i (g(x := Some c)))(n := Some ?a)"
      by (simp only: paper_ZF_action_transport_update; rule ext; simp add: different)
    show ?thesis by (simp only: paper_ZF_action_abstraction_body_def body_equal assignments)
  qed
  show ?thesis by (simp only: paper_ZF_action_eval.simps;
    rule paper_ZF_substitution_abstract_cong[OF points])
qed

end
