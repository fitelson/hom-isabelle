theory Bacon_Source_Exponential_Action
  imports Bacon_Source_Exponential_Transport
begin

section \<open>The exponential is an action\<close>

text \<open>
  The identities 1Aβ=β and (g∘f)β=g(fβ) follow from the category
  identity and associativity laws. Equality outside the pair domain follows
  from normalization, not an additional property of X or Y.
  Source: Bacon–Dorr Example 3.16, p.54.

  Representation: paper_exponential_action_from_actions constructs the
  paper_action predicate from the two supplied action predicates.
  Status: the exponential-action laws are proved here. No BBK model,
  object-language completeness, or size bound on the small category is used.
\<close>

context paper_exponential_actions
begin

lemma paper_exponential_transport_identity:
  assumes ao: "A \<in> objects" and member: "b \<in> exponential_fiber A"
  shows "exponential_transport (identity A) b = b"
proof -
  have ia: "identity A \<in> arrows" by (rule X.identity_arrow[OF ao])
  have si: "source (identity A) = A" by (rule X.identity_source[OF ao])
  have ti: "target (identity A) = A" by (rule X.identity_target[OF ao])
  have bs: "b \<in> exponential_fiber (source (identity A))" using member by (simp only: si)
  have moved: "exponential_transport (identity A) b \<in> exponential_fiber A"
    using paper_exponential_transport_type[OF ia bs] by (simp only: ti)
  show ?thesis
  proof (rule paper_exponential_fiber_ext[OF moved member])
    fix h x
    assume pair: "(h,x) \<in> exponential_pairs A"
    have ha: "h \<in> arrows" and sh: "source h = A"
      using pair by (auto simp: paper_exponential_pairs_iff)
    have at_target: "(h,x) \<in> exponential_pairs (target (identity A))"
      using pair by (simp only: ti)
    have unit: "compose h (identity A) = h"
      using X.identity_right[OF ha] by (simp only: sh)
    show "exponential_transport (identity A) b (h,x) = b (h,x)"
      by (simp only: paper_exponential_transport_on[OF at_target] unit)
  qed
qed

lemma paper_exponential_transport_compose:
  assumes fa: "f \<in> arrows" and ga: "g \<in> arrows" and fg: "target f = source g"
    and member: "b \<in> exponential_fiber (source f)"
  shows "exponential_transport (compose g f) b =
    exponential_transport g (exponential_transport f b)"
proof -
  have ca: "compose g f \<in> arrows" by (rule X.compose_arrow[OF fa ga fg])
  have cs: "source (compose g f) = source f" by (rule X.compose_source[OF fa ga fg])
  have ct: "target (compose g f) = target g" by (rule X.compose_target[OF fa ga fg])
  have bc: "b \<in> exponential_fiber (source (compose g f))" using member by (simp only: cs)
  have left: "exponential_transport (compose g f) b \<in> exponential_fiber (target g)"
    using paper_exponential_transport_type[OF ca bc] by (simp only: ct)
  have middle: "exponential_transport f b \<in> exponential_fiber (source g)"
    using paper_exponential_transport_type[OF fa member] by (simp only: fg)
  have right: "exponential_transport g (exponential_transport f b) \<in>
      exponential_fiber (target g)"
    by (rule paper_exponential_transport_type[OF ga middle])
  show ?thesis
  proof (rule paper_exponential_fiber_ext[OF left right])
    fix h x
    assume pair: "(h,x) \<in> exponential_pairs (target g)"
    have ha: "h \<in> arrows" and sh: "source h = target g"
      using pair by (auto simp: paper_exponential_pairs_iff)
    have gh: "target g = source h" by (rule sh[symmetric])
    have composite_pair: "(h,x) \<in> exponential_pairs (target (compose g f))"
      using pair by (simp only: ct)
    have pre: "(compose h g,x) \<in> exponential_pairs (source g)"
      by (rule paper_exponential_precompose_pair[OF ga pair])
    have middle_pair: "(compose h g,x) \<in> exponential_pairs (target f)"
      using pre by (simp only: fg)
    have assoc: "compose h (compose g f) = compose (compose h g) f"
      by (rule X.compose_assoc[OF fa ga ha fg gh])
    show "exponential_transport (compose g f) b (h,x) =
        exponential_transport g (exponential_transport f b) (h,x)"
      by (simp only: paper_exponential_transport_on[OF composite_pair]
        paper_exponential_transport_on[OF pair]
        paper_exponential_transport_on[OF middle_pair] assoc)
  qed
qed

theorem paper_exponential_action:
  "paper_action objects arrows source target compose identity exponential_fiber exponential_transport"
  by unfold_locales
    (auto intro: paper_exponential_transport_type paper_exponential_transport_identity
      paper_exponential_transport_compose)

end

theorem paper_exponential_action_from_actions:
  assumes source_action: "paper_action objects arrows source target compose identity X xmap"
    and target_action: "paper_action objects arrows source target compose identity Y ymap"
  shows "paper_action objects arrows source target compose identity
    (paper_exponential_fiber arrows source target compose X xmap Y ymap)
    (paper_exponential_transport arrows source target compose X)"
proof -
  interpret E: paper_exponential_actions objects arrows source target compose identity X xmap Y ymap
    by (unfold_locales; use source_action target_action in \<open>auto simp: paper_action_def paper_action_axioms_def paper_category_def\<close>)
  show ?thesis by (rule E.paper_exponential_action)
qed

end
