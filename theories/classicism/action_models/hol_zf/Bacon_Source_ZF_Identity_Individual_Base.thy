theory Bacon_Source_ZF_Identity_Individual_Base
  imports Bacon_Source_ZF_Subset_Carriers
    Bacon_Classicism_Action_Development.Bacon_Source_Action
begin

section \<open>The literal identity base for already coded individuals\<close>

text \<open>
  Proposition 3.22 defines fᵉM(a)=a (p.72). If the original
  individual values are already ZF values and D(W)⊆explode(B),
  separation inside B represents exactly D(W), with identity as
  the value map. The original transport is retained verbatim.

  This is not the arbitrary-carrier injection construction.
  It proves the source-literal identity specialization for an
  explicitly bounded individual base. It neither transports an
  arbitrary HOL-valued BBK model into ZF nor removes the set bound.
  Foundation: standard HOL-ZF.
\<close>

definition paper_ZF_identity_fiber_code ::
  "ZF \<Rightarrow> ('o \<Rightarrow> ZF set) \<Rightarrow> 'o \<Rightarrow> ZF" where
  "paper_ZF_identity_fiber_code B D W = paper_ZF_encode_subset B (D W)"

theorem paper_ZF_identity_fiber_elements:
  assumes bounded: "D W \<subseteq> explode B"
  shows "explode (paper_ZF_identity_fiber_code B D W) = D W"
  unfolding paper_ZF_identity_fiber_code_def
  by (rule paper_ZF_decode_encode_subset[OF bounded])

theorem paper_ZF_identity_base_bijection:
  assumes bounded: "D W \<subseteq> explode B"
  shows "bij_betw id (D W) (explode (paper_ZF_identity_fiber_code B D W))"
  by (simp add: paper_ZF_identity_fiber_elements[where D=D and W=W, OF bounded] bij_betw_def)

theorem paper_ZF_identity_base_action:
  assumes action: "paper_action Obj Arrows source target compose identity D t"
    and bounded: "\<And>W. W \<in> Obj \<Longrightarrow> D W \<subseteq> explode B"
  shows "paper_action Obj Arrows source target compose identity
    (\<lambda>W. explode (paper_ZF_identity_fiber_code B D W)) t"
proof -
  interpret Original: paper_action Obj Arrows source target compose identity D t by (rule action)
  have same: "explode (paper_ZF_identity_fiber_code B D W) = D W" if "W \<in> Obj" for W
    by (rule paper_ZF_identity_fiber_elements[where D=D and W=W, OF bounded[OF that]])
  show ?thesis
  proof unfold_locales
    fix h x
    assume arrow: "h \<in> Arrows"
      and member: "x \<in> explode (paper_ZF_identity_fiber_code B D (source h))"
    have original: "x \<in> D (source h)" using member
      by (simp only: same[OF Original.source_object[OF arrow]])
    have mapped: "t h x \<in> D (target h)" by (rule Original.transport_type[OF arrow original])
    show "t h x \<in> explode (paper_ZF_identity_fiber_code B D (target h))"
      by (simp only: same[OF Original.target_object[OF arrow]]; rule mapped)
  next
    fix W x
    assume object: "W \<in> Obj" and member: "x \<in> explode (paper_ZF_identity_fiber_code B D W)"
    have original: "x \<in> D W" using member by (simp only: same[OF object])
    show "t (identity W) x = x" by (rule Original.transport_identity[OF object original])
  next
    fix f g x
    assume first: "f \<in> Arrows" and second: "g \<in> Arrows" and meeting: "target f = source g"
      and member: "x \<in> explode (paper_ZF_identity_fiber_code B D (source f))"
    have original: "x \<in> D (source f)" using member
      by (simp only: same[OF Original.source_object[OF first]])
    show "t (compose g f) x = t g (t f x)"
      by (rule Original.transport_compose[OF first second meeting original])
  qed
qed

end
