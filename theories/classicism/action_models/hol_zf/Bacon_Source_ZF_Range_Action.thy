theory Bacon_Source_ZF_Range_Action
  imports Bacon_Source_ZF_Range_Carriers
begin

section \<open>The actual coded range inherits the ambient transport\<close>

text \<open>
  An equivariant family fW:D(W)→explode(B(W)) has image fibers
  coded by C(W)=range_code B f D W. The ambient maps u restrict
  to an action on these actual images (Definition 3.17, p.55).

  We first invoke the generic image-action construction. Equality of
  its image fibers with explode(C(W)) is required only at legitimate
  objects. No unjustified global equality of total family extensions,
  or equality of the range with the entire ambient fiber, is assumed.
  This helper does not itself construct a simultaneous all-type family.
\<close>

lemma paper_ZF_action_map_range:
  assumes family: "paper_action_map Obj Arrows source target D t (\<lambda>W. explode (B W)) u f"
    and object: "W \<in> Obj"
  shows "explode (paper_ZF_range_code B f D W) = paper_action_image f D W"
proof (rule paper_ZF_range_as_action_image)
  fix d
  assume member: "d \<in> D W"
  show "f W d \<in> explode (B W)" by (rule paper_action_map_type[OF family object member])
qed

theorem paper_ZF_range_action:
  assumes old_action: "paper_action Obj Arrows source target compose identity D t"
    and ambient_action: "paper_action Obj Arrows source target compose identity (\<lambda>W. explode (B W)) u"
    and family: "paper_action_map Obj Arrows source target D t (\<lambda>W. explode (B W)) u f"
  shows "paper_action Obj Arrows source target compose identity
    (\<lambda>W. explode (paper_ZF_range_code B f D W)) u"
proof -
  interpret Image: paper_action Obj Arrows source target compose identity "paper_action_image f D" u
    by (rule paper_action_image_action[OF old_action ambient_action family])
  show ?thesis
  proof unfold_locales
    fix h z
    assume arrow: "h \<in> Arrows" and member: "z \<in> explode (paper_ZF_range_code B f D (source h))"
    have so: "source h \<in> Obj" by (rule Image.source_object[OF arrow])
    have target_object: "target h \<in> Obj" by (rule Image.target_object[OF arrow])
    have original: "z \<in> paper_action_image f D (source h)"
      using member by (simp only: paper_ZF_action_map_range[OF family so])
    have transported: "u h z \<in> paper_action_image f D (target h)"
      by (rule Image.transport_type[OF arrow original])
    show "u h z \<in> explode (paper_ZF_range_code B f D (target h))"
      using transported by (simp only: paper_ZF_action_map_range[OF family target_object])
  next
    fix W z
    assume object: "W \<in> Obj" and member: "z \<in> explode (paper_ZF_range_code B f D W)"
    have original: "z \<in> paper_action_image f D W"
      using member by (simp only: paper_ZF_action_map_range[OF family object])
    show "u (identity W) z = z" by (rule Image.transport_identity[OF object original])
  next
    fix h k z
    assume first: "h \<in> Arrows" and second: "k \<in> Arrows" and meeting: "target h = source k"
      and member: "z \<in> explode (paper_ZF_range_code B f D (source h))"
    have object: "source h \<in> Obj" by (rule Image.source_object[OF first])
    have original: "z \<in> paper_action_image f D (source h)"
      using member by (simp only: paper_ZF_action_map_range[OF family object])
    show "u (compose k h) z = u k (u h z)" by (rule Image.transport_compose[OF first second meeting original])
  qed
qed

theorem paper_ZF_range_subaction:
  assumes old_action: "paper_action Obj Arrows source target compose identity D t"
    and ambient_action: "paper_action Obj Arrows source target compose identity (\<lambda>W. explode (B W)) u"
    and family: "paper_action_map Obj Arrows source target D t (\<lambda>W. explode (B W)) u f"
  shows "paper_subaction Obj Arrows source target compose identity
    (\<lambda>W. explode (paper_ZF_range_code B f D W)) u (\<lambda>W. explode (B W)) u"
proof (rule paper_subactionI[OF paper_ZF_range_action[OF old_action ambient_action family] ambient_action])
  fix W
  assume "W \<in> Obj"
  show "explode (paper_ZF_range_code B f D W) \<subseteq> explode (B W)" by (rule paper_ZF_range_code_subset)
next
  fix h z
  assume "h \<in> Arrows" and "z \<in> explode (paper_ZF_range_code B f D (source h))"
  show "u h z = u h z" by (rule refl)
qed

section \<open>Fiberwise bijections and the equivariant inverse\<close>

theorem paper_ZF_range_forward_action_map:
  assumes family: "paper_action_map Obj Arrows source target D t (\<lambda>W. explode (B W)) u f"
  shows "paper_action_map Obj Arrows source target D t
    (\<lambda>W. explode (paper_ZF_range_code B f D W)) u f"
proof (rule paper_action_mapI)
  fix W d
  assume object: "W \<in> Obj" and member: "d \<in> D W"
  have image_member: "f W d \<in> paper_action_image f D W"
    unfolding paper_action_image_def by (rule imageI[OF member])
  show "f W d \<in> explode (paper_ZF_range_code B f D W)"
    using image_member by (simp only: paper_ZF_action_map_range[OF family object])
next
  fix h d
  assume arrow: "h \<in> Arrows" and member: "d \<in> D (source h)"
  show "f (target h) (t h d) = u h (f (source h) d)"
    by (rule paper_action_map_equivariant[OF family arrow member])
qed

theorem paper_ZF_range_action_fiber_bijection:
  assumes family: "paper_action_map Obj Arrows source target D t (\<lambda>W. explode (B W)) u f"
    and object: "W \<in> Obj" and injective: "inj_on (f W) (D W)"
  shows "bij_betw (f W) (D W) (explode (paper_ZF_range_code B f D W))"
proof (rule paper_ZF_range_fiber_bijection[where B=B and f=f and D=D and W=W, OF _ injective])
  fix d
  assume member: "d \<in> D W"
  show "f W d \<in> explode (B W)" by (rule paper_action_map_type[OF family object member])
qed

theorem paper_ZF_range_inverse_action_map:
  assumes old_action: "paper_action Obj Arrows source target compose identity D t"
    and ambient_action: "paper_action Obj Arrows source target compose identity (\<lambda>W. explode (B W)) u"
    and family: "paper_action_map Obj Arrows source target D t (\<lambda>W. explode (B W)) u f"
    and injective: "\<And>W. W \<in> Obj \<Longrightarrow> inj_on (f W) (D W)"
  shows "paper_action_map Obj Arrows source target
    (\<lambda>W. explode (paper_ZF_range_code B f D W)) u D t (paper_ZF_range_decode f D)"
proof -
  interpret Old: paper_action Obj Arrows source target compose identity D t by (rule old_action)
  have inverse: "paper_action_map Obj Arrows source target (paper_action_image f D) u D t (paper_action_image_inverse f D)"
    by (rule paper_action_image_inverse_map[OF old_action ambient_action family injective])
  show ?thesis
  proof (rule paper_action_mapI)
    fix W z
    assume object: "W \<in> Obj" and member: "z \<in> explode (paper_ZF_range_code B f D W)"
    have original: "z \<in> paper_action_image f D W"
      using member by (simp only: paper_ZF_action_map_range[OF family object])
    show "paper_ZF_range_decode f D W z \<in> D W"
      unfolding paper_ZF_range_decode_def by (rule paper_action_image_inverse_type[OF original])
  next
    fix h z
    assume arrow: "h \<in> Arrows" and member: "z \<in> explode (paper_ZF_range_code B f D (source h))"
    have object: "source h \<in> Obj" by (rule Old.source_object[OF arrow])
    have original: "z \<in> paper_action_image f D (source h)"
      using member by (simp only: paper_ZF_action_map_range[OF family object])
    show "paper_ZF_range_decode f D (target h) (u h z) = t h (paper_ZF_range_decode f D (source h) z)"
      unfolding paper_ZF_range_decode_def by (rule paper_action_map_equivariant[OF inverse arrow original])
  qed
qed

end
