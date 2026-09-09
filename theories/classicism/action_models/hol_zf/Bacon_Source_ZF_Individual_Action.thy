theory Bacon_Source_ZF_Individual_Action
  imports Bacon_Source_ZF_Embedded_Carriers
    Bacon_Classicism_Action_Development.Bacon_Source_Action
begin

section \<open>An actual coded action for the individual base\<close>

text \<open>
  Suppose every individual fiber D(W) lies in U, e is injective on U,
  and e[U]⊆explode(B) for a specified HOL-ZF set B. Represent D(W)
  by the actual set code Sep B (λz.z∈e[D(W)]), and define
  hᵉ(z)=e(h(inv_into U e z)). The action laws follow from the
  original action and the inverse equations on these fibers.
  Source role: the individual action of Definition 3.18(1), p.55,
  and the individual-base representation in Proposition 3.22, p.57.

  The target action is constructed, not assumed. Original values may
  have an arbitrary HOL carrier; arrows are coded in a specified set A.
  The injection and its set bound remain explicit premises. This is
  only individual-base groundwork, relative to standard HOL-ZF. It
  establishes no proposition/exponential transport or all-type decoder.
\<close>

definition paper_ZF_individual_fiber_code ::
  "ZF \<Rightarrow> ('v \<Rightarrow> ZF) \<Rightarrow> ('o \<Rightarrow> 'v set) \<Rightarrow> 'o \<Rightarrow> ZF" where
  "paper_ZF_individual_fiber_code B e D W = paper_ZF_image_code B e (D W)"

definition paper_ZF_individual_transport ::
  "'v set \<Rightarrow> ('v \<Rightarrow> ZF) \<Rightarrow> (ZF \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_ZF_individual_transport U e oldmap h z = e (oldmap h (inv_into U e z))"

lemma paper_ZF_individual_fiber_elements:
  assumes bound: "image e U \<subseteq> explode B" and subset: "D W \<subseteq> U"
  shows "explode (paper_ZF_individual_fiber_code B e D W) = image e (D W)"
  unfolding paper_ZF_individual_fiber_code_def by (rule paper_ZF_image_code_elements[OF bound subset])

lemma paper_ZF_individual_encode_type:
  assumes bound: "image e U \<subseteq> explode B" and subset: "D W \<subseteq> U" and member: "x \<in> D W"
  shows "e x \<in> explode (paper_ZF_individual_fiber_code B e D W)"
  by (simp only: paper_ZF_individual_fiber_elements[where D=D and W=W, OF bound subset]; rule imageI[OF member])

lemma paper_ZF_individual_decode_type:
  assumes injective: "inj_on e U" and bound: "image e U \<subseteq> explode B" and subset: "D W \<subseteq> U"
    and member: "z \<in> explode (paper_ZF_individual_fiber_code B e D W)"
  shows "inv_into U e z \<in> D W"
  by (rule paper_ZF_image_inverse_type[OF injective bound subset member[unfolded paper_ZF_individual_fiber_code_def]])

lemma paper_ZF_individual_decode_encode:
  assumes injective: "inj_on e U" and subset: "D W \<subseteq> U" and member: "x \<in> D W"
  shows "inv_into U e (e x) = x"
  by (rule paper_ZF_image_inverse_left[OF injective subset member])

lemma paper_ZF_individual_encode_decode:
  assumes bound: "image e U \<subseteq> explode B" and subset: "D W \<subseteq> U"
    and member: "z \<in> explode (paper_ZF_individual_fiber_code B e D W)"
  shows "e (inv_into U e z) = z"
  by (rule paper_ZF_image_inverse_right[OF bound subset member[unfolded paper_ZF_individual_fiber_code_def]])

lemma paper_ZF_individual_transport_encode:
  assumes injective: "inj_on e U" and member: "x \<in> U"
  shows "paper_ZF_individual_transport U e oldmap h (e x) = e (oldmap h x)"
  by (simp only: paper_ZF_individual_transport_def inv_into_f_f[where f=e and A=U and x=x, OF injective member])

lemma paper_ZF_individual_transport_decode:
  assumes injective: "inj_on e U" and result: "oldmap h (inv_into U e z) \<in> U"
  shows "inv_into U e (paper_ZF_individual_transport U e oldmap h z) = oldmap h (inv_into U e z)"
  by (simp only: paper_ZF_individual_transport_def
    inv_into_f_f[where f=e and A=U and x="oldmap h (inv_into U e z)", OF injective result])

theorem paper_ZF_individual_action:
  fixes Obj :: "'o set" and A B :: ZF
    and source target :: "ZF \<Rightarrow> 'o"
    and compose :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" and identity :: "'o \<Rightarrow> ZF"
    and D :: "'o \<Rightarrow> 'v set" and oldmap :: "ZF \<Rightarrow> 'v \<Rightarrow> 'v"
    and U :: "'v set" and e :: "'v \<Rightarrow> ZF"
  assumes action: "paper_action Obj (explode A) source target compose identity D oldmap"
    and fibers: "\<And>W. W \<in> Obj \<Longrightarrow> D W \<subseteq> U"
    and injective: "inj_on e U" and bound: "image e U \<subseteq> explode B"
  shows "paper_action Obj (explode A) source target compose identity
    (\<lambda>W. explode (paper_ZF_individual_fiber_code B e D W)) (paper_ZF_individual_transport U e oldmap)"
proof -
  interpret Source: paper_action Obj "explode A" source target compose identity D oldmap by (rule action)
  show ?thesis
  proof unfold_locales
    fix h z
    assume arrow: "h \<in> explode A"
      and member: "z \<in> explode (paper_ZF_individual_fiber_code B e D (source h))"
    have source_bound: "D (source h) \<subseteq> U" by (rule fibers[OF Source.source_object[OF arrow]])
    have target_bound: "D (target h) \<subseteq> U" by (rule fibers[OF Source.target_object[OF arrow]])
    have decoded: "inv_into U e z \<in> D (source h)"
      by (rule paper_ZF_individual_decode_type[where D=D and W="source h", OF injective bound source_bound member])
    have moved: "oldmap h (inv_into U e z) \<in> D (target h)"
      by (rule Source.transport_type[OF arrow decoded])
    show "paper_ZF_individual_transport U e oldmap h z \<in>
        explode (paper_ZF_individual_fiber_code B e D (target h))"
      unfolding paper_ZF_individual_transport_def
      by (rule paper_ZF_individual_encode_type[where D=D and W="target h", OF bound target_bound moved])
  next
    fix W z
    assume object: "W \<in> Obj" and member: "z \<in> explode (paper_ZF_individual_fiber_code B e D W)"
    have fiber_bound: "D W \<subseteq> U" by (rule fibers[OF object])
    have decoded: "inv_into U e z \<in> D W"
      by (rule paper_ZF_individual_decode_type[where D=D and W=W, OF injective bound fiber_bound member])
    have unit: "oldmap (identity W) (inv_into U e z) = inv_into U e z"
      by (rule Source.transport_identity[OF object decoded])
    show "paper_ZF_individual_transport U e oldmap (identity W) z = z"
      by (simp only: paper_ZF_individual_transport_def unit;
        rule paper_ZF_individual_encode_decode[where D=D and W=W, OF bound fiber_bound member])
  next
    fix f g z
    assume first: "f \<in> explode A" and second: "g \<in> explode A" and meeting: "target f = source g"
      and member: "z \<in> explode (paper_ZF_individual_fiber_code B e D (source f))"
    have source_bound: "D (source f) \<subseteq> U" by (rule fibers[OF Source.source_object[OF first]])
    have middle_bound: "D (target f) \<subseteq> U" by (rule fibers[OF Source.target_object[OF first]])
    have decoded: "inv_into U e z \<in> D (source f)"
      by (rule paper_ZF_individual_decode_type[where D=D and W="source f", OF injective bound source_bound member])
    have moved: "oldmap f (inv_into U e z) \<in> D (target f)"
      by (rule Source.transport_type[OF first decoded])
    have middle_member: "oldmap f (inv_into U e z) \<in> U" by (rule subsetD[OF middle_bound moved])
    have inverse: "inv_into U e (e (oldmap f (inv_into U e z))) = oldmap f (inv_into U e z)"
      by (rule inv_into_f_f[where f=e and A=U and x="oldmap f (inv_into U e z)", OF injective middle_member])
    have associative: "oldmap (compose g f) (inv_into U e z) = oldmap g (oldmap f (inv_into U e z))"
      by (rule Source.transport_compose[OF first second meeting decoded])
    show "paper_ZF_individual_transport U e oldmap (compose g f) z =
        paper_ZF_individual_transport U e oldmap g (paper_ZF_individual_transport U e oldmap f z)"
      by (simp only: paper_ZF_individual_transport_def inverse associative)
  qed
qed

theorem paper_ZF_individual_decode_transport_on_fiber:
  fixes Obj :: "'o set" and A B :: ZF
    and source target :: "ZF \<Rightarrow> 'o"
    and compose :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" and identity :: "'o \<Rightarrow> ZF"
    and D :: "'o \<Rightarrow> 'v set" and oldmap :: "ZF \<Rightarrow> 'v \<Rightarrow> 'v"
    and U :: "'v set" and e :: "'v \<Rightarrow> ZF" and h z :: ZF
  assumes action: "paper_action Obj (explode A) source target compose identity D oldmap"
    and fibers: "\<And>W. W \<in> Obj \<Longrightarrow> D W \<subseteq> U"
    and injective: "inj_on e U" and bound: "image e U \<subseteq> explode B"
    and arrow: "h \<in> explode A" and member: "z \<in> explode (paper_ZF_individual_fiber_code B e D (source h))"
  shows "inv_into U e (paper_ZF_individual_transport U e oldmap h z) = oldmap h (inv_into U e z)"
proof -
  interpret Source: paper_action Obj "explode A" source target compose identity D oldmap by (rule action)
  have source_bound: "D (source h) \<subseteq> U" by (rule fibers[OF Source.source_object[OF arrow]])
  have target_bound: "D (target h) \<subseteq> U" by (rule fibers[OF Source.target_object[OF arrow]])
  have decoded: "inv_into U e z \<in> D (source h)"
    by (rule paper_ZF_individual_decode_type[where D=D and W="source h", OF injective bound source_bound member])
  have moved: "oldmap h (inv_into U e z) \<in> D (target h)" by (rule Source.transport_type[OF arrow decoded])
  have result: "oldmap h (inv_into U e z) \<in> U" by (rule subsetD[OF target_bound moved])
  show ?thesis by (rule paper_ZF_individual_transport_decode[where oldmap=oldmap and h=h and z=z, OF injective result])
qed

theorem paper_ZF_individual_fiber_nonempty:
  assumes bound: "image e U \<subseteq> explode B" and subset: "D W \<subseteq> U" and nonempty: "D W \<noteq> {}"
  shows "explode (paper_ZF_individual_fiber_code B e D W) \<noteq> {}"
proof -
  obtain x where member: "x \<in> D W" using nonempty by blast
  have encoded: "e x \<in> explode (paper_ZF_individual_fiber_code B e D W)"
    by (rule paper_ZF_individual_encode_type[where D=D and W=W, OF bound subset member])
  show ?thesis using encoded by blast
qed

theorem paper_ZF_individual_fiber_bijection:
  assumes injective: "inj_on e U" and bound: "image e U \<subseteq> explode B" and subset: "D W \<subseteq> U"
  shows "bij_betw e (D W) (explode (paper_ZF_individual_fiber_code B e D W))"
  unfolding paper_ZF_individual_fiber_code_def by (rule paper_ZF_image_code_bijection[OF injective bound subset])

text \<open>
  Nonemptiness transfers at each retained object; that particular fact
  needs no injectivity. The action and inverse laws do need injectivity
  on U. No property is asserted of transport on off-fiber arguments.
\<close>

end
