theory Bacon_Source_Image_Action_Inverse
  imports Bacon_Source_Image_Action
begin

section \<open>Inverting an injective family on its image fibers\<close>

text \<open>
  If eA:XΑ→YΑ is injective on XΑ, it has an inverse
  rA:eA[XΑ]→XΑ. For an equivariant family, these inverses also
  commute with transport: rB(hʸ(y))=hˣ(rA(y)) for h:A→B
  and y∈eA[XΑ]. This is a derived implementation ingredient for
  the profile-image construction of Bacon–Dorr Proposition 3.22,
  using the subactions of Definition 3.17, p.55; it is not a new
  source axiom or that representation theorem.

  The inverse is chosen separately in each object fiber. Its laws
  have explicit fiber guards; its arbitrary total extension outside
  the image is irrelevant. No category arrow, action transport, or
  model homomorphism is assumed invertible or injective. Only eA
  is injective on XΑ. The two action carriers may differ, and no
  uniform identification of model domains or semantic types is made.
\<close>

definition paper_action_image_inverse ::
  "('o \<Rightarrow> 'x \<Rightarrow> 'y) \<Rightarrow> ('o \<Rightarrow> 'x set) \<Rightarrow> 'o \<Rightarrow> 'y \<Rightarrow> 'x" where
  "paper_action_image_inverse e X A = inv_into (X A) (e A)"

lemma paper_action_image_inverse_left:
  assumes injective: "inj_on (e A) (X A)" and member: "x \<in> X A"
  shows "paper_action_image_inverse e X A (e A x) = x"
  unfolding paper_action_image_inverse_def
  by (rule inv_into_f_f[where f="e A" and A="X A" and x=x, OF injective member])

lemma paper_action_image_inverse_type:
  assumes member: "y \<in> paper_action_image e X A"
  shows "paper_action_image_inverse e X A y \<in> X A"
proof -
  have image_member: "y \<in> image (e A) (X A)"
    using member unfolding paper_action_image_def by assumption
  show ?thesis unfolding paper_action_image_inverse_def
    by (rule inv_into_into[where f="e A" and A="X A" and x=y, OF image_member])
qed

lemma paper_action_image_inverse_right:
  assumes member: "y \<in> paper_action_image e X A"
  shows "e A (paper_action_image_inverse e X A y) = y"
proof -
  have image_member: "y \<in> image (e A) (X A)"
    using member unfolding paper_action_image_def by assumption
  show ?thesis unfolding paper_action_image_inverse_def
    by (rule f_inv_into_f[where f="e A" and A="X A" and y=y, OF image_member])
qed

text \<open>
  Typing and the right-inverse law need only image membership.
  The left-inverse law and reverse equivariance require injectivity.
  In the equivariance proof, the constructed image action ensures
  that hʸ(y) is still an input on which the inverse laws apply.
\<close>

theorem paper_action_image_inverse_map:
  assumes source_action: "paper_action Obj Arrows source target compose identity X s"
    and target_action: "paper_action Obj Arrows source target compose identity Y t"
    and family: "paper_action_map Obj Arrows source target X s Y t e"
    and injective: "\<And>A. A \<in> Obj \<Longrightarrow> inj_on (e A) (X A)"
  shows "paper_action_map Obj Arrows source target (paper_action_image e X) t X s
    (paper_action_image_inverse e X)"
proof -
  interpret Source: paper_action Obj Arrows source target compose identity X s by (rule source_action)
  interpret Image: paper_action Obj Arrows source target compose identity "paper_action_image e X" t
    by (rule paper_action_image_action[OF source_action target_action family])
  show ?thesis
  proof (rule paper_action_mapI)
    fix A y
    assume object: "A \<in> Obj" and member: "y \<in> paper_action_image e X A"
    show "paper_action_image_inverse e X A y \<in> X A"
      by (rule paper_action_image_inverse_type[OF member])
  next
    fix h y
    assume arrow: "h \<in> Arrows" and member: "y \<in> paper_action_image e X (source h)"
    have target_object: "target h \<in> Obj" by (rule Source.target_object[OF arrow])
    have inverse_type: "paper_action_image_inverse e X (source h) y \<in> X (source h)"
      by (rule paper_action_image_inverse_type[OF member])
    have image_type: "t h y \<in> paper_action_image e X (target h)"
      by (rule Image.transport_type[OF arrow member])
    have left_type: "paper_action_image_inverse e X (target h) (t h y) \<in> X (target h)"
      by (rule paper_action_image_inverse_type[OF image_type])
    have right_type: "s h (paper_action_image_inverse e X (source h) y) \<in> X (target h)"
      by (rule Source.transport_type[OF arrow inverse_type])
    have left_image: "e (target h) (paper_action_image_inverse e X (target h) (t h y)) = t h y"
      by (rule paper_action_image_inverse_right[OF image_type])
    have source_image: "e (source h) (paper_action_image_inverse e X (source h) y) = y"
      by (rule paper_action_image_inverse_right[OF member])
    have commute: "e (target h) (s h (paper_action_image_inverse e X (source h) y)) =
        t h (e (source h) (paper_action_image_inverse e X (source h) y))"
      by (rule paper_action_map_equivariant[OF family arrow inverse_type])
    have right_image: "e (target h) (s h (paper_action_image_inverse e X (source h) y)) = t h y"
      using commute by (simp only: source_image)
    have images_equal: "e (target h) (paper_action_image_inverse e X (target h) (t h y)) =
        e (target h) (s h (paper_action_image_inverse e X (source h) y))"
      by (simp only: left_image right_image)
    show "paper_action_image_inverse e X (target h) (t h y) =
        s h (paper_action_image_inverse e X (source h) y)"
      by (rule inj_onD[OF injective[OF target_object] images_equal left_type right_type])
  qed
qed

end
