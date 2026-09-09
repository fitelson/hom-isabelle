theory Bacon_Source_Image_Action
  imports Bacon_Source_Subaction
begin

section \<open>Images of equivariant families are subactions\<close>

text \<open>
  Suppose eA:XΑ→YΑ commutes with transport:
  eB(hˣ(x))=hʸ(eA(x)) for h:A→B and x∈XΑ.
  Then eA[XΑ]⊆YΑ, and the inherited Y maps make these images
  a subaction of Y. This is the elementary construction needed for
  the profile images preceding Bacon–Dorr Definition 3.17, p.55.

  The source and target actions may have DIFFERENT value carriers.
  The raw family predicate below states typing and equivariance only;
  the image theorem separately requires both actual actions. It proves
  the action laws, rather than assuming an image action. Injectivity
  is unnecessary: nothing here identifies X with its image or proves
  that any truth/applicative profile separates its original elements.
\<close>

definition paper_action_map ::
  "'o set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow>
    ('o \<Rightarrow> 'x set) \<Rightarrow> ('a \<Rightarrow> 'x \<Rightarrow> 'x) \<Rightarrow>
    ('o \<Rightarrow> 'y set) \<Rightarrow> ('a \<Rightarrow> 'y \<Rightarrow> 'y) \<Rightarrow>
    ('o \<Rightarrow> 'x \<Rightarrow> 'y) \<Rightarrow> bool" where
  "paper_action_map Obj Arrows source target X s Y t e \<longleftrightarrow>
    (\<forall>A\<in>Obj. \<forall>x\<in>X A. e A x \<in> Y A) \<and>
    (\<forall>h\<in>Arrows. \<forall>x\<in>X (source h).
      e (target h) (s h x) = t h (e (source h) x))"

lemma paper_action_mapI:
  assumes typed: "\<And>A x. A \<in> Obj \<Longrightarrow> x \<in> X A \<Longrightarrow> e A x \<in> Y A"
    and equivariant: "\<And>h x. h \<in> Arrows \<Longrightarrow> x \<in> X (source h) \<Longrightarrow>
      e (target h) (s h x) = t h (e (source h) x)"
  shows "paper_action_map Obj Arrows source target X s Y t e"
  unfolding paper_action_map_def
  by (intro conjI ballI; (rule typed | rule equivariant); assumption)

lemma paper_action_map_type:
  assumes family: "paper_action_map Obj Arrows source target X s Y t e"
    and object: "A \<in> Obj" and member: "x \<in> X A"
  shows "e A x \<in> Y A"
  using family object member unfolding paper_action_map_def by blast

lemma paper_action_map_equivariant:
  assumes family: "paper_action_map Obj Arrows source target X s Y t e"
    and arrow: "h \<in> Arrows" and member: "x \<in> X (source h)"
  shows "e (target h) (s h x) = t h (e (source h) x)"
  using family arrow member unfolding paper_action_map_def by blast

definition paper_action_image ::
  "('o \<Rightarrow> 'x \<Rightarrow> 'y) \<Rightarrow> ('o \<Rightarrow> 'x set) \<Rightarrow> 'o \<Rightarrow> 'y set" where
  "paper_action_image e X A = image (e A) (X A)"

lemma paper_action_image_member:
  "y \<in> paper_action_image e X A \<longleftrightarrow> (\<exists>x\<in>X A. y = e A x)"
  unfolding paper_action_image_def by blast

lemma paper_action_image_subset:
  assumes family: "paper_action_map Obj Arrows source target X s Y t e" and object: "A \<in> Obj"
  shows "paper_action_image e X A \<subseteq> Y A"
proof
  fix y
  assume member: "y \<in> paper_action_image e X A"
  obtain x where xm: "x \<in> X A" and value_eq: "y = e A x"
    using member unfolding paper_action_image_def by blast
  have image_type: "e A x \<in> Y A" by (rule paper_action_map_type[OF family object xm])
  show "y \<in> Y A" by (simp only: value_eq; rule image_type)
qed

theorem paper_action_image_action:
  assumes source_action: "paper_action Obj Arrows source target compose identity X s"
    and target_action: "paper_action Obj Arrows source target compose identity Y t"
    and family: "paper_action_map Obj Arrows source target X s Y t e"
  shows "paper_action Obj Arrows source target compose identity (paper_action_image e X) t"
proof -
  interpret Source: paper_action Obj Arrows source target compose identity X s by (rule source_action)
  interpret Target: paper_action Obj Arrows source target compose identity Y t by (rule target_action)
  show ?thesis
  proof unfold_locales
    fix h y
    assume arrow: "h \<in> Arrows" and member: "y \<in> paper_action_image e X (source h)"
    obtain x where xm: "x \<in> X (source h)" and value_eq: "y = e (source h) x"
      using member unfolding paper_action_image_def by blast
    have transported: "s h x \<in> X (target h)" by (rule Source.transport_type[OF arrow xm])
    have commute: "e (target h) (s h x) = t h (e (source h) x)"
      by (rule paper_action_map_equivariant[OF family arrow xm])
    have image_member: "e (target h) (s h x) \<in> paper_action_image e X (target h)"
      unfolding paper_action_image_def by (rule imageI[OF transported])
    show "t h y \<in> paper_action_image e X (target h)"
      using image_member by (simp only: commute value_eq)
  next
    fix A y
    assume object: "A \<in> Obj" and member: "y \<in> paper_action_image e X A"
    have ym: "y \<in> Y A" by (rule subsetD[OF paper_action_image_subset[OF family object] member])
    show "t (identity A) y = y" by (rule Target.transport_identity[OF object ym])
  next
    fix f g y
    assume first: "f \<in> Arrows" and second: "g \<in> Arrows" and meeting: "target f = source g"
      and member: "y \<in> paper_action_image e X (source f)"
    have object: "source f \<in> Obj" by (rule Source.source_object[OF first])
    have ym: "y \<in> Y (source f)"
      by (rule subsetD[OF paper_action_image_subset[OF family object] member])
    show "t (compose g f) y = t g (t f y)"
      by (rule Target.transport_compose[OF first second meeting ym])
  qed
qed

theorem paper_action_image_subaction:
  assumes source_action: "paper_action Obj Arrows source target compose identity X s"
    and target_action: "paper_action Obj Arrows source target compose identity Y t"
    and family: "paper_action_map Obj Arrows source target X s Y t e"
  shows "paper_subaction Obj Arrows source target compose identity
    (paper_action_image e X) t Y t"
proof (rule paper_subactionI[OF paper_action_image_action[OF source_action target_action family] target_action])
  show "\<And>A. A \<in> Obj \<Longrightarrow> paper_action_image e X A \<subseteq> Y A"
    by (rule paper_action_image_subset[OF family]; assumption)
next
  show "\<And>h x. h \<in> Arrows \<Longrightarrow> x \<in> paper_action_image e X (source h) \<Longrightarrow> t h x = t h x"
    by (rule refl)
qed

end
