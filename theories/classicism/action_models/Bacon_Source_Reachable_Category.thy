theory Bacon_Source_Reachable_Category
  imports Bacon_Source_Reachable_Subcategory Bacon_Source_Rooted_Category
begin

section \<open>The inherited operations satisfy the category laws\<close>

text \<open>
  Restrict to objects reachable from R and all original arrows between
  them. Identities remain, and composition remains inside the selected
  objects. Source: §3.3, pp.49–50; the root convention is p.55.
  The restricted category is valid even when its object set is empty.
  The additional assumption R∈objects supplies a weakly initial root.
\<close>

context paper_category
begin

theorem paper_reachable_category:
  "paper_category (paper_reachable_objects arrows source target R)
    (paper_reachable_arrows arrows source target R) source target compose identity"
proof -
  let ?Obj = "paper_reachable_objects arrows source target R"
  let ?Arrows = "paper_reachable_arrows arrows source target R"
  have lift: "f \<in> arrows" if "f \<in> ?Arrows" for f
    by (rule paper_reachable_arrows_original[OF that])
  have sources: "source f \<in> ?Obj" if "f \<in> ?Arrows" for f
    using that by (auto simp only: paper_reachable_arrows_member)
  have targets: "target f \<in> ?Obj" if "f \<in> ?Arrows" for f
    using that by (auto simp only: paper_reachable_arrows_member)
  have original_object: "A \<in> objects" if "A \<in> ?Obj" for A
    by (rule paper_reachable_object_original[OF that])
  have ids: "identity A \<in> ?Arrows" if object: "A \<in> ?Obj" for A
  proof -
    have original: "A \<in> objects" by (rule original_object[OF object])
    show ?thesis
      by (rule paper_reachable_outgoing_retained[OF identity_arrow[OF original]];
        simp only: identity_source[OF original]; rule object)
  qed
  have comps: "compose g f \<in> ?Arrows"
    if fa: "f \<in> ?Arrows" and ga: "g \<in> ?Arrows" and meeting: "target f = source g" for f g
  proof -
    have original: "compose g f \<in> arrows" by (rule compose_arrow[OF lift[OF fa] lift[OF ga] meeting])
    have reachable: "source (compose g f) \<in> ?Obj"
      by (simp only: compose_source[OF lift[OF fa] lift[OF ga] meeting]; rule sources[OF fa])
    show ?thesis by (rule paper_reachable_outgoing_retained[OF original reachable])
  qed
  show ?thesis
  proof unfold_locales
    show "\<And>f. f \<in> ?Arrows \<Longrightarrow> source f \<in> ?Obj" by (rule sources)
    show "\<And>f. f \<in> ?Arrows \<Longrightarrow> target f \<in> ?Obj" by (rule targets)
    show "\<And>A. A \<in> ?Obj \<Longrightarrow> identity A \<in> ?Arrows" by (rule ids)
    show "\<And>A. A \<in> ?Obj \<Longrightarrow> source (identity A) = A"
      by (rule identity_source, rule original_object, assumption)
    show "\<And>A. A \<in> ?Obj \<Longrightarrow> target (identity A) = A"
      by (rule identity_target, rule original_object, assumption)
    show "\<And>f g. f \<in> ?Arrows \<Longrightarrow> g \<in> ?Arrows \<Longrightarrow> target f = source g \<Longrightarrow> compose g f \<in> ?Arrows"
      by (rule comps; assumption)
    show "\<And>f g. f \<in> ?Arrows \<Longrightarrow> g \<in> ?Arrows \<Longrightarrow> target f = source g \<Longrightarrow>
      source (compose g f) = source f"
      by (rule compose_source; ((rule lift, assumption) | assumption))
    show "\<And>f g. f \<in> ?Arrows \<Longrightarrow> g \<in> ?Arrows \<Longrightarrow> target f = source g \<Longrightarrow>
      target (compose g f) = target g"
      by (rule compose_target; ((rule lift, assumption) | assumption))
    show "\<And>f g h. f \<in> ?Arrows \<Longrightarrow> g \<in> ?Arrows \<Longrightarrow> h \<in> ?Arrows \<Longrightarrow>
      target f = source g \<Longrightarrow> target g = source h \<Longrightarrow>
      compose h (compose g f) = compose (compose h g) f"
      by (rule compose_assoc; ((rule lift, assumption) | assumption))
    show "\<And>f. f \<in> ?Arrows \<Longrightarrow> compose (identity (target f)) f = f"
      by (rule identity_left, rule lift, assumption)
    show "\<And>f. f \<in> ?Arrows \<Longrightarrow> compose f (identity (source f)) = f"
      by (rule identity_right, rule lift, assumption)
  qed
qed

theorem paper_reachable_rooted_category:
  assumes root: "R \<in> objects"
  shows "paper_rooted_category (paper_reachable_objects arrows source target R)
    (paper_reachable_arrows arrows source target R) source target compose identity R"
proof (unfold paper_rooted_category_def,
    rule conjI[OF paper_reachable_category], unfold_locales)
  show "R \<in> paper_reachable_objects arrows source target R" by (rule paper_reachable_root[OF root])
next
  fix A
  assume reachable: "A \<in> paper_reachable_objects arrows source target R"
  show "\<exists>h\<in>paper_reachable_arrows arrows source target R. source h = R \<and> target h = A"
    by (rule bspec[OF paper_reachable_root_weak_initial[OF root] reachable])
qed

end

section \<open>Every supplied action restricts along the reachable category\<close>

text \<open>
  The original fibers and transport maps are retained verbatim.
  Their guarded action laws remain true on the smaller category.
  Source: Definition 3.13, p.53. This is structural restriction,
  not an action-model interpretation or a preservation claim for the
  common theory of the original and restricted object collections.
\<close>

context paper_action
begin

theorem paper_reachable_action:
  "paper_action (paper_reachable_objects arrows source target R)
    (paper_reachable_arrows arrows source target R) source target compose identity fiber transport"
proof (unfold paper_action_def, rule conjI[OF paper_reachable_category], unfold_locales)
  fix h x
  assume arrow: "h \<in> paper_reachable_arrows arrows source target R" and member: "x \<in> fiber (source h)"
  show "transport h x \<in> fiber (target h)"
    by (rule transport_type[OF paper_reachable_arrows_original[OF arrow] member])
next
  fix A x
  assume object: "A \<in> paper_reachable_objects arrows source target R" and member: "x \<in> fiber A"
  show "transport (identity A) x = x" by (rule transport_identity[OF paper_reachable_object_original[OF object] member])
next
  fix f g x
  assume first: "f \<in> paper_reachable_arrows arrows source target R"
    and second: "g \<in> paper_reachable_arrows arrows source target R"
    and meeting: "target f = source g" and member: "x \<in> fiber (source f)"
  show "transport (compose g f) x = transport g (transport f x)"
    by (rule transport_compose[
      OF paper_reachable_arrows_original[OF first] paper_reachable_arrows_original[OF second] meeting member])
qed

end

end
