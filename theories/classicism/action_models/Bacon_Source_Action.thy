theory Bacon_Source_Action
  imports Bacon_Source_Category
begin

section \<open>An action is a covariant set-valued assignment\<close>

text \<open>
  An action gives a fiber A* at each object and a map h*:A*→B*
  at each arrow h:A→B, preserving identities and composition.
  Source: Bacon–Dorr Definition 3.13, p.53. Thus
  (g∘f)*(x)=g*(f*(x)), with all arrows composable and x∈source(f)*.

  Representation: fiber and transport are total functions, but their
  action laws are guarded by valid objects, arrows and fiber elements.
  No injectivity, surjectivity, nonempty fiber, finite category, or
  interpretation of object-language terms is assumed.
\<close>

locale paper_action = paper_category objects arrows source target compose identity
  for objects :: "'o set" and arrows :: "'a set"
    and source :: "'a \<Rightarrow> 'o" and target :: "'a \<Rightarrow> 'o"
    and compose :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and identity :: "'o \<Rightarrow> 'a" +
  fixes fiber :: "'o \<Rightarrow> 'v set" and transport :: "'a \<Rightarrow> 'v \<Rightarrow> 'v"
  assumes transport_type: "h \<in> arrows \<Longrightarrow> x \<in> fiber (source h) \<Longrightarrow>
      transport h x \<in> fiber (target h)"
    and transport_identity: "A \<in> objects \<Longrightarrow> x \<in> fiber A \<Longrightarrow>
      transport (identity A) x = x"
    and transport_compose: "f \<in> arrows \<Longrightarrow> g \<in> arrows \<Longrightarrow>
      target f = source g \<Longrightarrow> x \<in> fiber (source f) \<Longrightarrow>
      transport (compose g f) x = transport g (transport f x)"
begin

lemma paper_transport_image:
  assumes arrow: "h \<in> arrows"
  shows "image (transport h) (fiber (source h)) \<subseteq> fiber (target h)"
proof
  fix y
  assume member: "y \<in> image (transport h) (fiber (source h))"
  obtain x where source_member: "x \<in> fiber (source h)" and shape: "y = transport h x"
    using member by blast
  show "y \<in> fiber (target h)"
    by (simp only: shape; rule transport_type[OF arrow source_member])
qed

lemma paper_transport_composable:
  assumes composable: "paper_composable f g" and member: "x \<in> fiber (source f)"
  shows "transport (compose g f) x = transport g (transport f x)"
  by (rule transport_compose[OF paper_composableD(1,2,3)[OF composable] member])

lemma paper_transport_three:
  assumes first: "paper_composable f g" and second: "paper_composable g h"
    and member: "x \<in> fiber (source f)"
  shows "transport (compose h (compose g f)) x = transport h (transport g (transport f x))"
proof -
  have fa: "f \<in> arrows" and ga: "g \<in> arrows" and fg: "target f = source g"
    by (rule paper_composableD[OF first])+
  have combined: "paper_composable (compose g f) h"
    by (rule paper_composable_composites(1)[OF first second])
  have start: "x \<in> fiber (source (compose g f))"
    by (simp only: compose_source[OF fa ga fg]; rule member)
  have outer: "transport (compose h (compose g f)) x = transport h (transport (compose g f) x)"
    by (rule paper_transport_composable[OF combined start])
  show ?thesis by (simp only: outer paper_transport_composable[OF first member])
qed

end

context paper_category
begin

lemma paper_empty_action:
  "paper_action objects arrows source target compose identity (\<lambda>_. {}) transport"
  by unfold_locales simp_all

end

end
