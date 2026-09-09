theory Bacon_Source_Exponential_Domain
  imports Bacon_Source_Action
begin

section \<open>The functions in an exponential fiber\<close>

text \<open>
  For actions X and Y, the domain of β∈(X⇒Y)A consists of pairs
  ⟨h,x⟩ with h:A→B and x∈XB. Its values lie in YB and satisfy
  iY(β⟨h,x⟩)=β⟨i∘h,iX(x)⟩. Source: Bacon–Dorr Example 3.16, p.54.

  Representation: paper_exponential_fiber contains all functions satisfying
  these conditions, with undefined fixed outside the indicated domain.
  The two actions may have different HOL value carriers. This is a
  set-indexed construction, not a proper-class or object-language model.
  Status: definitions and elementary membership rules only in this leaf.
\<close>

definition paper_exponential_pairs ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow>
    ('o \<Rightarrow> 'x set) \<Rightarrow> 'o \<Rightarrow> ('a \<times> 'x) set" where
  "paper_exponential_pairs arrows source target X A =
    {(h,x). h \<in> arrows \<and> source h = A \<and> x \<in> X (target h)}"

definition paper_exponential_fiber ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow>
    ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('o \<Rightarrow> 'x set) \<Rightarrow>
    ('a \<Rightarrow> 'x \<Rightarrow> 'x) \<Rightarrow> ('o \<Rightarrow> 'y set) \<Rightarrow>
    ('a \<Rightarrow> 'y \<Rightarrow> 'y) \<Rightarrow> 'o \<Rightarrow> (('a \<times> 'x) \<Rightarrow> 'y) set" where
  "paper_exponential_fiber arrows source target compose X xmap Y ymap A =
    {b. (\<forall>p. p \<notin> paper_exponential_pairs arrows source target X A \<longrightarrow>
          b p = undefined) \<and>
      (\<forall>h x. h \<in> arrows \<longrightarrow> source h = A \<longrightarrow> x \<in> X (target h) \<longrightarrow>
          b (h,x) \<in> Y (target h)) \<and>
      (\<forall>h i x. h \<in> arrows \<longrightarrow> source h = A \<longrightarrow> i \<in> arrows \<longrightarrow>
          target h = source i \<longrightarrow> x \<in> X (target h) \<longrightarrow>
          ymap i (b (h,x)) = b (compose i h, xmap i x))}"

definition paper_exponential_transport ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow>
    ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('o \<Rightarrow> 'x set) \<Rightarrow>
    'a \<Rightarrow> (('a \<times> 'x) \<Rightarrow> 'y) \<Rightarrow> (('a \<times> 'x) \<Rightarrow> 'y)" where
  "paper_exponential_transport arrows source target compose X f b =
    (\<lambda>(i,x). if (i,x) \<in> paper_exponential_pairs arrows source target X (target f)
      then b (compose i f,x) else undefined)"

lemma paper_exponential_pairs_iff:
  "(h,x) \<in> paper_exponential_pairs arrows source target X A \<longleftrightarrow>
    h \<in> arrows \<and> source h = A \<and> x \<in> X (target h)"
  by (simp add: paper_exponential_pairs_def)

lemma paper_exponential_fiberI:
  assumes normal: "\<And>p. p \<notin> paper_exponential_pairs arrows source target X A \<Longrightarrow>
      b p = undefined"
    and typed: "\<And>h x. h \<in> arrows \<Longrightarrow> source h = A \<Longrightarrow>
      x \<in> X (target h) \<Longrightarrow> b (h,x) \<in> Y (target h)"
    and coherent: "\<And>h i x. h \<in> arrows \<Longrightarrow> source h = A \<Longrightarrow>
      i \<in> arrows \<Longrightarrow> target h = source i \<Longrightarrow> x \<in> X (target h) \<Longrightarrow>
      ymap i (b (h,x)) = b (compose i h,xmap i x)"
  shows "b \<in> paper_exponential_fiber arrows source target compose X xmap Y ymap A"
  using normal typed coherent unfolding paper_exponential_fiber_def by blast

lemma paper_exponential_fiber_normal:
  assumes "b \<in> paper_exponential_fiber arrows source target compose X xmap Y ymap A"
    and "p \<notin> paper_exponential_pairs arrows source target X A"
  shows "b p = undefined"
  using assms unfolding paper_exponential_fiber_def by blast

lemma paper_exponential_fiber_type:
  assumes "b \<in> paper_exponential_fiber arrows source target compose X xmap Y ymap A"
    and "h \<in> arrows" and "source h = A" and "x \<in> X (target h)"
  shows "b (h,x) \<in> Y (target h)"
  using assms unfolding paper_exponential_fiber_def by blast

lemma paper_exponential_fiber_coherent:
  assumes "b \<in> paper_exponential_fiber arrows source target compose X xmap Y ymap A"
    and "h \<in> arrows" and "source h = A" and "i \<in> arrows"
    and "target h = source i" and "x \<in> X (target h)"
  shows "ymap i (b (h,x)) = b (compose i h,xmap i x)"
  using assms unfolding paper_exponential_fiber_def by blast

lemma paper_exponential_transport_on:
  assumes "(i,x) \<in> paper_exponential_pairs arrows source target X (target f)"
  shows "paper_exponential_transport arrows source target compose X f b (i,x) =
    b (compose i f,x)"
  using assms by (simp add: paper_exponential_transport_def)

lemma paper_exponential_transport_off:
  assumes "p \<notin> paper_exponential_pairs arrows source target X (target f)"
  shows "paper_exponential_transport arrows source target compose X f b p = undefined"
  using assms by (cases p) (simp add: paper_exponential_transport_def)

lemma paper_exponential_fiber_ext:
  assumes left: "b \<in> paper_exponential_fiber arrows source target compose X xmap Y ymap A"
    and right: "c \<in> paper_exponential_fiber arrows source target compose X xmap Y ymap A"
    and agree: "\<And>h x. (h,x) \<in> paper_exponential_pairs arrows source target X A \<Longrightarrow>
      b (h,x) = c (h,x)"
  shows "b = c"
proof (rule ext)
  fix p
  show "b p = c p"
  proof (cases "p \<in> paper_exponential_pairs arrows source target X A")
    case True
    then show ?thesis using agree by (cases p) auto
  next
    case False
    show ?thesis by (simp only: paper_exponential_fiber_normal[OF left False]
      paper_exponential_fiber_normal[OF right False])
  qed
qed

end
