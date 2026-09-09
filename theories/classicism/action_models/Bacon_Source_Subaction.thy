theory Bacon_Source_Subaction
  imports Bacon_Source_Action
begin

section \<open>Subactions on the same category\<close>

text \<open>
  The action −* is a subaction of −† when A*⊆A† at every
  object A, and h*(x)=h†(x) for h:A→B and x∈A*.
  Source: Bacon–Dorr Definition 3.17, p.55.

  The predicate explicitly requires BOTH actions on the same category.
  Their fibers use the same value carrier, so the displayed inclusions
  are literal subsets. Agreement is required only on the smaller source
  fiber and along legitimate arrows; arbitrary HOL extensions elsewhere
  are not identified. Empty fibers and empty categories are allowed.
  No model, profile separation or action-model representation is assumed.
\<close>

definition paper_subaction ::
  "'o set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow>
    ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('o \<Rightarrow> 'a) \<Rightarrow>
    ('o \<Rightarrow> 'v set) \<Rightarrow> ('a \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
    ('o \<Rightarrow> 'v set) \<Rightarrow> ('a \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> bool" where
  "paper_subaction Obj Arrows source target compose identity U u V v \<longleftrightarrow>
    paper_action Obj Arrows source target compose identity U u \<and>
    paper_action Obj Arrows source target compose identity V v \<and>
    (\<forall>A\<in>Obj. U A \<subseteq> V A) \<and>
    (\<forall>h\<in>Arrows. \<forall>x\<in>U (source h). u h x = v h x)"

lemma paper_subactionI:
  assumes smaller: "paper_action Obj Arrows source target compose identity U u"
    and larger: "paper_action Obj Arrows source target compose identity V v"
    and fibers: "\<And>A. A \<in> Obj \<Longrightarrow> U A \<subseteq> V A"
    and maps: "\<And>h x. h \<in> Arrows \<Longrightarrow> x \<in> U (source h) \<Longrightarrow> u h x = v h x"
  shows "paper_subaction Obj Arrows source target compose identity U u V v"
  unfolding paper_subaction_def
  by (intro conjI; (rule smaller | rule larger | (intro ballI; rule fibers; assumption) |
      (intro ballI; rule maps; assumption)))

lemma paper_subaction_actions:
  assumes subaction: "paper_subaction Obj Arrows source target compose identity U u V v"
  shows "paper_action Obj Arrows source target compose identity U u"
    and "paper_action Obj Arrows source target compose identity V v"
  using subaction unfolding paper_subaction_def by blast+

lemma paper_subaction_subset:
  assumes subaction: "paper_subaction Obj Arrows source target compose identity U u V v"
    and object: "A \<in> Obj"
  shows "U A \<subseteq> V A"
  using subaction object unfolding paper_subaction_def by blast

lemma paper_subaction_transport:
  assumes subaction: "paper_subaction Obj Arrows source target compose identity U u V v"
    and arrow: "h \<in> Arrows" and member: "x \<in> U (source h)"
  shows "u h x = v h x"
  using subaction arrow member unfolding paper_subaction_def by blast

lemma paper_subaction_refl:
  assumes action: "paper_action Obj Arrows source target compose identity U u"
  shows "paper_subaction Obj Arrows source target compose identity U u U u"
  by (rule paper_subactionI[OF action action]; simp)

end
