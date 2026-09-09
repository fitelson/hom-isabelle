theory Bacon_Source_Powerset_Action
  imports Bacon_Source_Action
begin

section \<open>The concrete powerset action\<close>

text \<open>
  Write out(A) for the arrows with source A. Example 3.15 of
  Bacon–Dorr, p.54, defines Aᴾ=𝒫(out(A)) and, for h:A→B,
  hᴾ(X)={i:B→C | i∘h∈X}, with C ranging over the objects.
  Thus hᴾ maps the fiber at A to the fiber at B. Composition is
  covariant: (g∘f)ᴾ(X)=gᴾ(fᴾ(X)).

  Representation. Objects and arrows are sets of arbitrary cardinality.
  compose g f means g after f. The comprehension restricts i to a
  valid arrow with source target(h), so all compositions used by the
  category-law proofs have their required guards. Total HOL functions
  outside legitimate inputs carry no additional category assertion.
  No abstract powerset action, injectivity, surjectivity, finiteness,
  BBK model or interpretation is assumed.
\<close>

definition paper_outgoing :: "'a set \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> 'a set" where
  "paper_outgoing arrows source A = {h\<in>arrows. source h = A}"

definition paper_powerset_fiber ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> 'a set set" where
  "paper_powerset_fiber arrows source A = Pow (paper_outgoing arrows source A)"

definition paper_powerset_transport ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow>
    ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "paper_powerset_transport arrows source target compose h X =
    {i\<in>paper_outgoing arrows source (target h). compose i h \<in> X}"

lemma paper_outgoing_member:
  "h \<in> paper_outgoing arrows source A \<longleftrightarrow> h \<in> arrows \<and> source h = A"
  by (simp only: paper_outgoing_def mem_Collect_eq)

lemma paper_powerset_fiber_member:
  "X \<in> paper_powerset_fiber arrows source A \<longleftrightarrow> X \<subseteq> paper_outgoing arrows source A"
  by (simp only: paper_powerset_fiber_def Pow_iff)

lemma paper_powerset_transport_member:
  "i \<in> paper_powerset_transport arrows source target compose h X \<longleftrightarrow>
    i \<in> arrows \<and> source i = target h \<and> compose i h \<in> X"
  by (simp add: paper_powerset_transport_def paper_outgoing_member)

lemma paper_powerset_transport_type:
  "paper_powerset_transport arrows source target compose h X
    \<in> paper_powerset_fiber arrows source (target h)"
  unfolding paper_powerset_fiber_def paper_powerset_transport_def by auto

text \<open>
  The range-membership lemma is a set-theoretic property of the
  comprehension, even for arbitrary h and X. The action laws below
  concern legitimate category arrows; identity additionally uses X⊆out(A).
\<close>

context paper_category
begin

theorem paper_powerset_transport_identity:
  assumes object: "A \<in> objects"
    and fiber: "X \<in> paper_powerset_fiber arrows source A"
  shows "paper_powerset_transport arrows source target compose (identity A) X = X"
proof (rule set_eqI)
  fix i
  have target_identity: "target (identity A) = A" by (rule identity_target[OF object])
  have subset: "X \<subseteq> paper_outgoing arrows source A"
    by (rule iffD1[OF paper_powerset_fiber_member fiber])
  show "(i \<in> paper_powerset_transport arrows source target compose (identity A) X) = (i \<in> X)"
  proof (cases "i \<in> arrows \<and> source i = A")
    case True
    have arrow: "i \<in> arrows" and origin: "source i = A" using True by blast+
    have unit: "compose i (identity A) = i"
      using identity_right[OF arrow] by (simp only: origin)
    show ?thesis by (simp only: paper_powerset_transport_member target_identity arrow origin unit; simp)
  next
    case False
    have absent: "i \<notin> X" using subset False by (auto simp only: paper_outgoing_member)
    show ?thesis using False absent
      by (auto simp only: paper_powerset_transport_member target_identity)
  qed
qed

theorem paper_powerset_transport_compose:
  assumes first: "f \<in> arrows" and second: "g \<in> arrows"
    and meeting: "target f = source g"
  shows "paper_powerset_transport arrows source target compose (compose g f) X =
    paper_powerset_transport arrows source target compose g
      (paper_powerset_transport arrows source target compose f X)"
proof (rule set_eqI)
  fix i
  have composite_target: "target (compose g f) = target g"
    by (rule compose_target[OF first second meeting])
  show "(i \<in> paper_powerset_transport arrows source target compose (compose g f) X) =
    (i \<in> paper_powerset_transport arrows source target compose g
      (paper_powerset_transport arrows source target compose f X))"
  proof (cases "i \<in> arrows \<and> source i = target g")
    case True
    have arrow: "i \<in> arrows" and origin: "source i = target g" using True by blast+
    have next_meeting: "target g = source i" by (rule origin[symmetric])
    have composite_arrow: "compose i g \<in> arrows"
      by (rule compose_arrow[OF second arrow next_meeting])
    have composite_source: "source (compose i g) = target f"
      by (simp only: compose_source[OF second arrow next_meeting]; rule meeting[symmetric])
    have associative: "compose i (compose g f) = compose (compose i g) f"
      by (rule compose_assoc[OF first second arrow meeting next_meeting])
    show ?thesis by (simp only: paper_powerset_transport_member composite_target arrow origin
      composite_arrow composite_source associative; simp)
  next
    case False
    show ?thesis using False
      by (auto simp only: paper_powerset_transport_member composite_target)
  qed
qed

section \<open>The displayed functions satisfy the action interface\<close>

theorem paper_powerset_action:
  "paper_action objects arrows source target compose identity
    (paper_powerset_fiber arrows source) (paper_powerset_transport arrows source target compose)"
proof unfold_locales
  fix h X
  assume arrow: "h \<in> arrows" and member: "X \<in> paper_powerset_fiber arrows source (source h)"
  show "paper_powerset_transport arrows source target compose h X
    \<in> paper_powerset_fiber arrows source (target h)"
    by (rule paper_powerset_transport_type)
next
  fix A X
  assume object: "A \<in> objects" and member: "X \<in> paper_powerset_fiber arrows source A"
  show "paper_powerset_transport arrows source target compose (identity A) X = X"
    by (rule paper_powerset_transport_identity[OF object member])
next
  fix f g X
  assume first: "f \<in> arrows" and second: "g \<in> arrows" and meeting: "target f = source g"
    and member: "X \<in> paper_powerset_fiber arrows source (source f)"
  show "paper_powerset_transport arrows source target compose (compose g f) X =
    paper_powerset_transport arrows source target compose g
      (paper_powerset_transport arrows source target compose f X)"
    by (rule paper_powerset_transport_compose[OF first second meeting])
qed

interpretation Powerset: paper_action objects arrows source target compose identity
  "paper_powerset_fiber arrows source" "paper_powerset_transport arrows source target compose"
  by (rule paper_powerset_action)

end

end
