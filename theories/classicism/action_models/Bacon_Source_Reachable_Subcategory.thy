theory Bacon_Source_Reachable_Subcategory
  imports Bacon_Source_Powerset_Action
begin

section \<open>The full subcategory on objects reachable from a root\<close>

text \<open>
  Given R∈𝒞, retain objects B admitting an original arrow R→B,
  and retain every ORIGINAL arrow between retained objects.
  Source role: the category conventions of Bacon–Dorr §3.3,
  pp.49–50, and rooted restrictions used in the action-model setting.

  Full here means full relative to the supplied arrow set. It does
  not add all possible BBK homomorphisms or replace a chosen arrow
  collection by a larger one. Reachability uses one existing arrow;
  composition ensures closure under further arrows. All sets may be
  infinite. No uniqueness of arrows out of R is asserted.
\<close>

definition paper_reachable_objects :: "'a set \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> 'o set" where
  "paper_reachable_objects arrows source target R = {B. \<exists>h\<in>arrows. source h = R \<and> target h = B}"

definition paper_reachable_arrows :: "'a set \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> 'a set" where
  "paper_reachable_arrows arrows source target R = {h\<in>arrows.
    source h \<in> paper_reachable_objects arrows source target R \<and>
    target h \<in> paper_reachable_objects arrows source target R}"

lemma paper_reachable_objectsI:
  "h \<in> arrows \<Longrightarrow> source h = R \<Longrightarrow> target h = B \<Longrightarrow>
    B \<in> paper_reachable_objects arrows source target R"
  unfolding paper_reachable_objects_def by blast

lemma paper_reachable_objectsE:
  assumes member: "B \<in> paper_reachable_objects arrows source target R"
  obtains h where "h \<in> arrows" "source h = R" "target h = B"
  using member that unfolding paper_reachable_objects_def by blast

lemma paper_reachable_arrows_member:
  "h \<in> paper_reachable_arrows arrows source target R \<longleftrightarrow>
    h \<in> arrows \<and> source h \<in> paper_reachable_objects arrows source target R \<and>
    target h \<in> paper_reachable_objects arrows source target R"
  by (simp only: paper_reachable_arrows_def mem_Collect_eq)

lemma paper_reachable_arrows_original:
  "h \<in> paper_reachable_arrows arrows source target R \<Longrightarrow> h \<in> arrows"
  by (simp only: paper_reachable_arrows_member; blast)

context paper_category
begin

lemma paper_reachable_object_original:
  assumes reachable: "B \<in> paper_reachable_objects arrows source target R"
  shows "B \<in> objects"
proof -
  obtain h where arrow: "h \<in> arrows" and finish: "target h = B"
    by (rule paper_reachable_objectsE[OF reachable]; rule that; assumption)
  show ?thesis using target_object[OF arrow] by (simp only: finish)
qed

lemma paper_reachable_root:
  assumes root: "R \<in> objects"
  shows "R \<in> paper_reachable_objects arrows source target R"
  by (rule paper_reachable_objectsI[where source=source and target=target and h="identity R",
    OF identity_arrow[OF root] identity_source[OF root] identity_target[OF root]])

lemma paper_reachable_target:
  assumes reachable: "source f \<in> paper_reachable_objects arrows source target R"
    and arrow: "f \<in> arrows"
  shows "target f \<in> paper_reachable_objects arrows source target R"
proof -
  obtain h where ha: "h \<in> arrows" and hs: "source h = R" and ht: "target h = source f"
    by (rule paper_reachable_objectsE[OF reachable])
  have composite: "compose f h \<in> arrows" by (rule compose_arrow[OF ha arrow ht])
  have origin: "source (compose f h) = R" by (simp only: compose_source[OF ha arrow ht] hs)
  have finish: "target (compose f h) = target f" by (rule compose_target[OF ha arrow ht])
  show ?thesis by (rule paper_reachable_objectsI[where source=source and target=target and h="compose f h",
    OF composite origin finish])
qed

lemma paper_reachable_outgoing_retained:
  assumes arrow: "f \<in> arrows" and reachable: "source f \<in> paper_reachable_objects arrows source target R"
  shows "f \<in> paper_reachable_arrows arrows source target R"
  by (simp only: paper_reachable_arrows_member;
    rule conjI[OF arrow conjI[OF reachable paper_reachable_target[OF reachable arrow]]])

lemma paper_reachable_outgoing_equal:
  assumes reachable: "B \<in> paper_reachable_objects arrows source target R"
  shows "paper_outgoing (paper_reachable_arrows arrows source target R) source B =
    paper_outgoing arrows source B"
proof (rule set_eqI)
  fix f
  show "(f \<in> paper_outgoing (paper_reachable_arrows arrows source target R) source B) =
    (f \<in> paper_outgoing arrows source B)"
  proof
    assume member: "f \<in> paper_outgoing (paper_reachable_arrows arrows source target R) source B"
    show "f \<in> paper_outgoing arrows source B"
      using member by (auto simp only: paper_outgoing_member paper_reachable_arrows_member)
  next
    assume member: "f \<in> paper_outgoing arrows source B"
    have arrow: "f \<in> arrows" and origin: "source f = B" using member by (auto simp only: paper_outgoing_member)
    have retained: "f \<in> paper_reachable_arrows arrows source target R"
      by (rule paper_reachable_outgoing_retained[OF arrow]; simp only: origin; rule reachable)
    show "f \<in> paper_outgoing (paper_reachable_arrows arrows source target R) source B"
      by (simp only: paper_outgoing_member; rule conjI[OF retained origin])
  qed
qed

lemma paper_reachable_root_arrow:
  assumes root: "R \<in> objects" and reachable: "B \<in> paper_reachable_objects arrows source target R"
  obtains h where "h \<in> paper_reachable_arrows arrows source target R" "source h = R" "target h = B"
proof -
  obtain h where arrow: "h \<in> arrows" and origin: "source h = R" and finish: "target h = B"
    by (rule paper_reachable_objectsE[OF reachable])
  have retained: "h \<in> paper_reachable_arrows arrows source target R"
    by (rule paper_reachable_outgoing_retained[OF arrow]; simp only: origin; rule paper_reachable_root[OF root])
  show thesis by (rule that[OF retained origin finish])
qed

theorem paper_reachable_root_weak_initial:
  assumes root: "R \<in> objects"
  shows "\<forall>B\<in>paper_reachable_objects arrows source target R.
    \<exists>h\<in>paper_reachable_arrows arrows source target R. source h = R \<and> target h = B"
proof (intro ballI)
  fix B
  assume reachable: "B \<in> paper_reachable_objects arrows source target R"
  obtain h where arrow: "h \<in> paper_reachable_arrows arrows source target R"
    and origin: "source h = R" and finish: "target h = B"
    by (rule paper_reachable_root_arrow[OF root reachable])
  show "\<exists>h\<in>paper_reachable_arrows arrows source target R. source h = R \<and> target h = B"
    by (rule bexI[where x=h], rule conjI[OF origin finish], rule arrow)
qed

end

end
