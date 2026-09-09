theory Bacon_Source_Rooted_Category
  imports Bacon_Source_Category
begin

section \<open>A root has an arrow to every object, not a unique arrow\<close>

text \<open>
  W₀ is a root when W₀ is an object and, for each W, there is
  an arrow W₀→W. Source: Bacon–Dorr p.55, before Definition 3.18.
  This is weak initiality. No uniqueness or selected root arrow
  is included. All root arrows remain available as interpretation
  inputs in Definition 3.19.

  The category is set-indexed, with arbitrary object and arrow
  carriers. This structural interface asserts no logical domains,
  interpretation, BBK model, or action-model existence.
\<close>

locale paper_rooted_category =
  paper_category objects arrows source target compose identity
  for objects :: "'o set" and arrows :: "'a set"
    and source :: "'a \<Rightarrow> 'o" and target :: "'a \<Rightarrow> 'o"
    and compose :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and identity :: "'o \<Rightarrow> 'a" +
  fixes root :: 'o
  assumes root_object: "root \<in> objects"
    and root_reaches: "A \<in> objects \<Longrightarrow> \<exists>h\<in>arrows. source h = root \<and> target h = A"
begin

definition paper_root_arrows :: "'o \<Rightarrow> 'a set" where
  "paper_root_arrows A = {h\<in>arrows. source h = root \<and> target h = A}"

lemma paper_root_arrows_member:
  "h \<in> paper_root_arrows A \<longleftrightarrow> h \<in> arrows \<and> source h = root \<and> target h = A"
  by (simp only: paper_root_arrows_def mem_Collect_eq)

lemma paper_root_arrows_nonempty:
  assumes object: "A \<in> objects"
  shows "paper_root_arrows A \<noteq> {}"
  using root_reaches[OF object] unfolding paper_root_arrows_def by blast

lemma paper_root_arrows_target:
  assumes member: "h \<in> paper_root_arrows A"
  shows "A \<in> objects"
  using member target_object unfolding paper_root_arrows_def by blast

lemma paper_root_identity:
  "identity root \<in> paper_root_arrows root"
  by (simp add: paper_root_arrows_member identity_arrow[OF root_object]
    identity_source[OF root_object] identity_target[OF root_object])

lemma paper_root_arrows_compose:
  assumes first: "h \<in> paper_root_arrows A"
    and second: "i \<in> arrows" and origin: "source i = A"
  shows "compose i h \<in> paper_root_arrows (target i)"
proof -
  have ha: "h \<in> arrows" and hs: "source h = root" and ht: "target h = A"
    using first by (auto simp only: paper_root_arrows_member)
  have meeting: "target h = source i" using ht origin by simp
  show ?thesis
    by (simp only: paper_root_arrows_member compose_arrow[OF ha second meeting]
      compose_source[OF ha second meeting] compose_target[OF ha second meeting] hs; simp)
qed

end

section \<open>The root condition does not imply uniqueness\<close>

text \<open>
  A one-object category with the two-element group as arrows is rooted
  but has two root arrows to its sole object. This is a structural
  regression example, not a BBK or higher-order logical model.
\<close>

lemma paper_two_arrow_rooted_category:
  "paper_rooted_category {()} (UNIV :: bool set)
    (\<lambda>h. ()) (\<lambda>h. ()) (\<lambda>g f. g \<noteq> f) (\<lambda>A. False) ()"
  by unfold_locales auto

theorem paper_root_arrows_need_not_be_unique:
  "paper_rooted_category {()} (UNIV :: bool set)
      (\<lambda>h. ()) (\<lambda>h. ()) (\<lambda>g f. g \<noteq> f) (\<lambda>A. False) () \<and>
    (\<exists>f\<in>(UNIV :: bool set). \<exists>g\<in>UNIV.
      f \<noteq> g \<and> (\<lambda>h. ()) f = () \<and> (\<lambda>h. ()) g = ())"
  by (rule conjI[OF paper_two_arrow_rooted_category],
    rule bexI[where x=False], rule bexI[where x=True]) simp_all

end
