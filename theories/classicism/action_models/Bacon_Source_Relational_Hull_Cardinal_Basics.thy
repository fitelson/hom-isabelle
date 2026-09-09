theory Bacon_Source_Relational_Hull_Cardinal_Basics
  imports Bacon_Source_Relational_Separating_Hull_Syntax
    "HOL-Cardinals.Cardinal_Order_Relation"
begin

section \<open>Cardinal bounds for the individual hull operations\<close>

lemma paper_R_hull_singleton_cardinal_bound:
  assumes nonempty: "U \<noteq> {}"
  shows "card_of {a} \<le>o card_of U"
proof -
  obtain u where member: "u \<in> U" using nonempty by blast
  show ?thesis by (rule card_of_ordLeqI[where f="\<lambda>_. u"]; auto simp: member)
qed

lemma paper_R_hull_endpoints_cardinal_bound:
  assumes infinite: "infinite U" and arrows: "card_of S \<le>o card_of U"
  shows "card_of (paper_R_arrow_endpoints S) \<le>o card_of U"
proof -
  have sources: "card_of (image paper_arrow_source S) \<le>o card_of U"
    by (rule ordLeq_transitive[OF card_of_image arrows])
  have targets: "card_of (image paper_arrow_target S) \<le>o card_of U"
    by (rule ordLeq_transitive[OF card_of_image arrows])
  show ?thesis unfolding paper_R_arrow_endpoints_def
    by (rule card_of_Un_ordLeq_infinite[OF infinite sources targets])
qed

lemma paper_R_hull_separator_indices_subset:
  assumes fibers: "\<And>M. M \<in> Obj \<Longrightarrow> paper_bbk_domain M Prop \<subseteq> U"
  shows "paper_R_separator_indices Obj \<subseteq> Obj \<times> (U \<times> U)"
  using fibers by (auto simp: paper_R_separator_indices_def)

lemma paper_R_hull_separator_indices_cardinal_bound:
  assumes infinite: "infinite U" and objects: "card_of Obj \<le>o card_of U"
    and fibers: "\<And>M. M \<in> Obj \<Longrightarrow> paper_bbk_domain M Prop \<subseteq> U"
  shows "card_of (paper_R_separator_indices Obj) \<le>o card_of U"
proof -
  have reflexive: "card_of U \<le>o card_of U" by (rule card_of_mono1[OF subset_refl])
  have pairs: "card_of (U \<times> U) \<le>o card_of U"
    by (rule card_of_Times_ordLeq_infinite[OF infinite reflexive reflexive])
  have triples: "card_of (Obj \<times> (U \<times> U)) \<le>o card_of U"
    by (rule card_of_Times_ordLeq_infinite[OF infinite objects pairs])
  have subset: "paper_R_separator_indices Obj \<subseteq> Obj \<times> (U \<times> U)"
    by (rule paper_R_hull_separator_indices_subset[OF fibers])
  show ?thesis by (rule ordLeq_transitive[OF card_of_mono1[OF subset] triples])
qed

lemma paper_R_hull_separator_choices_cardinal_bound:
  assumes infinite: "infinite U" and objects: "card_of Obj \<le>o card_of U"
    and fibers: "\<And>M. M \<in> Obj \<Longrightarrow> paper_bbk_domain M Prop \<subseteq> U"
  shows "card_of (paper_R_separator_choices Arrows Obj) \<le>o card_of U"
  unfolding paper_R_separator_choices_def
  by (rule ordLeq_transitive[OF card_of_image
    paper_R_hull_separator_indices_cardinal_bound[OF infinite objects fibers]])

lemma paper_R_hull_composable_pairs_subset:
  "paper_R_hull_composable_pairs S \<subseteq> S \<times> S"
  by (auto simp: paper_R_hull_composable_pairs_def)

lemma paper_R_hull_composable_pairs_cardinal_bound:
  assumes infinite: "infinite U" and arrows: "card_of S \<le>o card_of U"
  shows "card_of (paper_R_hull_composable_pairs S) \<le>o card_of U"
proof -
  have pairs: "card_of (S \<times> S) \<le>o card_of U"
    by (rule card_of_Times_ordLeq_infinite[OF infinite arrows arrows])
  show ?thesis by (rule ordLeq_transitive[
    OF card_of_mono1[OF paper_R_hull_composable_pairs_subset] pairs])
qed

lemma paper_R_hull_composites_cardinal_bound:
  assumes infinite: "infinite U" and arrows: "card_of S \<le>o card_of U"
  shows "card_of (paper_R_hull_composites S) \<le>o card_of U"
  unfolding paper_R_hull_composites_def
  by (rule ordLeq_transitive[OF card_of_image
    paper_R_hull_composable_pairs_cardinal_bound[OF infinite arrows]])

text \<open>
  Endpoints and selected arrows are images of already bounded sets.
  Separators use only indices (M,p,q) in Obj×U×U, and composites
  use a subset of S×S. These cardinal facts need no category,
  existence of separating arrows, model validity or countability
  of the ambient record types. The chosen functions are bounded
  by their indexing sets even before their semantic specifications
  are invoked. Source role: a size-controlled selected category
  supporting the bounded construction of pp.51–52.
\<close>

end
