theory Bacon_Source_Relational_Hull_Cardinal_Stages
  imports Bacon_Source_Relational_Hull_Cardinal_Basics
begin

section \<open>The stage and union bounds follow the actual hull recursion\<close>

theorem paper_R_separating_stage_arrows_cardinal_bound:
  assumes infinite: "infinite U"
    and fibers: "\<And>n M. M \<in> paper_R_separating_stage_objects Arrows Root n \<Longrightarrow>
      paper_bbk_domain M Prop \<subseteq> U"
  shows "card_of (paper_R_separating_stage_arrows Arrows Root n) \<le>o card_of U"
proof (induction n)
  case 0
  have nonempty: "U \<noteq> {}" using infinite by auto
  show ?case by (simp only: paper_R_separating_stage_arrows.simps;
    rule paper_R_hull_singleton_cardinal_bound[OF nonempty])
next
  case (Suc n)
  let ?S = "paper_R_separating_stage_arrows Arrows Root n"
  let ?Obj = "paper_R_arrow_endpoints ?S"
  have objects: "card_of ?Obj \<le>o card_of U"
    by (rule paper_R_hull_endpoints_cardinal_bound[OF infinite Suc.IH])
  have identities: "card_of (image (paper_typed_identity paper_bbk_domain) ?Obj) \<le>o card_of U"
    by (rule ordLeq_transitive[OF card_of_image objects])
  have stage_fibers: "paper_bbk_domain M Prop \<subseteq> U" if "M \<in> ?Obj" for M
    by (rule fibers[where n=n]; use that in \<open>simp only: paper_R_separating_stage_objects_def\<close>)
  have separators: "card_of (paper_R_separator_choices Arrows ?Obj) \<le>o card_of U"
    by (rule paper_R_hull_separator_choices_cardinal_bound[OF infinite objects stage_fibers])
  have composites: "card_of (paper_R_hull_composites ?S) \<le>o card_of U"
    by (rule paper_R_hull_composites_cardinal_bound[OF infinite Suc.IH])
  have first_union: "card_of (?S \<union> image (paper_typed_identity paper_bbk_domain) ?Obj) \<le>o card_of U"
    by (rule card_of_Un_ordLeq_infinite[OF infinite Suc.IH identities])
  have second_union: "card_of (?S \<union> image (paper_typed_identity paper_bbk_domain) ?Obj \<union>
      paper_R_separator_choices Arrows ?Obj) \<le>o card_of U"
    by (rule card_of_Un_ordLeq_infinite[OF infinite first_union separators])
  show ?case by (simp only: paper_R_separating_stage_arrows.simps;
    rule card_of_Un_ordLeq_infinite[OF infinite second_union composites])
qed

theorem paper_R_separating_stage_objects_cardinal_bound:
  assumes infinite: "infinite U"
    and fibers: "\<And>n M. M \<in> paper_R_separating_stage_objects Arrows Root n \<Longrightarrow>
      paper_bbk_domain M Prop \<subseteq> U"
  shows "card_of (paper_R_separating_stage_objects Arrows Root n) \<le>o card_of U"
  unfolding paper_R_separating_stage_objects_def
  by (rule paper_R_hull_endpoints_cardinal_bound[
    OF infinite paper_R_separating_stage_arrows_cardinal_bound[OF infinite fibers]])

theorem paper_R_separating_hull_arrows_cardinal_bound:
  assumes infinite: "infinite U"
    and fibers: "\<And>n M. M \<in> paper_R_separating_stage_objects Arrows Root n \<Longrightarrow>
      paper_bbk_domain M Prop \<subseteq> U"
  shows "card_of (paper_R_separating_hull_arrows Arrows Root) \<le>o card_of U"
proof -
  have naturals: "card_of (UNIV :: nat set) \<le>o card_of U"
    using infinite infinite_iff_card_of_nat by blast
  have stages: "\<forall>n\<in>(UNIV :: nat set).
      card_of (paper_R_separating_stage_arrows Arrows Root n) \<le>o card_of U"
    by (intro ballI; rule paper_R_separating_stage_arrows_cardinal_bound[OF infinite fibers])
  show ?thesis unfolding paper_R_separating_hull_arrows_def
    by (rule card_of_UNION_ordLeq_infinite[OF infinite naturals stages])
qed

theorem paper_R_separating_hull_objects_cardinal_bound:
  assumes infinite: "infinite U"
    and fibers: "\<And>n M. M \<in> paper_R_separating_stage_objects Arrows Root n \<Longrightarrow>
      paper_bbk_domain M Prop \<subseteq> U"
  shows "card_of (paper_R_separating_hull_objects Arrows Root) \<le>o card_of U"
proof -
  have naturals: "card_of (UNIV :: nat set) \<le>o card_of U"
    using infinite infinite_iff_card_of_nat by blast
  have stages: "\<forall>n\<in>(UNIV :: nat set).
      card_of (paper_R_separating_stage_objects Arrows Root n) \<le>o card_of U"
    by (intro ballI; rule paper_R_separating_stage_objects_cardinal_bound[OF infinite fibers])
  show ?thesis unfolding paper_R_separating_hull_objects_def
    by (rule card_of_UNION_ordLeq_infinite[OF infinite naturals stages])
qed

text \<open>
  Stage zero is the singleton identity arrow. At each successor,
  the old arrows, endpoint identities, separator choices and pairwise
  composites each have cardinal at most |U|. The final arrow and
  object sets are countable unions of these bounded stages.
  Individual stages need not be countable when U is uncountable.
  No code for arbitrary model records is used.
\<close>

end
