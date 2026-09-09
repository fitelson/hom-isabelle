theory Bacon_Source_Relational_Hull_Cardinal_Bounds
  imports Bacon_Source_Relational_Hull_Cardinal_Stages
    Bacon_Source_Relational_Separating_Hull_Stages
begin

section \<open>Original proposition bounds control the generated separating hull\<close>

context paper_R_separating_hull
begin

lemma paper_R_hull_stage_prop_subset:
  assumes fibers: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Prop \<subseteq> U"
    and member: "M \<in> stage_objects n"
  shows "paper_bbk_domain M Prop \<subseteq> U"
  by (rule fibers[OF subsetD[OF paper_R_hull_stage_objects_original member]])

theorem paper_R_hull_stage_arrows_cardinal_bound:
  assumes infinite: "infinite U"
    and fibers: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Prop \<subseteq> U"
  shows "card_of (stage_arrows n) \<le>o card_of U"
  by (rule paper_R_separating_stage_arrows_cardinal_bound[
    where Arrows=arrows and Root=Root and U=U and n=n,
    OF infinite paper_R_hull_stage_prop_subset[OF fibers]])

theorem paper_R_hull_stage_objects_cardinal_bound:
  assumes infinite: "infinite U"
    and fibers: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Prop \<subseteq> U"
  shows "card_of (stage_objects n) \<le>o card_of U"
  by (rule paper_R_separating_stage_objects_cardinal_bound[
    where Arrows=arrows and Root=Root and U=U and n=n,
    OF infinite paper_R_hull_stage_prop_subset[OF fibers]])

theorem paper_R_hull_arrows_cardinal_bound:
  assumes infinite: "infinite U"
    and fibers: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Prop \<subseteq> U"
  shows "card_of hull_arrows \<le>o card_of U"
  by (rule paper_R_separating_hull_arrows_cardinal_bound[
    where Arrows=arrows and Root=Root and U=U,
    OF infinite paper_R_hull_stage_prop_subset[OF fibers]])

theorem paper_R_hull_objects_cardinal_bound:
  assumes infinite: "infinite U"
    and fibers: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Prop \<subseteq> U"
  shows "card_of hull_objects \<le>o card_of U"
  by (rule paper_R_separating_hull_objects_cardinal_bound[
    where Arrows=arrows and Root=Root and U=U,
    OF infinite paper_R_hull_stage_prop_subset[OF fibers]])

corollary paper_R_hull_cardinal_bounds:
  assumes infinite: "infinite U"
    and fibers: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Prop \<subseteq> U"
  shows "card_of hull_arrows \<le>o card_of U \<and> card_of hull_objects \<le>o card_of U"
  by (rule conjI[OF paper_R_hull_arrows_cardinal_bound[OF infinite fibers]
    paper_R_hull_objects_cardinal_bound[OF infinite fibers]])

end

text \<open>
  The separating-hull locale proves that every generated stage
  remains in the original selected R category. Therefore a bound
  Dₜ(M)⊆U on original objects supplies exactly the input required
  by the raw cardinal induction. Other type domains need no new
  bound for this counting argument.

  The result counts selected records and arrows, not all objects
  or all maps of their ambient HOL types. Category and separator
  assumptions justify the chosen hull; no countability assumption
  or concrete encoding of those ambient types is introduced.
  Source role: the size-controlled categorical representation
  following the fixed-carrier construction on p.52.
\<close>

end
