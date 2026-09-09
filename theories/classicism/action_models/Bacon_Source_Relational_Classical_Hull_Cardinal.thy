theory Bacon_Source_Relational_Classical_Hull_Cardinal
  imports Bacon_Source_Relational_Hull_Cardinal_Bounds
    Bacon_Source_Relational_Rooted_Separating_Hull
begin

section \<open>The generated and rooted classical hulls have cardinal at most |U|\<close>

context paper_R_classicism_hull
begin

lemma paper_R_classicism_full_prop_subset:
  assumes object: "M \<in> full_objects"
  shows "paper_bbk_domain M Prop \<subseteq> U"
proof -
  have bound: "(\<Union>\<sigma>. paper_bbk_domain M \<sigma>) \<subseteq> U"
    by (rule paper_R_bounded_theory_models_bound[OF object])
  show ?thesis using bound by blast
qed

theorem paper_R_classicism_hull_cardinal_bounds:
  "card_of generated_arrows \<le>o card_of U \<and> card_of generated_objects \<le>o card_of U"
  by (rule Hull.paper_R_hull_cardinal_bounds[OF infinite_bound paper_R_classicism_full_prop_subset])

corollary paper_R_classicism_hull_arrows_cardinal_bound:
  "card_of generated_arrows \<le>o card_of U"
  by (rule conjunct1[OF paper_R_classicism_hull_cardinal_bounds])

corollary paper_R_classicism_hull_objects_cardinal_bound:
  "card_of generated_objects \<le>o card_of U"
  by (rule conjunct2[OF paper_R_classicism_hull_cardinal_bounds])

theorem paper_R_classicism_rooted_arrows_cardinal_bound:
  "card_of rooted_arrows \<le>o card_of U"
  by (rule ordLeq_transitive[
    OF card_of_mono1[OF paper_R_classicism_rooted_arrows_subset]
      paper_R_classicism_hull_arrows_cardinal_bound])

theorem paper_R_classicism_rooted_objects_cardinal_bound:
  "card_of rooted_objects \<le>o card_of U"
  by (rule ordLeq_transitive[
    OF card_of_mono1[OF paper_R_classicism_rooted_objects_subset]
      paper_R_classicism_hull_objects_cardinal_bound])

corollary paper_R_classicism_rooted_cardinal_bounds:
  "card_of rooted_arrows \<le>o card_of U \<and> card_of rooted_objects \<le>o card_of U"
  by (rule conjI[OF paper_R_classicism_rooted_arrows_cardinal_bound
    paper_R_classicism_rooted_objects_cardinal_bound])

end

text \<open>
  Original bounded model objects have their proposition domains in U,
  so the proved hull cardinal induction applies directly. The reachable
  restriction can only decrease the arrow and object sets. These are
  bounds on the selected hulls, not on the full original model category
  or on the ambient HOL record types.
  Source role: the size-controlled rooted input to Proposition 3.22.
\<close>

end
