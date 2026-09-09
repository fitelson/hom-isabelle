theory Bacon_Source_Relational_Separating_Hull_Monotonicity
  imports Bacon_Source_Relational_Separating_Hull_Syntax
begin

lemma paper_R_arrow_endpoints_mono:
  "S \<subseteq> T \<Longrightarrow> paper_R_arrow_endpoints S \<subseteq> paper_R_arrow_endpoints T"
  unfolding paper_R_arrow_endpoints_def by blast

lemma paper_R_separating_stage_objects_zero:
  "paper_R_separating_stage_objects Arrows Root 0 = {Root}"
  by (simp add: paper_R_separating_stage_objects_def paper_R_arrow_endpoints_def)

lemma paper_R_separating_stage_step:
  "paper_R_separating_stage_arrows Arrows Root n \<subseteq> paper_R_separating_stage_arrows Arrows Root (Suc n)"
  by auto

theorem paper_R_separating_stage_arrows_mono:
  assumes order: "n \<le> m"
  shows "paper_R_separating_stage_arrows Arrows Root n \<subseteq> paper_R_separating_stage_arrows Arrows Root m"
  using order
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases "n = Suc m")
    case True
    then show ?thesis by simp
  next
    case False
    have earlier: "n \<le> m" using Suc.prems False by arith
    show ?thesis by (rule subset_trans[OF Suc.IH[OF earlier] paper_R_separating_stage_step])
  qed
qed

theorem paper_R_separating_stage_objects_mono:
  assumes order: "n \<le> m"
  shows "paper_R_separating_stage_objects Arrows Root n \<subseteq> paper_R_separating_stage_objects Arrows Root m"
  unfolding paper_R_separating_stage_objects_def
  by (rule paper_R_arrow_endpoints_mono[OF paper_R_separating_stage_arrows_mono[OF order]])

lemma paper_R_separating_stage_arrows_in_hull:
  "paper_R_separating_stage_arrows Arrows Root n \<subseteq> paper_R_separating_hull_arrows Arrows Root"
  unfolding paper_R_separating_hull_arrows_def by blast

lemma paper_R_separating_stage_objects_in_hull:
  "paper_R_separating_stage_objects Arrows Root n \<subseteq> paper_R_separating_hull_objects Arrows Root"
  unfolding paper_R_separating_hull_objects_def by blast

lemma paper_R_separating_hull_root:
  "Root \<in> paper_R_separating_hull_objects Arrows Root"
proof -
  have initial: "Root \<in> paper_R_separating_stage_objects Arrows Root 0"
    by (simp only: paper_R_separating_stage_objects_zero; simp)
  show ?thesis by (rule subsetD[OF paper_R_separating_stage_objects_in_hull initial])
qed

lemma paper_R_separating_hull_endpoints:
  "paper_R_separating_hull_objects Arrows Root = paper_R_arrow_endpoints (paper_R_separating_hull_arrows Arrows Root)"
  by (auto simp: paper_R_separating_hull_objects_def paper_R_separating_hull_arrows_def
    paper_R_separating_stage_objects_def paper_R_arrow_endpoints_def)

lemma paper_R_separating_stage_identity:
  assumes object: "M \<in> paper_R_separating_stage_objects Arrows Root n"
  shows "paper_typed_identity paper_bbk_domain M \<in> paper_R_separating_stage_arrows Arrows Root (Suc n)"
  using object unfolding paper_R_separating_stage_objects_def by auto

lemma paper_R_separating_stage_separator:
  assumes object: "M \<in> paper_R_separating_stage_objects Arrows Root n"
    and pm: "p \<in> paper_bbk_domain M Prop" and qm: "q \<in> paper_bbk_domain M Prop" and different: "p \<noteq> q"
  shows "paper_R_chosen_separator Arrows M p q \<in> paper_R_separating_stage_arrows Arrows Root (Suc n)"
proof -
  have selected: "paper_R_chosen_separator Arrows M p q \<in>
      paper_R_separator_choices Arrows (paper_R_arrow_endpoints (paper_R_separating_stage_arrows Arrows Root n))"
    by (rule paper_R_separator_choicesI[OF object[unfolded paper_R_separating_stage_objects_def] pm qm different])
  show ?thesis using selected by auto
qed

lemma paper_R_separating_stage_compose:
  assumes first: "f \<in> paper_R_separating_stage_arrows Arrows Root n"
    and second: "g \<in> paper_R_separating_stage_arrows Arrows Root n" and meeting: "paper_arrow_target f = paper_arrow_source g"
  shows "paper_typed_compose paper_bbk_domain g f \<in> paper_R_separating_stage_arrows Arrows Root (Suc n)"
proof -
  have pair: "(f,g) \<in> paper_R_hull_composable_pairs (paper_R_separating_stage_arrows Arrows Root n)"
    using first second meeting by (simp add: paper_R_hull_composable_pairs_def)
  have composite: "paper_typed_compose paper_bbk_domain g f \<in> paper_R_hull_composites (paper_R_separating_stage_arrows Arrows Root n)"
    unfolding paper_R_hull_composites_def
    by (rule image_eqI[where x="(f,g)"]; (simp | rule pair))
  show ?thesis using composite by auto
qed

end
