theory Bacon_Source_Relational_Separating_Hull_Stages
  imports Bacon_Source_Relational_Separating_Hull_Monotonicity
begin

locale paper_R_separating_hull =
  fixes signature :: "'c ssignature" and stock :: sgcontext
    and objects :: "('c,'v) paper_bbk_model_data set" and arrows :: "('c,'v) paper_R_bbk_arrow set"
    and Root :: "('c,'v) paper_bbk_model_data"
  assumes original_category: "paper_R_bbk_subcategory signature stock objects arrows"
    and root_object: "Root \<in> objects"
    and separators: "\<And>M p q. M \<in> objects \<Longrightarrow> p \<in> paper_bbk_domain M Prop \<Longrightarrow>
      q \<in> paper_bbk_domain M Prop \<Longrightarrow> p \<noteq> q \<Longrightarrow>
      \<exists>r\<in>arrows. paper_arrow_source r = M \<and>
        paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop p) \<noteq>
        paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop q)"
begin

sublocale Original: paper_category objects arrows paper_arrow_source paper_arrow_target
  "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
  by (rule paper_R_bbk_subcategory_category[OF original_category])

abbreviation stage_arrows where "stage_arrows \<equiv> paper_R_separating_stage_arrows arrows Root"
abbreviation stage_objects where "stage_objects \<equiv> paper_R_separating_stage_objects arrows Root"
abbreviation hull_arrows where "hull_arrows \<equiv> paper_R_separating_hull_arrows arrows Root"
abbreviation hull_objects where "hull_objects \<equiv> paper_R_separating_hull_objects arrows Root"

lemma paper_R_hull_endpoints_original:
  assumes subset: "S \<subseteq> arrows"
  shows "paper_R_arrow_endpoints S \<subseteq> objects"
  using subset Original.source_object Original.target_object
  by (auto simp: paper_R_arrow_endpoints_def)

lemma paper_R_hull_chosen_separator:
  assumes object: "M \<in> objects" and pm: "p \<in> paper_bbk_domain M Prop"
    and qm: "q \<in> paper_bbk_domain M Prop" and different: "p \<noteq> q"
  shows "paper_R_chosen_separator arrows M p q \<in> arrows \<and>
    paper_arrow_source (paper_R_chosen_separator arrows M p q) = M \<and>
    paper_bbk_valuation (paper_arrow_target (paper_R_chosen_separator arrows M p q))
      (paper_arrow_map (paper_R_chosen_separator arrows M p q) Prop p) \<noteq>
    paper_bbk_valuation (paper_arrow_target (paper_R_chosen_separator arrows M p q))
      (paper_arrow_map (paper_R_chosen_separator arrows M p q) Prop q)"
  by (rule paper_R_chosen_separator_spec[OF separators[OF object pm qm different]])

lemma paper_R_hull_separator_choices_original:
  assumes subset: "S \<subseteq> objects"
  shows "paper_R_separator_choices arrows S \<subseteq> arrows"
proof
  fix r
  assume member: "r \<in> paper_R_separator_choices arrows S"
  obtain M p q where object: "M \<in> S" and pm: "p \<in> paper_bbk_domain M Prop"
    and qm: "q \<in> paper_bbk_domain M Prop" and different: "p \<noteq> q" and shape: "r = paper_R_chosen_separator arrows M p q"
    by (rule paper_R_separator_choicesE[OF member])
  show "r \<in> arrows" by (simp only: shape;
    rule conjunct1[OF paper_R_hull_chosen_separator[OF subsetD[OF subset object] pm qm different]])
qed

lemma paper_R_hull_composites_original:
  assumes subset: "S \<subseteq> arrows"
  shows "paper_R_hull_composites S \<subseteq> arrows"
proof
  fix r
  assume member: "r \<in> paper_R_hull_composites S"
  obtain f g where first: "f \<in> S" and second: "g \<in> S"
    and meeting: "paper_arrow_target f = paper_arrow_source g"
    and shape: "r = paper_typed_compose paper_bbk_domain g f"
    using member unfolding paper_R_hull_composites_def paper_R_hull_composable_pairs_def by auto
  show "r \<in> arrows" by (simp only: shape;
    rule Original.compose_arrow[OF subsetD[OF subset first] subsetD[OF subset second] meeting])
qed

theorem paper_R_hull_stage_arrows_original:
  "stage_arrows n \<subseteq> arrows"
proof (induction n)
  case 0
  show ?case using Original.identity_arrow[OF root_object] by simp
next
  case (Suc n)
  have endpoints: "paper_R_arrow_endpoints (stage_arrows n) \<subseteq> objects"
    by (rule paper_R_hull_endpoints_original[OF Suc.IH])
  have identities: "paper_typed_identity paper_bbk_domain ` paper_R_arrow_endpoints (stage_arrows n) \<subseteq> arrows"
    using endpoints Original.identity_arrow by auto
  have selected: "paper_R_separator_choices arrows (paper_R_arrow_endpoints (stage_arrows n)) \<subseteq> arrows"
    by (rule paper_R_hull_separator_choices_original[OF endpoints])
  have composites: "paper_R_hull_composites (stage_arrows n) \<subseteq> arrows"
    by (rule paper_R_hull_composites_original[OF Suc.IH])
  show ?case using Suc.IH identities selected composites by auto
qed

theorem paper_R_hull_stage_objects_original:
  "stage_objects n \<subseteq> objects"
  unfolding paper_R_separating_stage_objects_def
  by (rule paper_R_hull_endpoints_original[OF paper_R_hull_stage_arrows_original])

theorem paper_R_hull_arrows_original:
  "hull_arrows \<subseteq> arrows"
  using paper_R_hull_stage_arrows_original unfolding paper_R_separating_hull_arrows_def by blast

theorem paper_R_hull_objects_original:
  "hull_objects \<subseteq> objects"
  using paper_R_hull_stage_objects_original unfolding paper_R_separating_hull_objects_def by blast

end

text \<open>
  The source category and the separating-arrow callback justify every
  chosen arrow. All stages remain inside that category. No cardinal,
  countability, inherited intensionality, or premodel assumption is used.
\<close>

end
