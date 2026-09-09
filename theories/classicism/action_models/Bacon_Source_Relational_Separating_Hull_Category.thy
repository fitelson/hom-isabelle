theory Bacon_Source_Relational_Separating_Hull_Category
  imports Bacon_Source_Relational_Separating_Hull_Stages
begin

section \<open>The union is an actual selected R category\<close>

context paper_R_separating_hull
begin

lemma paper_R_hull_identity:
  assumes object: "M \<in> hull_objects"
  shows "paper_typed_identity paper_bbk_domain M \<in> hull_arrows"
proof -
  obtain n where stage: "M \<in> stage_objects n" using object unfolding paper_R_separating_hull_objects_def by blast
  have successor_member: "paper_typed_identity paper_bbk_domain M \<in> stage_arrows (Suc n)"
    by (rule paper_R_separating_stage_identity[OF stage])
  show ?thesis by (rule subsetD[OF paper_R_separating_stage_arrows_in_hull successor_member])
qed

lemma paper_R_hull_compose:
  assumes first: "f \<in> hull_arrows" and second: "g \<in> hull_arrows" and meeting: "paper_arrow_target f = paper_arrow_source g"
  shows "paper_typed_compose paper_bbk_domain g f \<in> hull_arrows"
proof -
  obtain j where fj: "f \<in> stage_arrows j" using first unfolding paper_R_separating_hull_arrows_def by blast
  obtain k where gk: "g \<in> stage_arrows k" using second unfolding paper_R_separating_hull_arrows_def by blast
  have j_le: "j \<le> max j k" and k_le: "k \<le> max j k" by simp_all
  have fm: "f \<in> stage_arrows (max j k)"
    by (rule subsetD[OF paper_R_separating_stage_arrows_mono[OF j_le] fj])
  have gm: "g \<in> stage_arrows (max j k)"
    by (rule subsetD[OF paper_R_separating_stage_arrows_mono[OF k_le] gk])
  have successor_member: "paper_typed_compose paper_bbk_domain g f \<in> stage_arrows (Suc (max j k))"
    by (rule paper_R_separating_stage_compose[OF fm gm meeting])
  show ?thesis by (rule subsetD[OF paper_R_separating_stage_arrows_in_hull successor_member])
qed

theorem paper_R_hull_subcategory:
  "paper_R_bbk_subcategory signature stock hull_objects hull_arrows"
proof (unfold paper_R_bbk_subcategory_def, intro conjI)
  show "\<forall>M\<in>hull_objects. paper_R_bbk_data_valid signature stock M"
    by (intro ballI; rule paper_R_bbk_subcategory_models[OF original_category
      subsetD[OF paper_R_hull_objects_original]]; assumption)
next
  show "hull_arrows \<subseteq> paper_R_bbk_arrows signature stock hull_objects"
  proof
    fix r
    assume member: "r \<in> hull_arrows"
    have original: "r \<in> arrows" by (rule subsetD[OF paper_R_hull_arrows_original member])
    have full: "r \<in> paper_R_bbk_arrows signature stock objects"
      by (rule paper_R_bbk_subcategory_arrow[OF original_category original])
    have typed: "r \<in> paper_typed_arrows objects paper_bbk_domain" by (rule paper_R_bbk_arrows_typed[OF full])
    have src: "paper_arrow_source r \<in> hull_objects" and tgt: "paper_arrow_target r \<in> hull_objects"
      using member by (auto simp only: paper_R_separating_hull_endpoints paper_R_arrow_endpoints_def)
    have restricted: "r \<in> paper_typed_arrows hull_objects paper_bbk_domain"
      using typed src tgt unfolding paper_typed_arrows_def by blast
    show "r \<in> paper_R_bbk_arrows signature stock hull_objects"
      by (rule paper_R_bbk_arrowsI[OF restricted paper_R_bbk_arrows_morphism[OF full]])
  qed
next
  show "\<forall>M\<in>hull_objects. paper_typed_identity paper_bbk_domain M \<in> hull_arrows"
    by (intro ballI; rule paper_R_hull_identity; assumption)
next
  show "\<forall>f\<in>hull_arrows. \<forall>g\<in>hull_arrows. paper_arrow_target f = paper_arrow_source g \<longrightarrow>
    paper_typed_compose paper_bbk_domain g f \<in> hull_arrows"
    by (intro ballI impI; rule paper_R_hull_compose; assumption)
qed

theorem paper_R_hull_category:
  "paper_category hull_objects hull_arrows paper_arrow_source paper_arrow_target
    (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)"
  by (rule paper_R_bbk_subcategory_category[OF paper_R_hull_subcategory])

section \<open>Separators are retained, so quasi-Fregeanness is proved anew\<close>

theorem paper_R_hull_separating_arrow:
  assumes object: "M \<in> hull_objects" and pm: "p \<in> paper_bbk_domain M Prop"
    and qm: "q \<in> paper_bbk_domain M Prop" and different: "p \<noteq> q"
  obtains r where "r \<in> hull_arrows" "paper_arrow_source r = M"
    "paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop p) \<noteq>
      paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop q)"
proof -
  note finish = that
  obtain n where stage: "M \<in> stage_objects n" using object unfolding paper_R_separating_hull_objects_def by blast
  have original: "M \<in> objects" by (rule subsetD[OF paper_R_hull_objects_original object])
  let ?r = "paper_R_chosen_separator arrows M p q"
  have chosen: "?r \<in> arrows \<and> paper_arrow_source ?r = M \<and>
      paper_bbk_valuation (paper_arrow_target ?r) (paper_arrow_map ?r Prop p) \<noteq>
      paper_bbk_valuation (paper_arrow_target ?r) (paper_arrow_map ?r Prop q)"
    by (rule paper_R_hull_chosen_separator[OF original pm qm different])
  have successor_member: "?r \<in> stage_arrows (Suc n)" by (rule paper_R_separating_stage_separator[OF stage pm qm different])
  have member: "?r \<in> hull_arrows" by (rule subsetD[OF paper_R_separating_stage_arrows_in_hull successor_member])
  have src: "paper_arrow_source ?r = M" and separates: "paper_bbk_valuation (paper_arrow_target ?r) (paper_arrow_map ?r Prop p) \<noteq>
      paper_bbk_valuation (paper_arrow_target ?r) (paper_arrow_map ?r Prop q)" using chosen by blast+
  show thesis by (rule finish[OF member src separates])
qed

theorem paper_R_hull_quasi_fregean:
  "paper_bbk_quasi_fregean_on hull_objects hull_arrows"
proof (unfold paper_bbk_quasi_fregean_on_def, intro ballI)
  fix M
  assume object: "M \<in> hull_objects"
  show "inj_on (paper_bbk_truth_profile_on hull_arrows M) (paper_bbk_domain M Prop)"
  proof (rule inj_onI)
    fix p q
    assume pm: "p \<in> paper_bbk_domain M Prop" and qm: "q \<in> paper_bbk_domain M Prop"
      and profiles: "paper_bbk_truth_profile_on hull_arrows M p = paper_bbk_truth_profile_on hull_arrows M q"
    show "p = q"
    proof (rule ccontr)
      assume different: "p \<noteq> q"
      obtain r where arrow: "r \<in> hull_arrows" and src: "paper_arrow_source r = M"
        and separates: "paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop p) \<noteq>
          paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop q)"
        by (rule paper_R_hull_separating_arrow[OF object pm qm different])
      have same: "paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop p) =
          paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop q)"
        using iffD1[OF paper_bbk_truth_profile_on_eq_iff profiles] arrow src by blast
      show False using separates same by contradiction
    qed
  qed
qed

end

text \<open>
  Root belongs to the hull by its initial identity arrow. The category
  and quasi-Fregean properties are actual conclusions. Intensionality
  is not inherited by deleting arrows, nor asserted here; a later use
  of Modalized Functionality must establish quasi-functionality.
  Cardinal bounds and reachability are likewise separate obligations.
\<close>

end
