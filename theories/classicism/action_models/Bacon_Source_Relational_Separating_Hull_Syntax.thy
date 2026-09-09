theory Bacon_Source_Relational_Separating_Hull_Syntax
  imports Bacon_Source_Relational_Subcategory Bacon_Source_BBK_Selected_Truth_Profile
begin

section \<open>Chosen separators and the generated arrow stages\<close>

definition paper_R_chosen_separator ::
  "('c,'v) paper_R_bbk_arrow set \<Rightarrow> ('c,'v) paper_bbk_model_data \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('c,'v) paper_R_bbk_arrow" where
  "paper_R_chosen_separator Arrows M p q = (SOME r. r \<in> Arrows \<and> paper_arrow_source r = M \<and>
    paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop p) \<noteq>
    paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop q))"

lemma paper_R_chosen_separator_spec:
  assumes exists: "\<exists>r\<in>Arrows. paper_arrow_source r = M \<and>
    paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop p) \<noteq>
    paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop q)"
  shows "paper_R_chosen_separator Arrows M p q \<in> Arrows \<and>
    paper_arrow_source (paper_R_chosen_separator Arrows M p q) = M \<and>
    paper_bbk_valuation (paper_arrow_target (paper_R_chosen_separator Arrows M p q))
      (paper_arrow_map (paper_R_chosen_separator Arrows M p q) Prop p) \<noteq>
    paper_bbk_valuation (paper_arrow_target (paper_R_chosen_separator Arrows M p q))
      (paper_arrow_map (paper_R_chosen_separator Arrows M p q) Prop q)"
  unfolding paper_R_chosen_separator_def by (rule someI_ex; use exists in blast)

definition paper_R_arrow_endpoints :: "('c,'v) paper_R_bbk_arrow set \<Rightarrow> ('c,'v) paper_bbk_model_data set" where
  "paper_R_arrow_endpoints S = paper_arrow_source ` S \<union> paper_arrow_target ` S"

definition paper_R_separator_indices ::
  "('c,'v) paper_bbk_model_data set \<Rightarrow> (('c,'v) paper_bbk_model_data \<times> 'v \<times> 'v) set" where
  "paper_R_separator_indices Obj = {(M,p,q). M \<in> Obj \<and> p \<in> paper_bbk_domain M Prop \<and>
    q \<in> paper_bbk_domain M Prop \<and> p \<noteq> q}"

definition paper_R_separator_choices ::
  "('c,'v) paper_R_bbk_arrow set \<Rightarrow> ('c,'v) paper_bbk_model_data set \<Rightarrow> ('c,'v) paper_R_bbk_arrow set" where
  "paper_R_separator_choices Arrows Obj =
    (\<lambda>t. paper_R_chosen_separator Arrows (fst t) (fst (snd t)) (snd (snd t))) ` paper_R_separator_indices Obj"

lemma paper_R_separator_choicesI:
  assumes object: "M \<in> Obj" and pm: "p \<in> paper_bbk_domain M Prop"
    and qm: "q \<in> paper_bbk_domain M Prop" and different: "p \<noteq> q"
  shows "paper_R_chosen_separator Arrows M p q \<in> paper_R_separator_choices Arrows Obj"
proof -
  have index: "(M,p,q) \<in> paper_R_separator_indices Obj" using assms by (simp add: paper_R_separator_indices_def)
  have image: "(\<lambda>t. paper_R_chosen_separator Arrows (fst t) (fst (snd t)) (snd (snd t))) (M,p,q)
    \<in> paper_R_separator_choices Arrows Obj" unfolding paper_R_separator_choices_def by (rule imageI[OF index])
  show ?thesis using image by simp
qed

lemma paper_R_separator_choicesE:
  assumes member: "r \<in> paper_R_separator_choices Arrows Obj"
  obtains M p q where "M \<in> Obj" "p \<in> paper_bbk_domain M Prop" "q \<in> paper_bbk_domain M Prop"
    "p \<noteq> q" "r = paper_R_chosen_separator Arrows M p q"
  using member that unfolding paper_R_separator_choices_def paper_R_separator_indices_def by auto

definition paper_R_hull_composable_pairs ::
  "('c,'v) paper_R_bbk_arrow set \<Rightarrow> (('c,'v) paper_R_bbk_arrow \<times> ('c,'v) paper_R_bbk_arrow) set" where
  "paper_R_hull_composable_pairs S = {(f,g). f \<in> S \<and> g \<in> S \<and> paper_arrow_target f = paper_arrow_source g}"

definition paper_R_hull_composites :: "('c,'v) paper_R_bbk_arrow set \<Rightarrow> ('c,'v) paper_R_bbk_arrow set" where
  "paper_R_hull_composites S = (\<lambda>p. paper_typed_compose paper_bbk_domain (snd p) (fst p)) ` paper_R_hull_composable_pairs S"

primrec paper_R_separating_stage_arrows ::
  "('c,'v) paper_R_bbk_arrow set \<Rightarrow> ('c,'v) paper_bbk_model_data \<Rightarrow> nat \<Rightarrow> ('c,'v) paper_R_bbk_arrow set" where
  "paper_R_separating_stage_arrows Arrows Root 0 = {paper_typed_identity paper_bbk_domain Root}"
| "paper_R_separating_stage_arrows Arrows Root (Suc n) = paper_R_separating_stage_arrows Arrows Root n \<union>
    paper_typed_identity paper_bbk_domain ` paper_R_arrow_endpoints (paper_R_separating_stage_arrows Arrows Root n) \<union>
    paper_R_separator_choices Arrows (paper_R_arrow_endpoints (paper_R_separating_stage_arrows Arrows Root n)) \<union>
    paper_R_hull_composites (paper_R_separating_stage_arrows Arrows Root n)"

definition paper_R_separating_stage_objects ::
  "('c,'v) paper_R_bbk_arrow set \<Rightarrow> ('c,'v) paper_bbk_model_data \<Rightarrow> nat \<Rightarrow> ('c,'v) paper_bbk_model_data set" where
  "paper_R_separating_stage_objects Arrows Root n = paper_R_arrow_endpoints (paper_R_separating_stage_arrows Arrows Root n)"

definition paper_R_separating_hull_arrows ::
  "('c,'v) paper_R_bbk_arrow set \<Rightarrow> ('c,'v) paper_bbk_model_data \<Rightarrow> ('c,'v) paper_R_bbk_arrow set" where
  "paper_R_separating_hull_arrows Arrows Root = (\<Union>n. paper_R_separating_stage_arrows Arrows Root n)"

definition paper_R_separating_hull_objects ::
  "('c,'v) paper_R_bbk_arrow set \<Rightarrow> ('c,'v) paper_bbk_model_data \<Rightarrow> ('c,'v) paper_bbk_model_data set" where
  "paper_R_separating_hull_objects Arrows Root = (\<Union>n. paper_R_separating_stage_objects Arrows Root n)"

text \<open>
  The stage index counts closure rounds, not individual arrows. Stages
  need not be finite or countable. The chosen separator is constrained
  only where a separating arrow exists. Cardinal bounds and the actual
  selected-category certificate are subsequent theorems, not definitions.
\<close>

end
