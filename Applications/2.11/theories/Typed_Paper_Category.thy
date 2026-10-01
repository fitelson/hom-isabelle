theory Typed_Paper_Category
  imports Typed_Source_Model
    "Bacon_Classicism_ZF_Representation.Bacon_Source_ZF_Action_Premodel"
begin

definition pa_Ar :: ZF where
  "pa_Ar = Sep (CartProd raw_W raw_W) (\<lambda>h. raw_rel (Fst h) (Snd h))"

definition pa_compose :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "pa_compose g f = Opair (Fst f) (Snd g)"

definition pa_id :: "ZF \<Rightarrow> ZF" where "pa_id w = Opair w w"

lemma pa_arrow_pair [simp]:
  "Elem (Opair v w) pa_Ar \<longleftrightarrow> Elem v raw_W \<and> Elem w raw_W \<and> raw_rel v w"
  by (simp add: pa_Ar_def Sep CartProd Opair Fst Snd)

lemma pa_arrowE:
  assumes "Elem h pa_Ar"
  obtains v w where "Elem v raw_W" "Elem w raw_W" "raw_rel v w" "h=Opair v w"
  using assms that by (auto simp: pa_Ar_def Sep CartProd Fst Snd)

lemma pa_arrow_data:
  assumes "Elem h pa_Ar"
  shows "Elem (Fst h) raw_W" "Elem (Snd h) raw_W" "raw_rel (Fst h) (Snd h)"
    "Opair (Fst h) (Snd h)=h"
  using assms by (auto elim: pa_arrowE simp: Fst Snd)

lemma pa_arrow_iff:
  "Elem h pa_Ar \<longleftrightarrow> Elem (Fst h) raw_W \<and> Elem (Snd h) raw_W \<and>
    raw_rel (Fst h) (Snd h) \<and> Opair (Fst h) (Snd h)=h"
  using pa_arrow_data[of h] pa_arrow_pair[of "Fst h" "Snd h"] by metis

theorem pa_category:
  "paper_category (explode raw_W) (explode pa_Ar) Fst Snd pa_compose pa_id"
  by unfold_locales
    (auto simp: explode_Elem pa_arrow_iff pa_compose_def pa_id_def Fst Snd
      intro: raw_rel_refl raw_rel_trans)

lemma pa_root_reaches:
  assumes "w \<in> explode raw_W"
  shows "\<exists>h\<in>explode pa_Ar. Fst h=raw_root \<and> Snd h=w"
  by (rule bexI[where x="Opair raw_root w"])
    (use assms in \<open>simp_all add: Fst Snd explode_Elem raw_rel_def\<close>)

theorem pa_rooted_category:
  "paper_rooted_category (explode raw_W) (explode pa_Ar) Fst Snd pa_compose pa_id raw_root"
proof (rule paper_rooted_category.intro[OF pa_category],
    rule paper_rooted_category_axioms.intro)
  show "raw_root \<in> explode raw_W" by (simp only: explode_Elem raw_worlds)
  show "\<And>w. w \<in> explode raw_W \<Longrightarrow> \<exists>h\<in>explode pa_Ar. Fst h=raw_root \<and> Snd h=w"
    by (rule pa_root_reaches)
qed

interpretation pa: paper_rooted_category "explode raw_W" "explode pa_Ar"
  Fst Snd pa_compose pa_id raw_root by (rule pa_rooted_category)

lemma pa_pair_member:
  "Elem (Opair (Opair w v) x) (paper_ZF_pair_code pa_Ar Fst Snd D w) \<longleftrightarrow>
    Elem w raw_W \<and> Elem v raw_W \<and> raw_rel w v \<and> Elem x (D v)"
  by (simp only: paper_ZF_pair_code_member explode_Elem pa_arrow_pair Fst Snd; blast)

lemma pa_pairE:
  assumes "Elem z (paper_ZF_pair_code pa_Ar Fst Snd D w)"
  obtains v x where "Elem w raw_W" "Elem v raw_W" "raw_rel w v"
    "Elem x (D v)" "z=Opair (Opair w v) x"
  using assms that
  by (auto elim!: paper_ZF_pair_codeE pa_arrowE simp: explode_Elem Fst Snd)

lemma pa_pair_reconstruct:
  assumes "Elem z (paper_ZF_pair_code pa_Ar Fst Snd D w)"
  shows "Elem w raw_W" "Elem (Snd (Fst z)) raw_W" "raw_rel w (Snd (Fst z))"
    "Elem (Snd z) (D (Snd (Fst z)))" "z=Opair (Opair w (Snd (Fst z))) (Snd z)"
  using assms by (auto elim: pa_pairE simp: Fst Snd)

theorem pa_book_action:
  "paper_action (explode raw_W) (explode pa_Ar) Fst Snd pa_compose pa_id
    (\<lambda>w. explode (src_D a w)) (\<lambda>h. src_T a (Fst h) (Snd h))"
proof -
  interpret C: paper_category "explode raw_W" "explode pa_Ar" Fst Snd pa_compose pa_id
    by (rule pa_category)
  show ?thesis
    by unfold_locales
      (auto simp: explode_Elem pa_arrow_iff pa_id_def pa_compose_def Fst Snd
        intro: src_T_type src_T_id src_T_compose)
qed

end
