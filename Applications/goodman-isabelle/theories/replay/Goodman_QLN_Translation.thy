theory Goodman_QLN_Translation
  imports Goodman_Theorem_Equivalence_Congruence
begin

section \<open>Keep the two unary binder orders explicit\<close>

lemma gi_gb_z_reversed:
  "named_chart_fresh G [gb_y G \<sigma> \<tau>, gb_x G \<sigma>] \<upsilon> = gb_z G \<sigma> \<tau> \<upsilon>"
  by (simp add: gb_z_def named_chart_fresh_def insert_commute)

lemma gi_zeroary_recombination_shape:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_zeroary_recombination =
    book_all G (gb_x G Prop) (book_imp (gb_pure Prop (NVar (gb_x G Prop)))
      (book_imp (book_leibniz G Prop (NVar (gb_x G Prop)) (gi_old_top G [gb_x G Prop]))
        (NVar (gb_x G Prop))))"
  by (simp add: pp_zeroary_recombination_def ObjBox_def gi_true_translation
    gi_pure_translation gb_x_def Let_def)

lemma gi_zeroary_exhaustion_shape:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_zeroary_exhaustion =
    book_all G (gb_x G Prop) (book_imp (gb_pure Prop (NVar (gb_x G Prop)))
      (book_imp (NVar (gb_x G Prop))
        (book_leibniz G Prop (NVar (gb_x G Prop)) (gi_old_top G [gb_x G Prop]))))"
  by (simp add: pp_zeroary_exhaustion_def ObjBox_def gi_true_translation
    gi_pure_translation gb_x_def Let_def)

lemma gi_unary_recombination_shape:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_unary_recombination =
    book_all G (gb_x G gb_unary) (book_all G (gb_y G gb_unary Prop)
      (book_imp (gb_QLN_guard G)
        (book_imp (book_leibniz G Prop
          (NApp (NVar (gb_x G gb_unary)) (NVar (gb_y G gb_unary Prop)))
          (gi_old_top G [gb_y G gb_unary Prop, gb_x G gb_unary])) (gb_QLN_all G))))"
  by (simp add: pp_unary_recombination_def ObjBox_def gi_true_translation
    gi_pure_translation gi_fun_translation gb_QLN_guard_def gb_QLN_all_def
    gb_x_def gb_y_def gb_z_def Let_def named_chart_fresh_def insert_commute)

lemma gi_unary_exhaustion_shape:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_unary_exhaustion =
    book_all G (gb_x G gb_unary) (book_all G (gb_y G gb_unary Prop)
      (book_imp (gb_QLN_guard G)
        (book_imp (gb_QLN_all G) (book_leibniz G Prop
          (NApp (NVar (gb_x G gb_unary)) (NVar (gb_y G gb_unary Prop)))
          (gi_old_top G [gb_y G gb_unary Prop, gb_x G gb_unary])))))"
  by (simp add: pp_unary_exhaustion_def ObjBox_def gi_true_translation
    gi_pure_translation gi_fun_translation gb_QLN_guard_def gb_QLN_all_def
    gb_x_def gb_y_def gb_z_def Let_def named_chart_fresh_def insert_commute)

lemma gi_persistence_shape:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k (pp_persistence \<sigma>) =
    book_all G (gb_x G \<sigma>) (book_imp (gb_pure \<sigma> (NVar (gb_x G \<sigma>)))
      (book_leibniz G Prop (gb_pure \<sigma> (NVar (gb_x G \<sigma>))) (gi_old_top G [gb_x G \<sigma>])))"
  by (simp add: pp_persistence_def ObjBox_def gi_true_translation
    gi_pure_translation gb_x_def Let_def)

section \<open>Lift the checked Box equivalence through the axiom formulas\<close>

lemma gi_gb_universal_language:
  "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma> \<Longrightarrow>
    book_in_language book_minimal_logical_type UNIV (\<lambda>_. UNIV) G A \<sigma>"
  by (rule book_language_signature_mono; auto)

theorem gi_zeroary_recombination_equivalence:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves (\<lambda>_. UNIV) G T
    (book_iff G (gi_to_book G [] k pp_zeroary_recombination) (gb_zeroary_recombination G))"
  unfolding gi_zeroary_recombination_shape[OF names] gb_zeroary_recombination_def
  by (intro gi_goodman_iff_all_congruence[OF rich] gi_goodman_iff_imp_congruence[OF rich]
    gi_goodman_iff_reflexive[OF rich] gi_goodman_box_equivalence[OF rich]
    book_imp_language book_leibniz_language[OF rich] book_box_language[OF rich]
    gi_old_top_language[OF rich] gi_gb_universal_language gb_pure_language gb_x_language[OF rich])

theorem gi_zeroary_exhaustion_equivalence:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves (\<lambda>_. UNIV) G T
    (book_iff G (gi_to_book G [] k pp_zeroary_exhaustion) (gb_zeroary_exhaustion G))"
  unfolding gi_zeroary_exhaustion_shape[OF names] gb_zeroary_exhaustion_def
  by (intro gi_goodman_iff_all_congruence[OF rich] gi_goodman_iff_imp_congruence[OF rich]
    gi_goodman_iff_reflexive[OF rich] gi_goodman_box_equivalence[OF rich]
    book_imp_language book_leibniz_language[OF rich] book_box_language[OF rich]
    gi_old_top_language[OF rich] gi_gb_universal_language gb_pure_language gb_x_language[OF rich])

theorem gi_unary_recombination_equivalence:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves (\<lambda>_. UNIV) G T
    (book_iff G (gi_to_book G [] k pp_unary_recombination) (gb_unary_recombination G))"
proof -
  have arg: "book_theory_formula (\<lambda>_. UNIV) G
    (NApp (NVar (gb_x G gb_unary)) (NVar (gb_y G gb_unary Prop)))"
    by (rule book_language_App[OF gb_x_language[OF rich, where \<sigma>=gb_unary]
      gb_y_language[OF rich, where \<sigma>=gb_unary and \<tau>=Prop]])
  show ?thesis unfolding gi_unary_recombination_shape[OF names]
    gb_unary_recombination_def gb_QLN_box_def
    by (intro gi_goodman_iff_all_congruence[OF rich] gi_goodman_iff_imp_congruence[OF rich]
      gi_goodman_iff_reflexive[OF rich] gi_goodman_box_equivalence[OF rich]
      book_all_language book_imp_language book_leibniz_language[OF rich] book_box_language[OF rich]
      gi_old_top_language[OF rich] arg gi_gb_universal_language
      gb_QLN_guard_language[OF rich] gb_QLN_all_language[OF rich])
qed

theorem gi_unary_exhaustion_equivalence:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves (\<lambda>_. UNIV) G T
    (book_iff G (gi_to_book G [] k pp_unary_exhaustion) (gb_unary_exhaustion G))"
proof -
  have arg: "book_theory_formula (\<lambda>_. UNIV) G
    (NApp (NVar (gb_x G gb_unary)) (NVar (gb_y G gb_unary Prop)))"
    by (rule book_language_App[OF gb_x_language[OF rich, where \<sigma>=gb_unary]
      gb_y_language[OF rich, where \<sigma>=gb_unary and \<tau>=Prop]])
  show ?thesis unfolding gi_unary_exhaustion_shape[OF names]
    gb_unary_exhaustion_def gb_QLN_box_def
    by (intro gi_goodman_iff_all_congruence[OF rich] gi_goodman_iff_imp_congruence[OF rich]
      gi_goodman_iff_reflexive[OF rich] gi_goodman_box_equivalence[OF rich]
      book_all_language book_imp_language book_leibniz_language[OF rich] book_box_language[OF rich]
      gi_old_top_language[OF rich] arg gi_gb_universal_language
      gb_QLN_guard_language[OF rich] gb_QLN_all_language[OF rich])
qed

theorem gi_persistence_equivalence:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves (\<lambda>_. UNIV) G T
    (book_iff G (gi_to_book G [] k (pp_persistence \<sigma>)) (gb_persistence G \<sigma>))"
  unfolding gi_persistence_shape[OF names] gb_persistence_def
  by (intro gi_goodman_iff_all_congruence[OF rich] gi_goodman_iff_imp_congruence[OF rich]
    gi_goodman_iff_reflexive[OF rich] gi_goodman_box_equivalence[OF rich]
    book_imp_language book_leibniz_language[OF rich] book_box_language[OF rich]
    gi_old_top_language[OF rich] gi_gb_universal_language gb_pure_language gb_x_language[OF rich])

text \<open>
  Both QLN directions at arities zero and one, and each persistence
  instance, are theorem-equivalent in every C+[T]. This proves neither
  schema-set equality nor generic all-arity QLN. The unary binder-order
  calculation is explicit; the bound argument of ∀q is never confused
  with the fundamental-proposition variable r.
\<close>

end
