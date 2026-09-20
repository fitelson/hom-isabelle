theory Goodman_Book_QLN
  imports Goodman_Book_Vocabulary
begin

section \<open>Zeroary and unary Recombination and Exhaustion\<close>

text \<open>
  We encode separately:
    ∀p. Pure(p) → (□p → p),      ∀p. Pure(p) → (p → □p);
    ∀Xr. (Pure(X) ∧ Fun(r)) → (□Xr → ∀q.Xq), and its converse.
  The scope of the last ∀q does not bind r or X. Distinct names are
  chosen even when the argument types agree. This is the zeroary/unary
  package from the existing Goodman encoding, not a generic all-arity
  QLN theorem and not yet a proof of old-to-new formula correspondence.
\<close>

definition gb_zeroary_recombination where
  "gb_zeroary_recombination G = book_all G (gb_x G Prop)
    (book_imp (gb_pure Prop (NVar (gb_x G Prop)))
      (book_imp (book_box G (NVar (gb_x G Prop))) (NVar (gb_x G Prop))))"
definition gb_zeroary_exhaustion where
  "gb_zeroary_exhaustion G = book_all G (gb_x G Prop)
    (book_imp (gb_pure Prop (NVar (gb_x G Prop)))
      (book_imp (NVar (gb_x G Prop)) (book_box G (NVar (gb_x G Prop)))))"

definition gb_QLN_guard where
  "gb_QLN_guard G = book_and G
    (gb_pure gb_unary (NVar (gb_x G gb_unary)))
    (gb_fun Prop (NVar (gb_y G gb_unary Prop)))"
definition gb_QLN_box where
  "gb_QLN_box G = book_box G (NApp (NVar (gb_x G gb_unary)) (NVar (gb_y G gb_unary Prop)))"
definition gb_QLN_all where
  "gb_QLN_all G = book_all G (gb_z G gb_unary Prop Prop)
    (NApp (NVar (gb_x G gb_unary)) (NVar (gb_z G gb_unary Prop Prop)))"
definition gb_unary_recombination where
  "gb_unary_recombination G = book_all G (gb_x G gb_unary)
    (book_all G (gb_y G gb_unary Prop)
      (book_imp (gb_QLN_guard G) (book_imp (gb_QLN_box G) (gb_QLN_all G))))"
definition gb_unary_exhaustion where
  "gb_unary_exhaustion G = book_all G (gb_x G gb_unary)
    (book_all G (gb_y G gb_unary Prop)
      (book_imp (gb_QLN_guard G) (book_imp (gb_QLN_all G) (gb_QLN_box G))))"

lemma gb_zeroary_recombination_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_zeroary_recombination G)"
  unfolding gb_zeroary_recombination_def
  by (intro book_all_language book_imp_language gb_pure_language
    book_box_language[OF rich] gb_x_language[OF rich])

lemma gb_zeroary_exhaustion_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_zeroary_exhaustion G)"
  unfolding gb_zeroary_exhaustion_def
  by (intro book_all_language book_imp_language gb_pure_language
    book_box_language[OF rich] gb_x_language[OF rich])

lemma gb_QLN_guard_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_QLN_guard G)"
  unfolding gb_QLN_guard_def
  by (intro book_and_language[OF rich] gb_pure_language gb_fun_language
    gb_x_language[OF rich] gb_y_language[OF rich])

lemma gb_QLN_box_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_QLN_box G)"
  unfolding gb_QLN_box_def
  by (rule book_box_language[OF rich], rule book_language_App[
    OF gb_x_language[OF rich, where \<sigma>=gb_unary]
      gb_y_language[OF rich, where \<sigma>=gb_unary and \<tau>=Prop]])

lemma gb_QLN_all_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_QLN_all G)"
  unfolding gb_QLN_all_def
  by (rule book_all_language, rule book_language_App[
    OF gb_x_language[OF rich, where \<sigma>=gb_unary]
      gb_z_language[OF rich, where \<sigma>=gb_unary and \<tau>=Prop and \<upsilon>=Prop]])

lemma gb_unary_recombination_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_unary_recombination G)"
  unfolding gb_unary_recombination_def
  by (intro book_all_language book_imp_language gb_QLN_guard_language[OF rich]
    gb_QLN_box_language[OF rich] gb_QLN_all_language[OF rich])

lemma gb_unary_exhaustion_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_unary_exhaustion G)"
  unfolding gb_unary_exhaustion_def
  by (intro book_all_language book_imp_language gb_QLN_guard_language[OF rich]
    gb_QLN_box_language[OF rich] gb_QLN_all_language[OF rich])

lemma gb_QLN_axioms_closed:
  "named_fv (gb_zeroary_recombination G) = {}"
  "named_fv (gb_zeroary_exhaustion G) = {}"
  "named_fv (gb_unary_recombination G) = {}"
  "named_fv (gb_unary_exhaustion G) = {}"
  unfolding gb_zeroary_recombination_def gb_zeroary_exhaustion_def
    gb_unary_recombination_def gb_unary_exhaustion_def gb_QLN_guard_def gb_QLN_box_def gb_QLN_all_def
  by (auto simp: book_all_fv book_imp_fv book_box_fv book_and_fv)

end
