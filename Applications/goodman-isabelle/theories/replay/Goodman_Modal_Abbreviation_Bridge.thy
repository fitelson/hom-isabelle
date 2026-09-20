theory Goodman_Modal_Abbreviation_Bridge
  imports Goodman_Native_Stock_Bridge
    Bacon_Book_Classicism_Development.Bacon_Book_Box_Truth
begin

section \<open>The two truth terms are provably identical in C, not by definition\<close>

definition gi_old_top where
  "gi_old_top G ns = (let n = named_chart_fresh G ns Prop in
    book_all G n (book_imp (NVar n) (NVar n)))"

lemma gi_true_translation:
  "gi_to_book G ns k ObjTrue = gi_old_top G ns"
  by (simp add: ObjTrue_def gi_old_top_def Let_def)

lemma gi_old_top_language:
  "sg_rich G \<Longrightarrow> book_theory_formula \<Sigma> G (gi_old_top G ns)"
  unfolding gi_old_top_def Let_def
  by (intro book_all_language book_imp_language;
    simp only: book_language_var_iff named_chart_fresh_type)

lemma gi_old_top_closed:
  "named_fv (gi_old_top G ns) = {}"
  by (simp add: gi_old_top_def Let_def book_all_fv book_imp_fv)

context book_full_minimal_model
begin

lemma gi_old_top_true:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
  shows "V (denote g (gi_old_top stock ns))"
proof -
  let ?n = "named_chart_fresh stock ns Prop"
  have vl: "book_theory_formula signature stock (NVar ?n)"
    by (simp only: book_language_var_iff named_chart_fresh_type[OF rich])
  have il: "book_theory_formula signature stock (book_imp (NVar ?n) (NVar ?n))"
    by (rule book_imp_language[OF vl vl])
  have each: "\<And>a. a \<in> domain (stock ?n) \<Longrightarrow>
    V (denote (g(?n := a)) (book_imp (NVar ?n) (NVar ?n)))"
    by (simp only: book_imp_truth[OF book_env_update[OF typed] vl vl]; simp)
  show ?thesis unfolding gi_old_top_def Let_def
    by (simp only: book_all_truth[OF typed il]; use each in blast)
qed

end

lemma gi_H_truth_equivalence:
  assumes rich: "sg_rich G"
  shows "book_H \<Sigma> G (book_iff G (gi_old_top G ns) (book_top G))"
proof (rule gi_H_validity_certificate[OF rich
    book_iff_language[OF rich gi_old_top_language[OF rich] book_top_language[OF rich]]])
  fix D :: "otype \<Rightarrow> ('a book_henkin_name) book_named_term set set" and app J V c g
  assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
  interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
  show "V (J g (book_iff G (gi_old_top G ns) (book_top G)))"
    by (simp only: M.book_iff_truth[OF rich typed gi_old_top_language[OF rich] book_top_language[OF rich]]
      M.gi_old_top_true[OF rich typed] M.book_top_true[OF rich typed])
qed

theorem gi_goodman_truth_identity:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves \<Sigma> G T
    (book_leibniz G Prop (gi_old_top G ns) (book_top G))"
  by (rule goodman_book_proves.PE[OF _ gi_old_top_language[OF rich] book_top_language[OF rich]],
    rule goodman_book_proves.Base, rule book_full_C_proves.H,
    rule gi_H_truth_equivalence[OF rich])

section \<open>Changing the truth representative in necessity\<close>

lemma gi_H_box_representative:
  fixes \<Sigma> :: "'c ssignature" and A U :: "'c book_named_term"
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and ul: "book_theory_formula \<Sigma> G U"
  shows "book_H \<Sigma> G (book_imp (book_leibniz G Prop U (book_top G))
    (book_iff G (book_leibniz G Prop A U) (book_box G A)))"
proof -
  have tl: "book_theory_formula \<Sigma> G (book_top G)" by (rule book_top_language[OF rich])
  have el: "book_theory_formula \<Sigma> G (book_leibniz G Prop U (book_top G))"
    by (rule book_leibniz_language[OF rich ul tl])
  have au: "book_theory_formula \<Sigma> G (book_leibniz G Prop A U)"
    by (rule book_leibniz_language[OF rich al ul])
  have box: "book_theory_formula \<Sigma> G (book_box G A)" by (rule book_box_language[OF rich al])
  have iff: "book_theory_formula \<Sigma> G (book_iff G (book_leibniz G Prop A U) (book_box G A))"
    by (rule book_iff_language[OF rich au box])
  show ?thesis
  proof (rule gi_H_validity_certificate[OF rich book_imp_language[OF el iff]])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
    assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
    show "V (J g (book_imp (book_leibniz G Prop U (book_top G))
      (book_iff G (book_leibniz G Prop A U) (book_box G A))))"
      by (simp only: M.book_imp_truth[OF typed el iff] M.book_iff_truth[OF rich typed au box]
        M.book_leibniz_truth[OF rich typed ul tl] M.book_leibniz_truth[OF rich typed al ul]
        M.book_box_truth[OF rich typed al]; meson book_leibniz_trans book_leibniz_sym)
  qed
qed

theorem gi_goodman_box_equivalence:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
  shows "goodman_book_proves \<Sigma> G T
    (book_iff G (book_leibniz G Prop A (gi_old_top G ns)) (book_box G A))"
proof -
  have ul: "book_theory_formula \<Sigma> G (gi_old_top G ns)" by (rule gi_old_top_language[OF rich])
  have certificate: "goodman_book_proves \<Sigma> G T
    (book_imp (book_leibniz G Prop (gi_old_top G ns) (book_top G))
      (book_iff G (book_leibniz G Prop A (gi_old_top G ns)) (book_box G A)))"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H,
      rule gi_H_box_representative[OF rich al ul])
  show ?thesis by (rule goodman_book_proves.MP[OF gi_goodman_truth_identity[OF rich] certificate];
    intro book_iff_language[OF rich] book_leibniz_language[OF rich] book_box_language[OF rich] al ul)
qed

corollary gi_translated_box_equivalence:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G (gi_to_book G ns k A)"
  shows "goodman_book_proves \<Sigma> G T
    (book_iff G (gi_to_book G ns k (ObjBox A)) (book_box G (gi_to_book G ns k A)))"
  unfolding ObjBox_def gi_to_book.simps gi_true_translation
  by (rule gi_goodman_box_equivalence[OF rich al])

text \<open>
  This is a theorem-level equivalence in C+[T], for every T and every
  admitted signature. The proof uses PE on an H theorem equating the two
  truth terms. It does not identify co-true propositions in H, replace
  Leibniz identity by HOL equality, or apply PE under temporary assumptions.
\<close>

end
