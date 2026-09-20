theory Goodman_Vector_Charts
  imports Goodman_Integration_Proof.Goodman_Translated_Extension_Rules
    Bacon_C_Presentation_Development.Bacon_H_Only_Classicism_Equivalence
    Bacon_C_Presentation_Development.Bacon_C_Vector_Presentation
begin

section \<open>A fresh typed prefix, retaining both argument-order conventions\<close>

fun gi_prefix :: "sgcontext \<Rightarrow> otype list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "gi_prefix G [] ns = []"
| "gi_prefix G (\<sigma> # \<Delta>) ns =
    (let ps = gi_prefix G \<Delta> ns in named_chart_fresh G (ps @ ns) \<sigma> # ps)"

lemma gi_prefix_types:
  "sg_rich G \<Longrightarrow> map G (gi_prefix G \<Delta> ns) = \<Delta>"
  by (induction \<Delta>) (simp_all add: Let_def named_chart_fresh_type)

lemma gi_prefix_distinct:
  assumes rich: "sg_rich G" and distinct: "distinct ns"
  shows "distinct (gi_prefix G \<Delta> ns @ ns)"
proof (induction \<Delta>)
  case Nil
  show ?case using distinct by simp
next
  case (Cons a \<Delta>)
  have fresh: "named_chart_fresh G (gi_prefix G \<Delta> ns @ ns) a \<notin> set (gi_prefix G \<Delta> ns @ ns)"
    by (rule named_chart_fresh_notin[OF rich])
  show ?case using Cons.IH fresh by (simp add: Let_def)
qed

lemma gi_prefix_length[simp]: "length (gi_prefix G \<Delta> ns) = length \<Delta>"
  by (induction \<Delta>) (simp_all add: Let_def)

lemma gi_arrow_fold: "arrow_type \<Delta> \<tau> = foldr Arr \<Delta> \<tau>"
  by (induction \<Delta>) simp_all

lemma gi_shift_by_prefix_alpha:
  assumes rich: "sg_rich G" and typed: "\<Gamma> \<turnstile> F : \<tau>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct (ps @ ns)"
  shows "named_alpha G (gi_to_book G (ps @ ns) k (shift_by (length ps) F)) (gi_to_book G ns k F)"
proof -
  have original_distinct: "distinct ns" using distinct by simp
  have raised: "map G ps @ \<Gamma> \<turnstile> shift_by (length ps) F : \<tau>"
    using shift_by_preserves_typing[OF typed, where \<Delta>="map G ps"] by simp
  have target_chart: "map G (ps @ ns) = map G ps @ \<Gamma>" by (simp add: chart)
  show ?thesis unfolding shift_by_def
    by (rule gi_to_book_rename_alpha[OF rich typed raised[unfolded shift_by_def]
      chart target_chart original_distinct distinct]; simp add: shift_ren_def nth_append)
qed

lemma gi_translate_app_vec:
  "gi_to_book G ns k (app_vec F As) =
    foldl NApp (gi_to_book G ns k F) (map (gi_to_book G ns k) As)"
  by (induction As arbitrary: F) simp_all

lemma gi_translate_fresh_vars:
  "map (gi_to_book G (ps @ ns) k) (fresh_vars (length ps)) = map NVar ps"
proof (rule nth_equalityI)
  show "length (map (gi_to_book G (ps @ ns) k) (fresh_vars (length ps))) = length (map NVar ps)"
    by (simp add: fresh_vars_def)
  fix i
  assume bound: "i < length (map (gi_to_book G (ps @ ns) k) (fresh_vars (length ps)))"
  then show "map (gi_to_book G (ps @ ns) k) (fresh_vars (length ps)) ! i = map NVar ps ! i"
    by (simp add: fresh_vars_def nth_append)
qed

lemma gi_alpha_fold_app:
  "named_alpha G F H \<Longrightarrow> named_alpha G (foldl NApp F As) (foldl NApp H As)"
  by (induction As arbitrary: F H) (auto intro: named_alpha.App named_alpha.Refl)

lemma gi_alpha_binary:
  "named_alpha G A B \<Longrightarrow> named_alpha G C D \<Longrightarrow>
    named_alpha G (NApp (NApp E A) C) (NApp (NApp E B) D)"
  by (intro named_alpha.App named_alpha.Refl; assumption)

lemma gi_alpha_expanded_iff:
  "named_alpha G A A' \<Longrightarrow> named_alpha G B B' \<Longrightarrow>
    named_alpha G (book_and G (book_imp A B) (book_imp B A))
      (book_and G (book_imp A' B') (book_imp B' A'))"
  unfolding book_and_def book_imp_def
  by (intro gi_alpha_binary; assumption)

lemma gi_H_rule_raise_shift:
  "H_rule_raise n F = shift_by n F"
  by (simp only: H_rule_raise_bridge CEV_shift_by_is_vector_raise)

end
