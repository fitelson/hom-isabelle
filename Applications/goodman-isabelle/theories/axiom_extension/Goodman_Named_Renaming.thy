theory Goodman_Named_Renaming
  imports Goodman_Translation_Encoding
begin

section \<open>Slot renaming is independent of chosen binder names up to α\<close>

theorem gi_to_book_rename_alpha:
  assumes rich: "sg_rich G" and typed: "\<Gamma> \<turnstile> A : \<tau>"
    and renamed: "\<Delta> \<turnstile> rename r A : \<tau>"
    and chart: "map G ns = \<Gamma>" and target_chart: "map G ms = \<Delta>"
    and distinct: "distinct ns" and target_distinct: "distinct ms"
    and agrees: "\<And>i. i \<in> sfv (gi_expand G k A) \<Longrightarrow> ms ! r i = ns ! i"
  shows "named_alpha G (gi_to_book G ms k (rename r A)) (gi_to_book G ns k A)"
proof -
  have left: "named_to_source G [] (gi_to_book G ms k (rename r A)) =
    srename ((\<lambda>i. ms ! i) \<circ> r) (gi_expand G k A)"
    using gi_to_book_empty_encoding[OF rich renamed target_chart target_distinct, where k=k]
    by (simp only: gi_expand_rename srename_comp)
  have agreement: "srename ((\<lambda>i. ms ! i) \<circ> r) (gi_expand G k A) =
    srename (\<lambda>i. ns ! i) (gi_expand G k A)"
    by (rule srename_fv_agreement; simp only: comp_def; rule agrees; assumption)
  have right: "named_to_source G [] (gi_to_book G ns k A) =
    srename (\<lambda>i. ns ! i) (gi_expand G k A)"
    by (rule gi_to_book_empty_encoding[OF rich typed chart distinct])
  show ?thesis by (rule named_encoding_implies_alpha[OF rich]; simp only: left agreement right)
qed

corollary gi_to_book_shift_alpha:
  assumes rich: "sg_rich G" and typed: "\<Gamma> \<turnstile> A : \<tau>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and fresh: "n \<notin> set ns" and type_n: "G n = \<sigma>"
  shows "named_alpha G (gi_to_book G (n # ns) k (shift A)) (gi_to_book G ns k A)"
proof -
  have shifted: "\<sigma> # \<Gamma> \<turnstile> rename Suc A : \<tau>"
    using weakening_front[OF typed, where \<sigma>=\<sigma>] by (simp only: shift_def)
  have target_chart: "map G (n # ns) = \<sigma> # \<Gamma>" by (simp add: type_n chart)
  have target_distinct: "distinct (n # ns)" by (simp add: fresh distinct)
  show ?thesis unfolding shift_def
    by (rule gi_to_book_rename_alpha[OF rich typed shifted chart target_chart distinct target_distinct]; simp)
qed

end
