theory Goodman_T6_Transfer
  imports Goodman_CEV_Axiom_Preservation
    Goodman_Legacy_06.Bacon_PP_Goodman_T6_RS
    Goodman_Legacy_05.Bacon_PP_Goodman_T6_WI
begin

section \<open>Replay the four T6 contradictions in the book-language extension\<close>

lemma gi_T6_core_closed:
  "A \<in> pp_T6_core_PP_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  by (rule pp_T6_Inv_axioms_typed; auto simp: pp_T6_Inv_axioms_def)

lemma gi_T6_TU_closed:
  "A \<in> pp_T6_TU_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding pp_T6_TU_axioms_def
  by (auto intro: gi_T6_core_closed typed_pp_TU typed_pp_L2 typed_pp_exists_fun_prime)

lemma gi_T6_WI_closed:
  "A \<in> pp_T6_WI_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding pp_T6_WI_axioms_def
  by (auto intro: gi_T6_core_closed typed_pp_WI typed_pp_L2 typed_pp_exists_fun_prime)

theorem gi_T6_Inv_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) pp_T6_Inv_axioms) (book_bottom G)"
  by (rule gi_CEV_closed_refutation[OF rich CEV_Goodman_T6_Inv pp_T6_Inv_axioms_typed])

corollary gi_T6_Inv_inconsistent:
  "sg_rich G \<Longrightarrow> \<not> goodman_book_consistent (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) pp_T6_Inv_axioms)"
  unfolding goodman_book_consistent_def using gi_T6_Inv_refutation by blast

theorem gi_T6_TU_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) pp_T6_TU_axioms) (book_bottom G)"
  by (rule gi_CEV_closed_refutation[OF rich CEV_Goodman_T6_TU gi_T6_TU_closed])

corollary gi_T6_TU_inconsistent:
  "sg_rich G \<Longrightarrow> \<not> goodman_book_consistent (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) pp_T6_TU_axioms)"
  unfolding goodman_book_consistent_def using gi_T6_TU_refutation by blast

theorem gi_T6_WI_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) pp_T6_WI_axioms) (book_bottom G)"
  by (rule gi_CEV_closed_refutation[OF rich CEV_Goodman_T6_WI gi_T6_WI_closed])

corollary gi_T6_WI_inconsistent:
  "sg_rich G \<Longrightarrow> \<not> goodman_book_consistent (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) pp_T6_WI_axioms)"
  unfolding goodman_book_consistent_def using gi_T6_WI_refutation by blast

theorem gi_T6_RS_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) pp_T6_RS_axioms) (book_bottom G)"
  by (rule gi_CEV_closed_refutation[OF rich CEV_Goodman_T6_RS pp_T6_RS_axioms_typed])

corollary gi_T6_RS_inconsistent:
  "sg_rich G \<Longrightarrow> \<not> goodman_book_consistent (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) pp_T6_RS_axioms)"
  unfolding goodman_book_consistent_def using gi_T6_RS_refutation by blast

text \<open>
  Each theorem retains the exact image of its original closed T6 stock.
  Inv, TU and WI use existence of fun′, weak L2 and their respective
  additional principle. RS uses strong L2 and rigid specification.
  These are not contradictions from the central PP stock alone.
  The target is full-F/minimal C+[T] in the universal signature.
\<close>

end
