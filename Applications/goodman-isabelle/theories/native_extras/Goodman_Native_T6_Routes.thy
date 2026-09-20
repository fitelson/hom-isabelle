theory Goodman_Native_T6_Routes
  imports Goodman_Native_T6_Extras
    "Goodman_Integration_Central_Stock.Goodman_Central_Stock_T6"
    "Goodman_Integration_Individual.Goodman_TU_Inv_Exhaustion"
begin

section \<open>T6 over the native logical-purity/application/PP core\<close>

text \<open>
  The conclusions below contain no translation parameter k and no
  untranslated route extras. Weak L2 with Inv, TU, or WI requires the
  explicit ∃fun′ axiom over the small common core. The strong-L2/RS route
  retains precisely its original two extras; no separate existence axiom
  is inserted. These are refutations of those displayed augmented stocks,
  not refutations of PP by itself.
\<close>

theorem gi_native_T6_Inv_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G
    (gb_T6_core G \<union> {gb_exists_fun_prime G, gb_L2 G, gb_Inv G}) (book_bottom G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "goodman_book_proves gb_signature G
      (gi_T6_native_core_extension G k {pp_exists_fun_prime, pp_L2, pp_Inv}) (book_bottom G)"
    by (rule gi_T6_native_Inv_refutation_in_signature[OF rich names])
  show ?thesis using original
    by (simp only: gi_T6_native_core_extension_def image_insert image_empty
        gi_exists_fun_prime_translation[OF names] gi_L2_native_translation[OF names] gi_Inv_native_translation[OF names])
qed

theorem gi_native_T6_TU_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G
    (gb_T6_core G \<union> {gb_exists_fun_prime G, gb_L2 G, gb_TU G}) (book_bottom G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "goodman_book_proves gb_signature G
      (gi_T6_native_core_extension G k {pp_exists_fun_prime, pp_L2, pp_TU}) (book_bottom G)"
    by (rule gi_T6_native_TU_refutation_in_signature[OF rich names])
  show ?thesis using original
    by (simp only: gi_T6_native_core_extension_def image_insert image_empty
        gi_exists_fun_prime_translation[OF names] gi_L2_native_translation[OF names] gi_TU_native_translation[OF names])
qed

theorem gi_native_T6_WI_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G
    (gb_T6_core G \<union> {gb_exists_fun_prime G, gb_L2 G, gb_WI G}) (book_bottom G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "goodman_book_proves gb_signature G
      (gi_T6_native_core_extension G k {pp_exists_fun_prime, pp_L2, pp_WI}) (book_bottom G)"
    by (rule gi_T6_native_WI_refutation_in_signature[OF rich names])
  show ?thesis using original
    by (simp only: gi_T6_native_core_extension_def image_insert image_empty
        gi_exists_fun_prime_translation[OF names] gi_L2_native_translation[OF names] gi_WI_native_translation[OF names])
qed

theorem gi_native_T6_RS_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G
    (gb_T6_core G \<union> {gb_strong_L2 G, gb_RS G}) (book_bottom G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "goodman_book_proves gb_signature G
      (gi_T6_native_core_extension G k {pp_strong_L2, pp_RS}) (book_bottom G)"
    by (rule gi_T6_native_RS_refutation_in_signature[OF rich names])
  show ?thesis using original
    by (simp only: gi_T6_native_core_extension_def image_insert image_empty
        gi_strong_L2_native_translation[OF names] gi_RS_native_translation[OF names])
qed

section \<open>The repaired central stock supplies the existence premise\<close>

text \<open>
  This base adds unique proposition-level fundamentality, absence of
  other fundamentals, Recombination, and zeroary Exhaustion to the
  appropriate purity/PP background. Its already checked derivation of
  ∃fun′ means that existence is not listed as an independent route extra.
  The only extras below are exactly those shown in each axiom set.
\<close>

theorem gi_native_central_T6_Inv_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G
    (gb_recombination_PP_zeroary_exhaustion G \<union> {gb_L2 G, gb_Inv G}) (book_bottom G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "goodman_book_proves gb_signature G
      (gb_central_T6_extension G k {pp_L2, pp_Inv}) (book_bottom G)"
    by (rule gi_central_T6_Inv_refutation[OF rich names])
  show ?thesis using original
    by (simp only: gb_central_T6_extension_def image_insert image_empty
        gi_L2_native_translation[OF names] gi_Inv_native_translation[OF names])
qed

theorem gi_native_central_T6_TU_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G
    (gb_recombination_PP_zeroary_exhaustion G \<union> {gb_L2 G, gb_TU G}) (book_bottom G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "goodman_book_proves gb_signature G
      (gb_central_T6_extension G k {pp_L2, pp_TU}) (book_bottom G)"
    by (rule gi_central_T6_TU_refutation[OF rich names])
  show ?thesis using original
    by (simp only: gb_central_T6_extension_def image_insert image_empty
        gi_L2_native_translation[OF names] gi_TU_native_translation[OF names])
qed

theorem gi_native_central_T6_WI_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G
    (gb_recombination_PP_zeroary_exhaustion G \<union> {gb_L2 G, gb_WI G}) (book_bottom G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "goodman_book_proves gb_signature G
      (gb_central_T6_extension G k {pp_L2, pp_WI}) (book_bottom G)"
    by (rule gi_central_T6_WI_refutation[OF rich names])
  show ?thesis using original
    by (simp only: gb_central_T6_extension_def image_insert image_empty
        gi_L2_native_translation[OF names] gi_WI_native_translation[OF names])
qed

theorem gi_native_central_T6_RS_refutation:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G
    (gb_recombination_PP_zeroary_exhaustion G \<union> {gb_strong_L2 G, gb_RS G}) (book_bottom G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "goodman_book_proves gb_signature G
      (gb_central_T6_extension G k {pp_strong_L2, pp_RS}) (book_bottom G)"
    by (rule gi_central_T6_RS_refutation[OF rich names])
  show ?thesis using original
    by (simp only: gb_central_T6_extension_def image_insert image_empty
        gi_strong_L2_native_translation[OF names] gi_RS_native_translation[OF names])
qed

section \<open>Consistency statements retain all of their route assumptions\<close>

corollary gi_native_T6_Inv_inconsistent:
  "sg_rich G \<Longrightarrow> \<not> goodman_book_consistent gb_signature G
    (gb_T6_core G \<union> {gb_exists_fun_prime G, gb_L2 G, gb_Inv G})"
  unfolding goodman_book_consistent_def using gi_native_T6_Inv_refutation by blast

corollary gi_native_T6_TU_inconsistent:
  "sg_rich G \<Longrightarrow> \<not> goodman_book_consistent gb_signature G
    (gb_T6_core G \<union> {gb_exists_fun_prime G, gb_L2 G, gb_TU G})"
  unfolding goodman_book_consistent_def using gi_native_T6_TU_refutation by blast

corollary gi_native_T6_WI_inconsistent:
  "sg_rich G \<Longrightarrow> \<not> goodman_book_consistent gb_signature G
    (gb_T6_core G \<union> {gb_exists_fun_prime G, gb_L2 G, gb_WI G})"
  unfolding goodman_book_consistent_def using gi_native_T6_WI_refutation by blast

corollary gi_native_T6_RS_inconsistent:
  "sg_rich G \<Longrightarrow> \<not> goodman_book_consistent gb_signature G
    (gb_T6_core G \<union> {gb_strong_L2 G, gb_RS G})"
  unfolding goodman_book_consistent_def using gi_native_T6_RS_refutation by blast

corollary gi_native_central_T6_Inv_inconsistent:
  "sg_rich G \<Longrightarrow> \<not> goodman_book_consistent gb_signature G
    (gb_recombination_PP_zeroary_exhaustion G \<union> {gb_L2 G, gb_Inv G})"
  unfolding goodman_book_consistent_def using gi_native_central_T6_Inv_refutation by blast

corollary gi_native_central_T6_TU_inconsistent:
  "sg_rich G \<Longrightarrow> \<not> goodman_book_consistent gb_signature G
    (gb_recombination_PP_zeroary_exhaustion G \<union> {gb_L2 G, gb_TU G})"
  unfolding goodman_book_consistent_def using gi_native_central_T6_TU_refutation by blast

corollary gi_native_central_T6_WI_inconsistent:
  "sg_rich G \<Longrightarrow> \<not> goodman_book_consistent gb_signature G
    (gb_recombination_PP_zeroary_exhaustion G \<union> {gb_L2 G, gb_WI G})"
  unfolding goodman_book_consistent_def using gi_native_central_T6_WI_refutation by blast

corollary gi_native_central_T6_RS_inconsistent:
  "sg_rich G \<Longrightarrow> \<not> goodman_book_consistent gb_signature G
    (gb_recombination_PP_zeroary_exhaustion G \<union> {gb_strong_L2 G, gb_RS G})"
  unfolding goodman_book_consistent_def using gi_native_central_T6_RS_refutation by blast

section \<open>Existing classification consequences with native inputs and outputs\<close>

theorem gi_native_WI_derives_TU:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G {gb_WI G} (gb_TU G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "[] ; {pp_WI} \<turnstile>\<^sub>CEV\<^sup>+ pp_TU"
    by (rule CEV_axiom_WI_implies_TU; simp)
  have closed_stock: "\<And>A. A \<in> {pp_WI} \<Longrightarrow> [] \<turnstile> A : Prop"
    using typed_pp_WI by auto
  have admitted_stock: "\<And>A. A \<in> {pp_WI} \<Longrightarrow> gi_constants_admitted k gb_signature A"
    using gi_WI_admitted[OF names] by auto
  have translated: "goodman_book_proves gb_signature G
      (image (gi_to_book G [] k) {pp_WI}) (gi_to_book G [] k pp_TU)"
    by (rule gi_CEV_axiom_preservation_in_signature[
      OF rich original closed_stock _ _ admitted_stock gi_TU_admitted[OF names]]; simp)
  show ?thesis using translated
    by (simp only: image_insert image_empty gi_WI_native_translation[OF names] gi_TU_native_translation[OF names])
qed

theorem gi_native_T1_WI_derives_Inv:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (insert (gb_WI G) (gb_T1_axioms G)) (gb_Inv G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "goodman_book_proves gb_signature G (gi_T1_WI_native_stock G k) (gi_to_book G [] k pp_Inv)"
    by (rule gi_T1_WI_implies_Inv_translated[OF rich names])
  show ?thesis using original
    by (simp only: gi_T1_WI_native_stock_def gi_WI_native_translation[OF names] gi_Inv_native_translation[OF names])
qed

theorem gi_native_T1_TU_derives_Inv:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (insert (gb_TU G) (gb_T1_axioms G)) (gb_Inv G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "goodman_book_proves gb_signature G
      (insert (gi_to_book G [] k pp_TU) (gb_T1_axioms G)) (gi_to_book G [] k pp_Inv)"
    by (rule gi_TU_Exhaustion_implies_Inv_translated[OF rich names])
  show ?thesis using original
    by (simp only: gi_TU_native_translation[OF names] gi_Inv_native_translation[OF names])
qed

text \<open>
  The last three statements concern named axiom-extension derivability,
  not an unproved deduction-theorem conversion to a single implication.
  The T1 stock contains logical purity, application closure, and zeroary
  Exhaustion; the WI→Inv and TU→Inv consequences retain that stock and
  introduce no PP, L2, or existence-of-fun′ premise. No new Inv→WI theorem
  is asserted by these transfers.
\<close>

end
