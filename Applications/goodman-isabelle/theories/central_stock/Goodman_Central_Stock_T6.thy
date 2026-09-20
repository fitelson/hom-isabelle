theory Goodman_Central_Stock_T6
  imports Goodman_Native_Fun_Prime
begin

section \<open>T6 over the repaired native central stock\<close>

definition gb_central_T6_extension where
  "gb_central_T6_extension G k S = gb_recombination_PP_zeroary_exhaustion G \<union> image (gi_to_book G [] k) S"

text \<open>
  The native central stock includes unique fundamentality, Recombination,
  PP, and zeroary Exhaustion. It supplies ∃fun′ by the preceding theorem.
  S contains only each route's extra principles. Their formulas remain
  translated from the original encoding; their assumptions are unchanged.
\<close>

lemma gi_central_T6_language:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and extras: "S \<subseteq> gi_T6_extra_inventory"
    and member: "B \<in> gb_central_T6_extension G k S"
  shows "book_theory_formula gb_signature G B"
proof (cases "B \<in> gb_recombination_PP_zeroary_exhaustion G")
  case True
  show ?thesis by (rule gb_repaired_PP_language[OF rich True])
next
  case False
  have "B \<in> gi_T6_signature_support G k"
    using member False extras unfolding gb_central_T6_extension_def gi_T6_signature_support_def by blast
  then show ?thesis by (rule gi_T6_signature_support_language[OF rich names])
qed

lemma gi_central_T6_support:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and extras: "S \<subseteq> gi_T6_extra_inventory"
    and member: "B \<in> pp_recombination_zeroary_exhaustion_axioms \<union> S"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_central_T6_extension G k S) (gi_to_book G [] k B)"
proof (cases "B \<in> pp_recombination_zeroary_exhaustion_axioms")
  case True
  have original: "B \<in> insert pp_zeroary_exhaustion pp_recombination_PP_axioms"
    using True by (simp only: pp_recombination_zeroary_exhaustion_axioms_def)
  have base: "goodman_book_proves (\<lambda>_. UNIV) G (gb_recombination_PP_zeroary_exhaustion G) (gi_to_book G [] k B)"
    by (rule gi_repaired_package_support[OF rich names original])
  show ?thesis by (rule goodman_book_mono[OF base]; auto simp: gb_central_T6_extension_def)
next
  case False
  have bs: "B \<in> S" using member False by blast
  have bm: "B \<in> gi_T6_extra_inventory" using extras bs by blast
  have language: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G [] k B)"
    by (rule gi_to_book_language[OF rich gi_T6_extra_inventory_typed[OF bm] _ gi_constants_universal]; simp)
  show ?thesis by (rule goodman_book_proves.Axiom[OF _ language]; auto simp: gb_central_T6_extension_def bs)
qed

theorem gi_central_T6_refutation_transfer:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and extras: "S \<subseteq> gi_T6_extra_inventory"
    and refutation: "[] ; pp_recombination_zeroary_exhaustion_axioms \<union> S \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
  shows "goodman_book_proves gb_signature G (gb_central_T6_extension G k S) (book_bottom G)"
proof -
  have closed: "\<And>B. B \<in> pp_recombination_zeroary_exhaustion_axioms \<union> S \<Longrightarrow> [] \<turnstile> B : Prop"
    using extras by (auto intro: pp_recombination_zeroary_exhaustion_axioms_typed gi_T6_extra_inventory_typed)
  have image: "goodman_book_proves (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) (pp_recombination_zeroary_exhaustion_axioms \<union> S)) (book_bottom G)"
    by (rule gi_CEV_closed_refutation[OF rich refutation closed])
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_central_T6_extension G k S) (book_bottom G)"
    by (rule goodman_book_cut[OF image]; auto intro: gi_central_T6_support[OF rich names extras])
  show ?thesis
  proof (rule gi_goodman_foreign_constants_eliminate[OF rich universal])
    fix B assume "B \<in> gb_central_T6_extension G k S"
    then show "book_theory_formula gb_signature G B" by (rule gi_central_T6_language[OF rich names extras])
  next
    show "named_in_signature gb_signature (book_bottom G)"
      by (rule book_language_signature[OF book_bottom_language[OF rich]])
  qed
qed

theorem gi_central_T6_Inv_refutation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_central_T6_extension G k {pp_L2, pp_Inv}) (book_bottom G)"
proof (rule gi_central_T6_refutation_transfer[OF rich names])
  show "{pp_L2, pp_Inv} \<subseteq> gi_T6_extra_inventory" by (auto simp: gi_T6_extra_inventory_def)
  show "[] ; pp_recombination_zeroary_exhaustion_axioms \<union> {pp_L2, pp_Inv} \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    using CEV_Goodman_T6_Inv_repaired_central_stock by (simp only: pp_repaired_T6_Inv_axioms_def)
qed

theorem gi_central_T6_TU_refutation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_central_T6_extension G k {pp_L2, pp_TU}) (book_bottom G)"
proof (rule gi_central_T6_refutation_transfer[OF rich names])
  show "{pp_L2, pp_TU} \<subseteq> gi_T6_extra_inventory" by (auto simp: gi_T6_extra_inventory_def)
  have stock: "pp_recombination_zeroary_exhaustion_axioms \<union> {pp_L2, pp_TU} = pp_repaired_T6_TU_axioms"
    unfolding pp_repaired_T6_TU_axioms_def by auto
  show "[] ; pp_recombination_zeroary_exhaustion_axioms \<union> {pp_L2, pp_TU} \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    unfolding stock by (rule CEV_Goodman_T6_TU_repaired_central_stock)
qed

theorem gi_central_T6_WI_refutation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_central_T6_extension G k {pp_L2, pp_WI}) (book_bottom G)"
proof (rule gi_central_T6_refutation_transfer[OF rich names])
  show "{pp_L2, pp_WI} \<subseteq> gi_T6_extra_inventory" by (auto simp: gi_T6_extra_inventory_def)
  have stock: "pp_recombination_zeroary_exhaustion_axioms \<union> {pp_L2, pp_WI} = pp_repaired_T6_WI_axioms"
    unfolding pp_repaired_T6_WI_axioms_def by auto
  show "[] ; pp_recombination_zeroary_exhaustion_axioms \<union> {pp_L2, pp_WI} \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    unfolding stock by (rule CEV_Goodman_T6_WI_repaired_central_stock)
qed

theorem gi_central_T6_RS_refutation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gb_central_T6_extension G k {pp_strong_L2, pp_RS}) (book_bottom G)"
proof (rule gi_central_T6_refutation_transfer[OF rich names])
  show "{pp_strong_L2, pp_RS} \<subseteq> gi_T6_extra_inventory" by (auto simp: gi_T6_extra_inventory_def)
  have stock: "pp_recombination_zeroary_exhaustion_axioms \<union> {pp_strong_L2, pp_RS} = pp_repaired_T6_RS_axioms"
    unfolding pp_repaired_T6_RS_axioms_def by auto
  show "[] ; pp_recombination_zeroary_exhaustion_axioms \<union> {pp_strong_L2, pp_RS} \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
    unfolding stock by (rule CEV_Goodman_T6_RS_repaired_central_stock)
qed

end
