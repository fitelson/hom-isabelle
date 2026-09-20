theory Goodman_T6_Restricted_Signature
  imports Goodman_Restricted_Signature_Transfer
begin

section \<open>The T6 extra assumptions use only the declared Pure/Fun signature\<close>

lemma gi_exists_fun_prime_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_exists_fun_prime"
  by (simp add: pp_exists_fun_prime_def pp_fun_prime_def pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def shift_by_def gi_constants_rename)

lemma gi_L2_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_L2"
  by (simp add: pp_L2_def pp_fun_prime_def pp_same_kind_def pp_group_member_def
    pp_reversible_def pp_compose_def pp_identity_operator_def pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def shift_by_def shift_def gi_constants_rename)

lemma gi_Inv_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_Inv"
  by (simp add: pp_Inv_def pp_group_member_def pp_reversible_def pp_compose_def
    pp_identity_operator_def pp_negation_operator_def pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def shift_def gi_constants_rename)

lemma gi_TU_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_TU"
  by (simp add: pp_TU_def pp_group_member_def pp_reversible_def pp_compose_def
    pp_identity_operator_def pp_truth_preserving_def pp_truth_flipping_def pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def shift_def gi_constants_rename)

lemma gi_WI_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_WI"
  by (simp add: pp_WI_def pp_biconditional_member_def pp_biconditional_operator_def pp_biconditional_builder_def
    pp_group_member_def pp_reversible_def pp_compose_def pp_identity_operator_def pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def shift_def gi_constants_rename)

lemma gi_strong_L2_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_strong_L2"
  by (simp add: pp_strong_L2_def pp_strong_same_kind_def pp_fun_prime_def
    pp_group_member_def pp_reversible_def pp_compose_def pp_identity_operator_def pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def shift_by_def shift_def gi_constants_rename)

lemma gi_RS_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_RS"
  by (simp add: pp_RS_def pp_rigid_specification_def pp_spec_instantiated_def
    pp_spec_only_fun_prime_def pp_spec_rigid_def pp_fun_prime_def pp_group_member_def
    pp_reversible_def pp_compose_def pp_identity_operator_def pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def shift_by_def shift_def gi_constants_rename)

text \<open>
  The next set is a language-checking inventory, NOT an axiom package.
  Each route below keeps its original extra assumptions; none is enlarged
  to include all entries of this inventory.
\<close>

definition gi_T6_extra_inventory where
  "gi_T6_extra_inventory = {pp_exists_fun_prime, pp_L2, pp_Inv, pp_TU, pp_WI, pp_strong_L2, pp_RS}"

lemma gi_T6_extra_inventory_typed:
  "A \<in> gi_T6_extra_inventory \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding gi_T6_extra_inventory_def
  by (auto intro: typed_pp_exists_fun_prime typed_pp_L2 typed_pp_Inv typed_pp_TU typed_pp_WI typed_pp_strong_L2 typed_pp_RS)

lemma gi_T6_extra_inventory_admitted:
  "gi_goodman_names k \<Longrightarrow> A \<in> gi_T6_extra_inventory \<Longrightarrow> gi_constants_admitted k gb_signature A"
  unfolding gi_T6_extra_inventory_def
  by (auto intro: gi_exists_fun_prime_admitted gi_L2_admitted gi_Inv_admitted gi_TU_admitted
    gi_WI_admitted gi_strong_L2_admitted gi_RS_admitted)

definition gi_T6_signature_support where
  "gi_T6_signature_support G k = gb_T6_core G \<union> image (gi_to_book G [] k) gi_T6_extra_inventory"

lemma gi_T6_signature_support_language:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and member: "A \<in> gi_T6_signature_support G k"
  shows "book_theory_formula gb_signature G A"
proof (cases "A \<in> gb_T6_core G")
  case True
  show ?thesis by (rule gb_T6_core_language[OF rich True])
next
  case False
  obtain B where member': "B \<in> gi_T6_extra_inventory" and shape: "A = gi_to_book G [] k B"
    using member False unfolding gi_T6_signature_support_def by blast
  show ?thesis unfolding shape
    by (rule gi_to_book_language[OF rich gi_T6_extra_inventory_typed[OF member'] _
      gi_T6_extra_inventory_admitted[OF names member']]; simp)
qed

lemma gi_T6_image_stocks_in_signature_support:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "image (gi_to_book G [] k) pp_T6_Inv_axioms \<subseteq> gi_T6_signature_support G k"
    and "image (gi_to_book G [] k) pp_T6_TU_axioms \<subseteq> gi_T6_signature_support G k"
    and "image (gi_to_book G [] k) pp_T6_WI_axioms \<subseteq> gi_T6_signature_support G k"
    and "image (gi_to_book G [] k) pp_T6_RS_axioms \<subseteq> gi_T6_signature_support G k"
  using gi_T6_core_inclusion[OF rich names]
  unfolding pp_T6_Inv_axioms_def pp_T6_TU_axioms_def pp_T6_WI_axioms_def pp_T6_RS_axioms_def
    gi_T6_signature_support_def gi_T6_extra_inventory_def by auto

lemma gi_T6_native_stock_in_signature_support:
  "S \<subseteq> gi_T6_extra_inventory \<Longrightarrow>
    gi_T6_native_core_extension G k S \<subseteq> gi_T6_signature_support G k"
  unfolding gi_T6_native_core_extension_def gi_T6_signature_support_def by auto

lemma gi_T6_refutation_restrict:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "goodman_book_proves (\<lambda>_. UNIV) G T (book_bottom G)"
    and support: "T \<subseteq> gi_T6_signature_support G k"
  shows "goodman_book_proves gb_signature G T (book_bottom G)"
proof (rule gi_goodman_foreign_constants_eliminate[OF rich derivation])
  fix B assume "B \<in> T"
  then have "B \<in> gi_T6_signature_support G k" using support by blast
  then show "book_theory_formula gb_signature G B" by (rule gi_T6_signature_support_language[OF rich names])
next
  show "named_in_signature gb_signature (book_bottom G)"
    by (rule book_language_signature[OF book_bottom_language[OF rich]])
qed

section \<open>All four exact image-stock refutations in the restricted signature\<close>

theorem gi_T6_Inv_refutation_in_signature:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow>
    goodman_book_proves gb_signature G (image (gi_to_book G [] k) pp_T6_Inv_axioms) (book_bottom G)"
  by (rule gi_T6_refutation_restrict;
    (assumption | rule gi_T6_Inv_refutation | rule gi_T6_image_stocks_in_signature_support(1)); assumption)

theorem gi_T6_TU_refutation_in_signature:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow>
    goodman_book_proves gb_signature G (image (gi_to_book G [] k) pp_T6_TU_axioms) (book_bottom G)"
  by (rule gi_T6_refutation_restrict;
    (assumption | rule gi_T6_TU_refutation | rule gi_T6_image_stocks_in_signature_support(2)); assumption)

theorem gi_T6_WI_refutation_in_signature:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow>
    goodman_book_proves gb_signature G (image (gi_to_book G [] k) pp_T6_WI_axioms) (book_bottom G)"
  by (rule gi_T6_refutation_restrict;
    (assumption | rule gi_T6_WI_refutation | rule gi_T6_image_stocks_in_signature_support(3)); assumption)

theorem gi_T6_RS_refutation_in_signature:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow>
    goodman_book_proves gb_signature G (image (gi_to_book G [] k) pp_T6_RS_axioms) (book_bottom G)"
  by (rule gi_T6_refutation_restrict;
    (assumption | rule gi_T6_RS_refutation | rule gi_T6_image_stocks_in_signature_support(4)); assumption)

section \<open>The native common-core variants keep the same route extras\<close>

theorem gi_T6_native_Inv_refutation_in_signature:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G
    (gi_T6_native_core_extension G k {pp_exists_fun_prime, pp_L2, pp_Inv}) (book_bottom G)"
  by (rule gi_T6_refutation_restrict[OF rich names gi_T6_native_core_Inv_refutation[OF rich names]],
    rule gi_T6_native_stock_in_signature_support; auto simp: gi_T6_extra_inventory_def)

theorem gi_T6_native_TU_refutation_in_signature:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G
    (gi_T6_native_core_extension G k {pp_exists_fun_prime, pp_L2, pp_TU}) (book_bottom G)"
  by (rule gi_T6_refutation_restrict[OF rich names gi_T6_native_core_TU_refutation[OF rich names]],
    rule gi_T6_native_stock_in_signature_support; auto simp: gi_T6_extra_inventory_def)

theorem gi_T6_native_WI_refutation_in_signature:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G
    (gi_T6_native_core_extension G k {pp_exists_fun_prime, pp_L2, pp_WI}) (book_bottom G)"
  by (rule gi_T6_refutation_restrict[OF rich names gi_T6_native_core_WI_refutation[OF rich names]],
    rule gi_T6_native_stock_in_signature_support; auto simp: gi_T6_extra_inventory_def)

theorem gi_T6_native_RS_refutation_in_signature:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G
    (gi_T6_native_core_extension G k {pp_strong_L2, pp_RS}) (book_bottom G)"
  by (rule gi_T6_refutation_restrict[OF rich names gi_T6_native_core_RS_refutation[OF rich names]],
    rule gi_T6_native_stock_in_signature_support; auto simp: gi_T6_extra_inventory_def)

end
