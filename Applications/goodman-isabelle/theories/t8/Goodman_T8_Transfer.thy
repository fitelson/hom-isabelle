theory Goodman_T8_Transfer
  imports Goodman_Legacy_T8_Growth.Bacon_PP_Goodman_T8_Growth
    Goodman_Integration_Numbered.Goodman_T7_Transfer
begin

section \<open>Signature guards for T8's operators and formulas\<close>

lemma gi_T8_same_kind_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature X \<Longrightarrow>
    gi_constants_admitted k gb_signature Y \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_same_kind X Y)"
  by (simp add: pp_same_kind_def gi_T2a_group_member_admitted pp_compose_def
    shift_def gi_constants_rename)

lemma gi_T8_base_admitted:
  "X \<in> set pp_T8_base_operators \<Longrightarrow> gi_constants_admitted k gb_signature X"
  by (auto simp: pp_T8_base_operators_def pp_identity_operator_def gd_box_op_def
    pp_T8_diamond_operator_def gd_true_op_def gd_false_op_def ObjTrue_def ObjFalse_def)

lemma gi_T8_representation_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature p \<Longrightarrow>
    gi_constants_admitted k gb_signature X \<Longrightarrow> gi_constants_admitted k gb_signature q \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_T8_representation p X q)"
  by (simp add: pp_T8_representation_def gi_T2_fun_prime_admitted pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def)

lemma gi_T8_not_same_all_admitted:
  assumes names: "gi_goodman_names k" and x: "gi_constants_admitted k gb_signature X"
    and ys: "\<And>Y. Y \<in> set Ys \<Longrightarrow> gi_constants_admitted k gb_signature Y"
  shows "gi_constants_admitted k gb_signature (pp_T8_not_same_all X Ys)"
  using ys by (induction Ys) (auto simp: ObjTrue_def intro: gi_T8_same_kind_admitted[OF names x])

lemma gi_T8_pairwise_kind_admitted:
  assumes names: "gi_goodman_names k"
    and xs: "\<And>X. X \<in> set Xs \<Longrightarrow> gi_constants_admitted k gb_signature X"
  shows "gi_constants_admitted k gb_signature (pp_T8_pairwise_kind_distinct Xs)"
  using xs by (induction Xs) (auto simp: ObjTrue_def intro: gi_T8_not_same_all_admitted[OF names])

lemma gi_T8_base_kind_claim_admitted:
  assumes names: "gi_goodman_names k"
  shows "gi_constants_admitted k gb_signature pp_T8_base_kind_claim"
  unfolding pp_T8_base_kind_claim_def
  by (rule gi_T8_pairwise_kind_admitted[OF names gi_T8_base_admitted])

lemma gi_T8_disjoin_admitted:
  assumes terms: "\<And>A. A \<in> set As \<Longrightarrow> gi_constants_admitted k gb_signature A"
  shows "gi_constants_admitted k gb_signature (pp_T8_disjoin As)"
  using terms by (induction As rule: pp_T8_disjoin.induct) (auto simp: ObjFalse_def ObjTrue_def)

lemma gi_T8_kind_atom_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature B \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_T8_kind_atom B)"
  by (simp add: pp_T8_kind_atom_def gi_T2_fun_prime_admitted)

lemma gi_T8_kind_property_admitted:
  assumes names: "gi_goodman_names k" and subset: "set Bs \<subseteq> set pp_T8_base_operators"
  shows "gi_constants_admitted k gb_signature (pp_T8_kind_property Bs)"
  unfolding pp_T8_kind_property_def gi_constants_admitted.simps
  by (rule gi_T8_disjoin_admitted;
    use subset in \<open>auto intro: gi_T8_kind_atom_admitted[OF names] gi_T8_base_admitted\<close>)

lemma gi_T8_growth_operator_admitted:
  assumes names: "gi_goodman_names k" and member: "X \<in> set pp_T8_growth_operators"
  shows "gi_constants_admitted k gb_signature X"
proof -
  obtain Bs where bs: "Bs \<in> set pp_T8_nonempty_subsets" and shape: "X = pp_T8_kind_property Bs"
    using member unfolding pp_T8_growth_operators_def by auto
  show ?thesis unfolding shape
    by (rule gi_T8_kind_property_admitted[OF names pp_T8_nonempty_subset_is_base_subset[OF bs]])
qed

lemma gi_T8_neq_all_admitted:
  assumes a: "gi_constants_admitted k gb_signature A"
    and bs: "\<And>B. B \<in> set Bs \<Longrightarrow> gi_constants_admitted k gb_signature B"
  shows "gi_constants_admitted k gb_signature (pp_T8_neq_all \<sigma> A Bs)"
  using bs by (induction Bs) (auto simp: ObjTrue_def a)

lemma gi_T8_pairwise_distinct_admitted:
  assumes terms: "\<And>A. A \<in> set As \<Longrightarrow> gi_constants_admitted k gb_signature A"
  shows "gi_constants_admitted k gb_signature (pp_T8_pairwise_distinct \<sigma> As)"
  using terms by (induction As) (auto simp: ObjTrue_def intro: gi_T8_neq_all_admitted)

lemma gi_T8_growth_claim_admitted:
  assumes names: "gi_goodman_names k" and r: "gi_constants_admitted k gb_signature r"
  shows "gi_constants_admitted k gb_signature (pp_T8_growth_claim r)"
  unfolding pp_T8_growth_claim_def gi_constants_admitted.simps
  by (intro conjI gi_T8_pairwise_distinct_admitted;
    auto intro: gi_T8_growth_operator_admitted[OF names] simp: r)

lemma gi_T8_growth_result_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature pp_T8_growth_result"
  by (simp add: pp_T8_growth_result_def gi_T2_fun_prime_admitted gi_T8_growth_claim_admitted)

section \<open>T8b: uniqueness of represented kind requires only L2\<close>

theorem gi_T8b_kind_uniqueness_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and pt: "\<Gamma> \<turnstile> p : Prop" and xt: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and qt: "\<Gamma> \<turnstile> q : Prop" and yt: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and st: "\<Gamma> \<turnstile> s : Prop" and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and pa: "gi_constants_admitted k gb_signature p" and xa: "gi_constants_admitted k gb_signature X"
    and qa: "gi_constants_admitted k gb_signature q" and ya: "gi_constants_admitted k gb_signature Y"
    and sa: "gi_constants_admitted k gb_signature s"
  shows "goodman_book_proves gb_signature G {gi_to_book G [] k pp_L2}
    (gi_to_book G ns k (Imp (Conj (pp_T8_representation p X q) (pp_T8_representation p Y s))
      (pp_same_kind X Y)))"
proof -
  let ?A = "Imp (Conj (pp_T8_representation p X q) (pp_T8_representation p Y s)) (pp_same_kind X Y)"
  have source: "\<Gamma> ; {pp_L2} \<turnstile>\<^sub>CEV\<^sup>+ ?A"
    by (rule CEV_Goodman_T8_kind_uniqueness[OF _ pt xt qt yt st]; simp)
  have closed: "\<And>B. B \<in> {pp_L2} \<Longrightarrow> [] \<turnstile> B : Prop"
    by (auto intro: typed_pp_L2)
  have axioms: "\<And>B. B \<in> {pp_L2} \<Longrightarrow> gi_constants_admitted k gb_signature B"
    by (auto intro: gi_L2_admitted[OF names])
  have conclusion: "gi_constants_admitted k gb_signature ?A"
    using gi_T8_representation_admitted[OF names pa xa qa]
      gi_T8_representation_admitted[OF names pa ya sa] gi_T8_same_kind_admitted[OF names xa ya] by simp
  show ?thesis using gi_CEV_axiom_preservation_in_signature[OF rich source closed chart distinct axioms conclusion]
    by (simp only: image_insert image_empty)
qed

section \<open>T8a: ten base-kind separations, with their exact stocks\<close>

text \<open>
  The first three source pair theorems use the purity/application/PP core.
  The seven pairs involving a constant operator need no added axioms at all,
  although their fun′(r) antecedent remains. All ten are displayed below;
  the combined five-kind statement uses the common core. L2 is not assumed
  for T8a. The same-kind formulas here remain explicitly translated.
\<close>

lemma gi_T8a_pair_core:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and rt: "G r = Prop"
    and source: "[Prop] ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind X Y))"
    and x: "X \<in> set pp_T8_base_operators" and y: "Y \<in> set pp_T8_base_operators"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind X Y))))"
proof (rule gi_T2_PP_native_preservation[OF rich names source])
  show "map G [r] = [Prop]" using rt by simp
  show "distinct [r]" by simp
  show "gi_constants_admitted k gb_signature (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind X Y)))"
    using gi_T8_same_kind_admitted[OF names gi_T8_base_admitted[OF x] gi_T8_base_admitted[OF y]]
    by (simp add: gi_T2_fun_prime_admitted[OF names])
qed

lemma gi_T8a_pair_empty:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and rt: "G r = Prop"
    and source: "[Prop] ; {} \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind X Y))"
    and x: "X \<in> set pp_T8_base_operators" and y: "Y \<in> set pp_T8_base_operators"
  shows "goodman_book_proves gb_signature G {}
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind X Y))))"
proof -
  let ?A = "Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind X Y))"
  have chart: "map G [r] = [Prop]" using rt by simp
  have admitted: "gi_constants_admitted k gb_signature ?A"
    using gi_T8_same_kind_admitted[OF names gi_T8_base_admitted[OF x] gi_T8_base_admitted[OF y]]
    by (simp add: gi_T2_fun_prime_admitted[OF names])
  have "goodman_book_proves gb_signature G (image (gi_to_book G [] k) {}) (gi_to_book G [r] k ?A)"
    by (rule gi_CEV_axiom_preservation_in_signature[OF rich source _ chart _ _ admitted]; simp)
  then show ?thesis by (simp only: image_empty)
qed

context
  fixes G k r
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and rt: "G r = Prop"
begin

theorem gi_T8a_Id_Box_translated:
  "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind pp_identity_operator gd_box_op))))"
  by (rule gi_T8a_pair_core[OF rich names rt CEV_Goodman_T8a_Id_Box[OF subset_refl typed_var0]];
    simp add: pp_T8_base_operators_def)

theorem gi_T8a_Id_Diamond_translated:
  "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind pp_identity_operator pp_T8_diamond_operator))))"
  by (rule gi_T8a_pair_core[OF rich names rt CEV_Goodman_T8a_Id_Diamond[OF subset_refl typed_var0]];
    simp add: pp_T8_base_operators_def)

theorem gi_T8a_Box_Diamond_translated:
  "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind gd_box_op pp_T8_diamond_operator))))"
  by (rule gi_T8a_pair_core[OF rich names rt CEV_Goodman_T8a_Box_Diamond[OF subset_refl typed_var0]];
    simp add: pp_T8_base_operators_def)

theorem gi_T8a_Id_Ktop_translated:
  "goodman_book_proves gb_signature G {}
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind pp_identity_operator gd_true_op))))"
  by (rule gi_T8a_pair_empty[OF rich names rt CEV_Goodman_T8a_Id_Ktop[OF typed_var0]];
    simp add: pp_T8_base_operators_def)

theorem gi_T8a_Box_Ktop_translated:
  "goodman_book_proves gb_signature G {}
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind gd_box_op gd_true_op))))"
  by (rule gi_T8a_pair_empty[OF rich names rt CEV_Goodman_T8a_Box_Ktop[OF typed_var0]];
    simp add: pp_T8_base_operators_def)

theorem gi_T8a_Diamond_Ktop_translated:
  "goodman_book_proves gb_signature G {}
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind pp_T8_diamond_operator gd_true_op))))"
  by (rule gi_T8a_pair_empty[OF rich names rt CEV_Goodman_T8a_Diamond_Ktop[OF typed_var0]];
    simp add: pp_T8_base_operators_def)

theorem gi_T8a_Id_Kbot_translated:
  "goodman_book_proves gb_signature G {}
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind pp_identity_operator gd_false_op))))"
  by (rule gi_T8a_pair_empty[OF rich names rt CEV_Goodman_T8a_Id_Kbot[OF typed_var0]];
    simp add: pp_T8_base_operators_def)

theorem gi_T8a_Box_Kbot_translated:
  "goodman_book_proves gb_signature G {}
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind gd_box_op gd_false_op))))"
  by (rule gi_T8a_pair_empty[OF rich names rt CEV_Goodman_T8a_Box_Kbot[OF typed_var0]];
    simp add: pp_T8_base_operators_def)

theorem gi_T8a_Diamond_Kbot_translated:
  "goodman_book_proves gb_signature G {}
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind pp_T8_diamond_operator gd_false_op))))"
  by (rule gi_T8a_pair_empty[OF rich names rt CEV_Goodman_T8a_Diamond_Kbot[OF typed_var0]];
    simp add: pp_T8_base_operators_def)

theorem gi_T8a_Ktop_Kbot_translated:
  "goodman_book_proves gb_signature G {}
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (Neg (pp_same_kind gd_true_op gd_false_op))))"
  by (rule gi_T8a_pair_empty[OF rich names rt CEV_Goodman_T8a_Ktop_Kbot[OF typed_var0]];
    simp add: pp_T8_base_operators_def)

end

theorem gi_T8a_five_kinds_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and ra: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gi_to_book G ns k (Imp (pp_fun_prime r) pp_T8_base_kind_claim))"
proof (rule gi_T2_PP_native_preservation[OF rich names CEV_Goodman_T8a[OF subset_refl rt] chart distinct])
  show "gi_constants_admitted k gb_signature (Imp (pp_fun_prime r) pp_T8_base_kind_claim)"
    using gi_T2_fun_prime_admitted[OF names ra] gi_T8_base_kind_claim_admitted[OF names] by simp
qed

section \<open>T8c: transfer over the same core-plus-L2 stock as T7a\<close>

lemma gi_T8_stocks_as_T7:
  "pp_T8_axioms = pp_T7_axioms" "pp_T8_full_axioms = pp_T7_full_axioms"
  by (simp_all add: pp_T8_axioms_def pp_T7_axioms_def pp_T8_full_axioms_def pp_T7_full_axioms_def)

lemma gi_T8_L2_native_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and source: "\<Gamma> ; pp_T8_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns" and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gi_T7_native_axioms G k) (gi_to_book G ns k A)"
proof -
  have old: "\<Gamma> ; pp_T7_axioms \<turnstile>\<^sub>CEV\<^sup>+ A" using source by (simp only: gi_T8_stocks_as_T7)
  have image: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) pp_T7_axioms) (gi_to_book G ns k A)"
    by (rule gi_CEV_axiom_preservation[OF rich old gi_T7_axioms_closed chart distinct])
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gi_T7_native_axioms G k) (gi_to_book G ns k A)"
    by (rule goodman_book_mono[OF image gi_T7_stock_inclusion[OF rich names]])
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich old chart admitted
    universal gi_T7_native_axioms_language[OF rich names]])
qed

theorem gi_T8c_growth_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and rt: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>"
    and distinct: "distinct ns" and ra: "gi_constants_admitted k gb_signature r"
  shows "goodman_book_proves gb_signature G (gi_T7_native_axioms G k)
    (gi_to_book G ns k (Imp (pp_fun_prime r) (pp_T8_growth_claim r)))"
proof -
  have core: "pp_T6_core_PP_axioms \<subseteq> pp_T8_axioms" and l2: "pp_L2 \<in> pp_T8_axioms"
    by (auto simp: pp_T8_axioms_def)
  have source: "\<Gamma> ; pp_T8_axioms \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime r) (pp_T8_growth_claim r)"
    by (rule CEV_Goodman_T8c[OF core l2 rt])
  show ?thesis by (rule gi_T8_L2_native_preservation[OF rich names source chart distinct];
    simp add: gi_T2_fun_prime_admitted[OF names ra] gi_T8_growth_claim_admitted[OF names ra])
qed

theorem gi_T8c_operator_purity:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and distinct: "distinct ns"
    and member: "X \<in> set pp_T8_growth_operators"
  shows "goodman_book_proves gb_signature G (gb_T6_core G)
    (gb_pure gb_unary (gi_to_book G ns k X))"
proof -
  have local: "map G ns ; pp_T6_core_PP_axioms ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty X"
    by (rule CEVs_pure_pp_T8_growth_operator[OF subset_refl member])
  have source: "map G ns ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty X"
    using local by (simp only: CEV_axiom_from_empty_iff)
  have admitted: "gi_constants_admitted k gb_signature (pp_pure pp_unary_ty X)"
    using names gi_T8_growth_operator_admitted[OF names member]
    by (simp add: pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def)
  have translated: "goodman_book_proves gb_signature G (gb_T6_core G) (gi_to_book G ns k (pp_pure pp_unary_ty X))"
    by (rule gi_T2_PP_native_preservation[OF rich names source refl distinct admitted])
  show ?thesis using translated by (simp only: gi_pure_translation[OF names] pp_unary_ty_def)
qed

section \<open>Native conjunctions of object-language inequalities\<close>

fun gb_T8_neq_all where
  "gb_T8_neq_all G ns \<sigma> A [] = gi_old_top G ns"
| "gb_T8_neq_all G ns \<sigma> A (B # Bs) =
    book_and G (book_not G (book_leibniz G \<sigma> A B)) (gb_T8_neq_all G ns \<sigma> A Bs)"

fun gb_T8_pairwise_distinct where
  "gb_T8_pairwise_distinct G ns \<sigma> [] = gi_old_top G ns"
| "gb_T8_pairwise_distinct G ns \<sigma> (A # As) =
    book_and G (gb_T8_neq_all G ns \<sigma> A As) (gb_T8_pairwise_distinct G ns \<sigma> As)"

lemma gi_T8_neq_all_translation:
  "gi_to_book G ns k (pp_T8_neq_all \<sigma> A Bs) =
    gb_T8_neq_all G ns \<sigma> (gi_to_book G ns k A) (map (gi_to_book G ns k) Bs)"
  by (induction Bs) (simp_all add: gi_true_translation)

lemma gi_T8_pairwise_distinct_translation:
  "gi_to_book G ns k (pp_T8_pairwise_distinct \<sigma> As) =
    gb_T8_pairwise_distinct G ns \<sigma> (map (gi_to_book G ns k) As)"
  by (induction As) (simp_all add: gi_T8_neq_all_translation gi_true_translation)

definition gi_T8_growth_terms where
  "gi_T8_growth_terms G ns k = map (gi_to_book G ns k) pp_T8_growth_operators"

theorem gi_T8c_listed_operators_pure:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and distinct: "distinct ns"
    and member: "X \<in> set (gi_T8_growth_terms G ns k)"
  shows "goodman_book_proves gb_signature G (gb_T6_core G) (gb_pure gb_unary X)"
proof -
  obtain Y where old: "Y \<in> set pp_T8_growth_operators" and shape: "X = gi_to_book G ns k Y"
    using member unfolding gi_T8_growth_terms_def by auto
  show ?thesis unfolding shape by (rule gi_T8c_operator_purity[OF rich names distinct old])
qed

lemma gi_T8_growth_terms_length:
  "length (gi_T8_growth_terms G ns k) = 31"
  by (simp add: gi_T8_growth_terms_def)

lemma gi_T8_growth_values_length:
  "length (map (\<lambda>X. NApp X r) (gi_T8_growth_terms G ns k)) = 31"
  by (simp add: gi_T8_growth_terms_length)

definition gb_T8_growth_claim where
  "gb_T8_growth_claim G ns k r = book_and G
    (gb_T8_pairwise_distinct G ns gb_unary (gi_T8_growth_terms G ns k))
    (gb_T8_pairwise_distinct G ns Prop (map (\<lambda>X. NApp X r) (gi_T8_growth_terms G ns k)))"

lemma gi_T8_growth_claim_translation:
  "gi_to_book G ns k (pp_T8_growth_claim r) = gb_T8_growth_claim G ns k (gi_to_book G ns k r)"
  by (simp add: pp_T8_growth_claim_def gb_T8_growth_claim_def gi_T8_growth_terms_def
    gi_T8_pairwise_distinct_translation pp_unary_ty_def map_map comp_def)

theorem gi_T8c_growth:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k" and rt: "G r = Prop"
  shows "goodman_book_proves gb_signature G (gi_T7_native_axioms G k)
    (book_imp (gb_T2a_fun_prime_on_chart G [r] (NVar r)) (gb_T8_growth_claim G [r] k (NVar r)))"
proof -
  have typed: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have chart: "map G [r] = [Prop]" using rt by simp
  have translated: "goodman_book_proves gb_signature G (gi_T7_native_axioms G k)
    (gi_to_book G [r] k (Imp (pp_fun_prime (Var 0)) (pp_T8_growth_claim (Var 0))))"
    by (rule gi_T8c_growth_translated[OF rich names typed chart]; simp)
  show ?thesis using translated by (simp add: gi_T5_fun_prime_head_translation[OF names]
    gi_T8_growth_claim_translation)
qed

section \<open>The closed existence result and its repaired-central-stock version\<close>

theorem gi_T8c_closed_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gi_T7_native_full_axioms G k)
    (gi_to_book G [] k pp_T8_growth_result)"
proof -
  have source: "[] ; pp_T7_full_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_T8_growth_result"
    using CEV_Goodman_T8c_closed by (simp only: gi_T8_stocks_as_T7)
  have image: "goodman_book_proves (\<lambda>_. UNIV) G (image (gi_to_book G [] k) pp_T7_full_axioms)
    (gi_to_book G [] k pp_T8_growth_result)"
    by (rule gi_CEV_axiom_preservation[OF rich source gi_T7_full_axioms_closed]; simp)
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gi_T7_native_full_axioms G k)
    (gi_to_book G [] k pp_T8_growth_result)"
    by (rule goodman_book_mono[OF image gi_T7_full_stock_inclusion[OF rich names]])
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich source _ gi_T8_growth_result_admitted[OF names]
    universal gi_T7_native_full_axioms_language[OF rich names]]; simp)
qed

definition gb_T8_growth_result where
  "gb_T8_growth_result G k = (let r = gb_x G Prop in
    book_exists G r (book_and G (gb_T2a_fun_prime_on_chart G [r] (NVar r))
      (gb_T8_growth_claim G [r] k (NVar r))))"

lemma gi_T8_growth_result_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k pp_T8_growth_result = gb_T8_growth_result G k"
  by (simp add: pp_T8_growth_result_def gb_T8_growth_result_def
    gi_T5_fun_prime_head_translation gi_T8_growth_claim_translation gb_x_def[symmetric] Let_def)

theorem gi_T8c_closed:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gi_T7_native_full_axioms G k) (gb_T8_growth_result G k)"
  using gi_T8c_closed_translated[OF rich names]
  by (simp only: gi_T8_growth_result_translation[OF names])

lemma gi_T8_full_to_repaired:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "goodman_book_proves gb_signature G (gi_T7_native_full_axioms G k) A"
  shows "goodman_book_proves gb_signature G (gi_T7_repaired_native_axioms G k) A"
proof (rule goodman_book_cut[OF derivation])
  fix B assume member: "B \<in> gi_T7_native_full_axioms G k"
  show "goodman_book_proves gb_signature G (gi_T7_repaired_native_axioms G k) B"
  proof (cases "B = gb_exists_fun_prime G")
    case True
    show ?thesis unfolding True by (rule goodman_book_mono[OF gi_repaired_native_exists_fun_prime[OF rich]];
      auto simp: gi_T7_repaired_native_axioms_def)
  next
    case False
    have old: "B \<in> gi_T7_native_axioms G k"
      using member False unfolding gi_T7_native_full_axioms_def by blast
    have new: "B \<in> gi_T7_repaired_native_axioms G k"
      using old gi_T7_native_core_in_repaired by blast
    show ?thesis by (rule goodman_book_proves.Axiom[OF new gi_T7_native_axioms_language[OF rich names old]])
  qed
qed

theorem gi_T8c_repaired_central_stock:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "goodman_book_proves gb_signature G (gi_T7_repaired_native_axioms G k) (gb_T8_growth_result G k)"
  by (rule gi_T8_full_to_repaired[OF rich names gi_T8c_closed[OF rich names]])

text \<open>
  The pairwise predicates are native object-language conjunctions of negated
  Leibniz identities. Their 31 operator arguments are the translated explicit
  source construction; an independent native reconstruction of the kind-property
  builders and L2/same-kind syntax remains separate. The purity companion is a
  proved theorem for each listed operator, not a conjunct silently attributed
  to the inequality formula. It uses the PP core but needs neither L2 nor a
  fun′ antecedent. The 31/31 inequalities require both L2 and fun′(r).

  The result is 31 pairwise-distinct pure operators and 31 pairwise-distinct
  propositions, conditional on a fun′ witness (or using the stated repaired
  central stock to derive one). It does NOT assert 31 distinct kinds, iteration
  of the construction, infinitely many kinds, or consistency of any premise.
\<close>

end
