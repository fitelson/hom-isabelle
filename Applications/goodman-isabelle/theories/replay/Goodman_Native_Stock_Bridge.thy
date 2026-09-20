theory Goodman_Native_Stock_Bridge
  imports Goodman_T6_Transfer
begin

section \<open>Identify the Goodman names without assuming a global renaming\<close>

text \<open>
  The map k sends Pure and Fun, at every type, to the corresponding named
  constants. No injectivity on other names is asserted or needed. The
  translation of a closed logical term contains no nonlogical names.
\<close>

definition gi_goodman_names :: "(string \<Rightarrow> otype \<Rightarrow> goodman_constant) \<Rightarrow> bool" where
  "gi_goodman_names k \<longleftrightarrow>
    (\<forall>\<tau>. k pp_pure_name \<tau> = PureName) \<and>
    (\<forall>\<tau>. k pp_fun_name \<tau> = FunName)"

lemma gi_goodman_names_satisfiable:
  "\<exists>k. gi_goodman_names k"
proof -
  have "gi_goodman_names (\<lambda>c \<tau>. if c = pp_pure_name then PureName else FunName)"
    by (simp add: gi_goodman_names_def pp_pure_name_def pp_fun_name_def)
  then show ?thesis by blast
qed

lemma gi_logical_constants_iff:
  "gi_constants_admitted k (\<lambda>_. {}) A \<longleftrightarrow> pp_logical_vocabulary A"
  unfolding pp_logical_vocabulary_def by (induction A) auto

lemma gi_Pure_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G ns k (pp_Pure \<sigma>) = gb_Pure \<sigma>"
  by (simp add: gi_goodman_names_def pp_Pure_def gb_Pure_def)

lemma gi_Fun_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G ns k (pp_Fun \<sigma>) = gb_Fun \<sigma>"
  by (simp add: gi_goodman_names_def pp_Fun_def gb_Fun_def)

lemma gi_pure_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G ns k (pp_pure \<sigma> A) = gb_pure \<sigma> (gi_to_book G ns k A)"
  by (simp add: pp_pure_def gb_pure_def gi_Pure_translation)

lemma gi_fun_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G ns k (pp_fun \<sigma> A) = gb_fun \<sigma> (gi_to_book G ns k A)"
  by (simp add: pp_fun_def gb_fun_def gi_Fun_translation)

lemma gi_PP_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G ns k pp_target_PP = gb_target_PP"
  by (simp add: pp_target_PP_def pp_purity_of_pure_def gb_target_PP_def
    gb_purity_of_pure_def gi_pure_translation gi_Pure_translation)

section \<open>Literal agreement for the nonmodal axiom constructors\<close>

lemma gi_application_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [] k (pp_application_closure \<sigma> \<tau>) = gb_application_closure G \<sigma> \<tau>"
  by (simp add: pp_application_closure_def gb_application_closure_def
    gi_pure_translation gb_x_def gb_y_def Let_def)

lemma gi_unique_fundamental_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [] k (pp_unique_fundamental \<sigma>) = gb_unique_fundamental G \<sigma>"
  by (simp add: pp_unique_fundamental_def gb_unique_fundamental_def
    gi_fun_translation gb_x_def gb_y_def Let_def)

lemma gi_no_fundamentals_translation:
  "gi_goodman_names k \<Longrightarrow>
    gi_to_book G [] k (pp_no_fundamentals \<sigma>) = gb_no_fundamentals G \<sigma>"
  by (simp add: pp_no_fundamentals_def gb_no_fundamentals_def
    gi_fun_translation gb_x_def Let_def)

text \<open>
  Logical purity gives an inclusion, not an equality: every translated old
  instance is a native instance, but no converse is asserted. Application
  closure and absence of nonpropositional fundamentals do give literal
  equalities of their formula sets. No interpretation of Pure is involved.
\<close>

theorem gi_purity_schema_inclusion:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "image (gi_to_book G [] k) pp_purity_schema \<subseteq> gb_purity_schema G"
proof
  fix B assume "B \<in> image (gi_to_book G [] k) pp_purity_schema"
  then obtain \<sigma> M where typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
    and B: "B = gi_to_book G [] k (pp_pure \<sigma> M)"
    unfolding pp_purity_schema_def by blast
  have admitted: "gi_constants_admitted k (\<lambda>_. {}) M"
    using logical gi_logical_constants_iff by blast
  have "gb_pure \<sigma> (gi_to_book G [] k M) \<in> gb_purity_schema G"
    by (rule gi_translated_logical_purity_instance[OF rich typed admitted])
  then show "B \<in> gb_purity_schema G"
    by (simp add: B gi_pure_translation[OF names])
qed

theorem gi_application_schema_equality:
  "gi_goodman_names k \<Longrightarrow>
    image (gi_to_book G [] k) pp_application_closure_schema = gb_application_schema G"
  unfolding pp_application_closure_schema_def gb_application_schema_def
  by (force simp: gi_application_translation)

theorem gi_no_other_fundamentals_schema_equality:
  "gi_goodman_names k \<Longrightarrow>
    image (gi_to_book G [] k) pp_no_other_fundamentals_schema = gb_no_other_fundamentals_schema G"
  unfolding pp_no_other_fundamentals_schema_def gb_no_other_fundamentals_schema_def
  by (force simp: gi_no_fundamentals_translation)

theorem gi_background_inclusion:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "image (gi_to_book G [] k) pp_background_axioms \<subseteq> gb_background_axioms G"
  unfolding pp_background_axioms_def gb_background_axioms_def image_Un
  using gi_purity_schema_inclusion[OF rich names]
    gi_application_schema_equality[OF names, of G]
    gi_no_other_fundamentals_schema_equality[OF names, of G]
    gi_unique_fundamental_translation[OF names, of G Prop]
  by auto

lemma gi_background_closed:
  "A \<in> pp_background_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding pp_background_axioms_def
  by (auto intro: pp_purity_schema_typed pp_application_closure_schema_typed
    pp_no_other_fundamentals_schema_typed typed_pp_unique_fundamental)

theorem gi_background_proof_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; pp_background_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_background_axioms G) (gi_to_book G ns k A)"
  by (rule goodman_book_mono[
    OF gi_CEV_axiom_preservation[OF rich derivation gi_background_closed chart distinct]
      gi_background_inclusion[OF rich names]])

section \<open>T6 with the independently written purity/application/PP core\<close>

definition gb_T6_core where
  "gb_T6_core G = gb_purity_schema G \<union> gb_application_schema G \<union> {gb_target_PP}"

text \<open>
  The common T6 core is smaller than the central Goodman background: it
  contains neither unique fundamentality nor Recombination. The extra
  route assumptions below are still translated formulas, not independently
  identified native definitions of L2, Inv, TU, WI, or RS.
\<close>

lemma gi_T6_core_inclusion:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow>
    image (gi_to_book G [] k) pp_T6_core_PP_axioms \<subseteq> gb_T6_core G"
  unfolding pp_T6_core_PP_axioms_def gb_T6_core_def image_Un
  using gi_purity_schema_inclusion gi_application_schema_equality gi_PP_translation
  by fastforce

lemma gb_T6_core_language:
  "sg_rich G \<Longrightarrow> A \<in> gb_T6_core G \<Longrightarrow> book_theory_formula gb_signature G A"
  unfolding gb_T6_core_def gb_application_schema_def
  by (auto intro: gb_purity_schema_language gb_application_closure_language gb_target_PP_language)

lemma gb_T6_core_closed:
  "A \<in> gb_T6_core G \<Longrightarrow> named_fv A = {}"
  unfolding gb_T6_core_def gb_application_schema_def
  by (auto simp: gb_purity_schema_closed gb_basic_axioms_closed)

definition gi_T6_native_core_extension where
  "gi_T6_native_core_extension G k S = gb_T6_core G \<union> image (gi_to_book G [] k) S"

lemma gi_T6_native_core_transfer:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "goodman_book_proves (\<lambda>_. UNIV) G
      (image (gi_to_book G [] k) (pp_T6_core_PP_axioms \<union> S)) A"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gi_T6_native_core_extension G k S) A"
  by (rule goodman_book_mono[OF derivation];
    use gi_T6_core_inclusion[OF rich names] in
      \<open>auto simp: gi_T6_native_core_extension_def\<close>)

theorem gi_T6_native_core_Inv_refutation:
  assumes "sg_rich G" "gi_goodman_names k"
  shows "goodman_book_proves (\<lambda>_. UNIV) G
    (gi_T6_native_core_extension G k {pp_exists_fun_prime, pp_L2, pp_Inv}) (book_bottom G)"
  by (rule gi_T6_native_core_transfer[OF assms];
    use gi_T6_Inv_refutation[OF assms(1), of k] in \<open>simp add: pp_T6_Inv_axioms_def\<close>)

theorem gi_T6_native_core_TU_refutation:
  assumes "sg_rich G" "gi_goodman_names k"
  shows "goodman_book_proves (\<lambda>_. UNIV) G
    (gi_T6_native_core_extension G k {pp_exists_fun_prime, pp_L2, pp_TU}) (book_bottom G)"
proof (rule gi_T6_native_core_transfer[OF assms])
  have stock: "pp_T6_core_PP_axioms \<union> {pp_exists_fun_prime, pp_L2, pp_TU} = pp_T6_TU_axioms"
    unfolding pp_T6_TU_axioms_def by auto
  show "goodman_book_proves (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) (pp_T6_core_PP_axioms \<union> {pp_exists_fun_prime, pp_L2, pp_TU})) (book_bottom G)"
    unfolding stock by (rule gi_T6_TU_refutation[OF assms(1)])
qed

theorem gi_T6_native_core_WI_refutation:
  assumes "sg_rich G" "gi_goodman_names k"
  shows "goodman_book_proves (\<lambda>_. UNIV) G
    (gi_T6_native_core_extension G k {pp_exists_fun_prime, pp_L2, pp_WI}) (book_bottom G)"
proof (rule gi_T6_native_core_transfer[OF assms])
  have stock: "pp_T6_core_PP_axioms \<union> {pp_exists_fun_prime, pp_L2, pp_WI} = pp_T6_WI_axioms"
    unfolding pp_T6_WI_axioms_def by auto
  show "goodman_book_proves (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) (pp_T6_core_PP_axioms \<union> {pp_exists_fun_prime, pp_L2, pp_WI})) (book_bottom G)"
    unfolding stock by (rule gi_T6_WI_refutation[OF assms(1)])
qed

theorem gi_T6_native_core_RS_refutation:
  assumes "sg_rich G" "gi_goodman_names k"
  shows "goodman_book_proves (\<lambda>_. UNIV) G
    (gi_T6_native_core_extension G k {pp_strong_L2, pp_RS}) (book_bottom G)"
proof (rule gi_T6_native_core_transfer[OF assms])
  have stock: "pp_T6_core_PP_axioms \<union> {pp_strong_L2, pp_RS} = pp_T6_RS_axioms"
    unfolding pp_T6_RS_axioms_def by auto
  show "goodman_book_proves (\<lambda>_. UNIV) G
    (image (gi_to_book G [] k) (pp_T6_core_PP_axioms \<union> {pp_strong_L2, pp_RS})) (book_bottom G)"
    unfolding stock by (rule gi_T6_RS_refutation[OF assms(1)])
qed

corollary gi_T6_native_core_Inv_inconsistent:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow>
    \<not> goodman_book_consistent (\<lambda>_. UNIV) G
      (gi_T6_native_core_extension G k {pp_exists_fun_prime, pp_L2, pp_Inv})"
  unfolding goodman_book_consistent_def using gi_T6_native_core_Inv_refutation by blast

corollary gi_T6_native_core_TU_inconsistent:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow>
    \<not> goodman_book_consistent (\<lambda>_. UNIV) G
      (gi_T6_native_core_extension G k {pp_exists_fun_prime, pp_L2, pp_TU})"
  unfolding goodman_book_consistent_def using gi_T6_native_core_TU_refutation by blast

corollary gi_T6_native_core_WI_inconsistent:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow>
    \<not> goodman_book_consistent (\<lambda>_. UNIV) G
      (gi_T6_native_core_extension G k {pp_exists_fun_prime, pp_L2, pp_WI})"
  unfolding goodman_book_consistent_def using gi_T6_native_core_WI_refutation by blast

corollary gi_T6_native_core_RS_inconsistent:
  "sg_rich G \<Longrightarrow> gi_goodman_names k \<Longrightarrow>
    \<not> goodman_book_consistent (\<lambda>_. UNIV) G
      (gi_T6_native_core_extension G k {pp_strong_L2, pp_RS})"
  unfolding goodman_book_consistent_def using gi_T6_native_core_RS_refutation by blast

end
