theory Goodman_Exact_Generic_Interpretation
  imports Goodman_Exact_Recombination.Bacon_PP_ZF_Exact_Recombination
    Goodman_Integration_Logical_Stock.Goodman_Exact_Stock_Correspondence
    Goodman_Integration_Exact_Applicative.Goodman_Exact_Goodman_Translation
begin

section \<open>The specified generic Pure/Fun interpretation in the native language\<close>

text \<open>
  We retain the exact carriers and the existing generic internal constants.
  Pure classifies the complete closed-logical stock, saturated at each
  world under local identity. Fun at t classifies the specified moving
  seed pp_e_generic_seed_at w; Fun at every other type is empty.

  This is the generic moving-seed interpretation already defined in the
  exact construction. It is not silently identified with a particular
  fixed constant assignment obtained by Theorem 10.1 gluing. No PP
  instance is asserted in this theory.
\<close>

lemma gi_exact_generic_constants:
  "pp_e_constants pp_e_generic_internal_constants"
  by standard (rule pp_e_generic_internal_constants_typed)

lemma gi_exact_generic_native_denote_type:
  assumes language: "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma>"
    and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_goodman_denote pp_e_generic_internal_constants G g A \<in> gi_exact_domain \<sigma>"
  unfolding gi_exact_goodman_denote_def
  by (rule pp_e_constants.gi_exact_named_denote_type[OF gi_exact_generic_constants
    gi_goodman_string_term_language[OF language] typed])

lemma gi_exact_generic_Pure_denotation:
  "gi_exact_goodman_denote pp_e_generic_internal_constants G g (gb_Pure \<sigma>) =
    pp_e_classifier \<sigma> (pp_e_closed_logical_stock \<sigma>)"
  unfolding gi_exact_goodman_denote_def
  by (simp add: gi_goodman_string_term_Pure gi_exact_named_denote_const)

lemma gi_exact_generic_Fun_denotation:
  "gi_exact_goodman_denote pp_e_generic_internal_constants G g (gb_Fun \<sigma>) =
    pp_e_classifier \<sigma> (pp_e_generic_fundamental_at \<sigma>)"
  unfolding gi_exact_goodman_denote_def
  by (simp add: gi_goodman_string_term_Fun gi_exact_named_denote_const
    pp_fun_name_def pp_pure_name_def)

lemma gi_exact_generic_pure_denotation:
  "gi_exact_goodman_denote pp_e_generic_internal_constants G g (gb_pure \<sigma> A) =
    pp_e_classifier \<sigma> (pp_e_closed_logical_stock \<sigma>) \<acute>
      gi_exact_goodman_denote pp_e_generic_internal_constants G g A"
  unfolding gb_pure_def gi_exact_goodman_denote_def
  by (simp add: gi_goodman_string_term_Pure
    gi_exact_named_denote_app[where \<sigma>=\<sigma> and \<tau>=Prop]
    gi_exact_app_value gi_exact_named_denote_const)

lemma gi_exact_generic_fun_denotation:
  "gi_exact_goodman_denote pp_e_generic_internal_constants G g (gb_fun \<sigma> A) =
    pp_e_classifier \<sigma> (pp_e_generic_fundamental_at \<sigma>) \<acute>
      gi_exact_goodman_denote pp_e_generic_internal_constants G g A"
  unfolding gb_fun_def gi_exact_goodman_denote_def
  by (simp add: gi_goodman_string_term_Fun
    gi_exact_named_denote_app[where \<sigma>=\<sigma> and \<tau>=Prop]
    gi_exact_app_value gi_exact_named_denote_const pp_fun_name_def pp_pure_name_def)

theorem gi_exact_generic_native_pure_holds:
  assumes rich: "sg_rich G"
    and language: "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma>"
    and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_valuation w (gi_exact_goodman_denote pp_e_generic_internal_constants G g (gb_pure \<sigma> A))
    \<longleftrightarrow> gi_exact_native_logical_stock G \<sigma> w
      (gi_exact_goodman_denote pp_e_generic_internal_constants G g A)"
proof -
  have member: "Elem (gi_exact_goodman_denote pp_e_generic_internal_constants G g A) (pp_e_domain \<sigma>)"
    using gi_exact_generic_native_denote_type[OF language typed]
    by (simp only: gi_exact_domain_member)
  show ?thesis by (simp only: gi_exact_generic_pure_denotation gi_exact_valuation_def
    pp_e_classifier_holds[OF member] gi_exact_native_stock_iff_original[OF rich])
qed

theorem gi_exact_generic_native_fun_holds:
  assumes language: "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma>"
    and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_valuation w (gi_exact_goodman_denote pp_e_generic_internal_constants G g (gb_fun \<sigma> A))
    \<longleftrightarrow> pp_e_generic_fundamental_at \<sigma> w
      (gi_exact_goodman_denote pp_e_generic_internal_constants G g A)"
proof -
  have member: "Elem (gi_exact_goodman_denote pp_e_generic_internal_constants G g A) (pp_e_domain \<sigma>)"
    using gi_exact_generic_native_denote_type[OF language typed]
    by (simp only: gi_exact_domain_member)
  show ?thesis by (simp only: gi_exact_generic_fun_denotation gi_exact_valuation_def
    pp_e_classifier_holds[OF member])
qed

section \<open>Logical purity for every native closed logical term\<close>

theorem gi_exact_generic_logical_purity_gvalid:
  assumes rich: "sg_rich G" and logical: "gb_closed_logical G \<sigma> A"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gb_pure \<sigma> A)"
  unfolding gi_exact_goodman_global_valid_iff
proof (intro allI impI)
  fix w g assume typed: "book_env_typed gi_exact_domain G g"
  have language: "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma>"
    by (rule gb_closed_logical_in_signature[OF logical])
  have old_typed: "[] \<turnstile> gi_exact_decode G (gi_goodman_string_term A) : \<sigma>"
    by (rule gi_goodman_closed_logical_decode_denotation(1)[OF logical])
  have old_logical: "pp_logical_vocabulary (gi_exact_decode G (gi_goodman_string_term A))"
    by (rule gi_goodman_closed_logical_decode_denotation(2)[OF logical])
  have original_stock: "pp_e_closed_logical_stock \<sigma> w
    (pp_e_closed_den (gi_exact_decode G (gi_goodman_string_term A)))"
    by (rule pp_e_closed_logical_stockI[OF old_typed old_logical])
  have stock: "gi_exact_native_logical_stock G \<sigma> w
    (gi_exact_goodman_denote pp_e_generic_internal_constants G g A)"
    by (simp only: gi_exact_native_stock_iff_original[OF rich]
      gi_goodman_closed_logical_decode_denotation(3)[OF logical]; rule original_stock)
  show "gi_exact_valuation w
    (gi_exact_goodman_denote pp_e_generic_internal_constants G g (gb_pure \<sigma> A))"
    using gi_exact_generic_native_pure_holds[OF rich language typed, where w=w] stock by blast
qed

theorem gi_exact_generic_purity_schema_gvalid:
  assumes rich: "sg_rich G" and member: "A \<in> gb_purity_schema G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G A"
proof -
  obtain \<sigma> M where logical: "gb_closed_logical G \<sigma> M" and shape: "A = gb_pure \<sigma> M"
    using member unfolding gb_purity_schema_def by blast
  show ?thesis unfolding shape by (rule gi_exact_generic_logical_purity_gvalid[OF rich logical])
qed

section \<open>Closed formula transfer for the remaining nonmodal axioms\<close>

lemma gi_exact_generic_closed_shape_gvalid:
  assumes rich: "sg_rich G" and typed: "[] \<turnstile> M : Prop"
    and names: "gi_goodman_names k"
    and vocabulary: "consts_of M \<subseteq> {pp_pure_name, pp_fun_name}"
    and shape: "gi_to_book G [] k M = A"
    and truth: "\<And>w. pp_e_holds (pp_e_eval pp_e_generic_internal_constants pp_e_closed_env M) w"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G A"
  unfolding gi_exact_goodman_global_valid_iff
proof (intro allI impI)
  fix w g assume environment: "book_env_typed gi_exact_domain G g"
  have denotation: "gi_exact_goodman_denote pp_e_generic_internal_constants G g A =
    pp_e_eval pp_e_generic_internal_constants pp_e_closed_env M"
    unfolding shape[symmetric]
    by (rule pp_e_constants.gi_exact_goodman_closed_denotation_translation[
      OF gi_exact_generic_constants rich typed environment names vocabulary])
  show "gi_exact_valuation w (gi_exact_goodman_denote pp_e_generic_internal_constants G g A)"
    by (simp only: denotation gi_exact_valuation_def; rule truth)
qed

theorem gi_exact_generic_application_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gb_application_closure G \<sigma> \<tau>)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of (pp_application_closure \<sigma> \<tau>) \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_application_closure_def pp_pure_def pp_Pure_def pp_pure_name_def)
  have truth: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants pp_e_closed_env
    (pp_application_closure \<sigma> \<tau>)) w" for w
    unfolding pp_e_generic_closed_logical_application_closure_holds_iff
    using pp_e_closed_logical_stock_application_closed by blast
  show ?thesis by (rule gi_exact_generic_closed_shape_gvalid[OF rich typed_pp_application_closure
    names vocabulary gi_application_translation[OF names] truth])
qed

theorem gi_exact_generic_application_schema_gvalid:
  assumes rich: "sg_rich G" and member: "A \<in> gb_application_schema G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G A"
  using member unfolding gb_application_schema_def
  by (auto intro: gi_exact_generic_application_gvalid[OF rich])

theorem gi_exact_generic_unique_fundamental_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gb_unique_fundamental G Prop)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of (pp_unique_fundamental Prop) \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_unique_fundamental_def pp_fun_def pp_Fun_def pp_fun_name_def)
  show ?thesis by (rule gi_exact_generic_closed_shape_gvalid[OF rich typed_pp_unique_fundamental
    names vocabulary gi_unique_fundamental_translation[OF names] pp_e_generic_unique_fundamental_holds])
qed

theorem gi_exact_generic_no_fundamentals_gvalid:
  assumes rich: "sg_rich G" and nonprop: "\<sigma> \<noteq> Prop"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gb_no_fundamentals G \<sigma>)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of (pp_no_fundamentals \<sigma>) \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_no_fundamentals_def pp_fun_def pp_Fun_def pp_fun_name_def)
  show ?thesis by (rule gi_exact_generic_closed_shape_gvalid[OF rich typed_pp_no_fundamentals
    names vocabulary gi_no_fundamentals_translation[OF names] pp_e_generic_no_fundamentals_holds[OF nonprop]])
qed

theorem gi_exact_generic_no_other_fundamentals_schema_gvalid:
  assumes rich: "sg_rich G" and member: "A \<in> gb_no_other_fundamentals_schema G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G A"
  using member unfolding gb_no_other_fundamentals_schema_def
  by (auto intro: gi_exact_generic_no_fundamentals_gvalid[OF rich])

theorem gi_exact_generic_background_gvalid:
  assumes rich: "sg_rich G" and member: "A \<in> gb_background_axioms G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G A"
  using member unfolding gb_background_axioms_def
  by (auto intro: gi_exact_generic_purity_schema_gvalid[OF rich]
    gi_exact_generic_application_schema_gvalid[OF rich]
    gi_exact_generic_unique_fundamental_gvalid[OF rich]
    gi_exact_generic_no_other_fundamentals_schema_gvalid[OF rich])

end
