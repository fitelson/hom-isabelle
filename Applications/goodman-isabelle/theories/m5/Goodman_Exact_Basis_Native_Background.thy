theory Goodman_Exact_Basis_Native_Background
  imports Goodman_Exact_Basis_Seed
    Goodman_Integration_Exact_Applicative.Goodman_Exact_Goodman_Translation
begin

context gi_exact_invariant_basis
begin

section \<open>Native Pure/Fun meaning for the enlarged basis interpretation\<close>

lemma gi_basis_native_denote_member:
  assumes language: "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma>"
    and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_goodman_denote (gi_basis_internal_constants B) G g A \<in> gi_exact_domain \<sigma>"
  unfolding gi_exact_goodman_denote_def
  by (rule pp_e_constants.gi_exact_named_denote_type[OF gi_basis_internal_constants_locale
    gi_goodman_string_term_language[OF language] typed])

lemma gi_basis_native_pure_denotation:
  "gi_exact_goodman_denote (gi_basis_internal_constants B) G g (gb_pure \<sigma> A) =
    pp_e_classifier \<sigma> (gi_basis_pure B \<sigma>) \<acute>
      gi_exact_goodman_denote (gi_basis_internal_constants B) G g A"
  unfolding gb_pure_def gi_exact_goodman_denote_def
  by (simp add: gi_goodman_string_term_Pure
    gi_exact_named_denote_app[where \<sigma>=\<sigma> and \<tau>=Prop]
    gi_exact_app_value gi_exact_named_denote_const)

lemma gi_basis_native_fun_denotation:
  "gi_exact_goodman_denote (gi_basis_internal_constants B) G g (gb_fun \<sigma> A) =
    pp_e_classifier \<sigma> (gi_basis_fundamental_at B \<sigma>) \<acute>
      gi_exact_goodman_denote (gi_basis_internal_constants B) G g A"
  unfolding gb_fun_def gi_exact_goodman_denote_def
  by (simp add: gi_goodman_string_term_Fun
    gi_exact_named_denote_app[where \<sigma>=\<sigma> and \<tau>=Prop]
    gi_exact_app_value gi_exact_named_denote_const pp_fun_name_def pp_pure_name_def)

theorem gi_basis_native_pure_holds:
  assumes language: "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma>"
    and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_valuation w (gi_exact_goodman_denote (gi_basis_internal_constants B) G g (gb_pure \<sigma> A))
    \<longleftrightarrow> gi_basis_pure B \<sigma> w (gi_exact_goodman_denote (gi_basis_internal_constants B) G g A)"
proof -
  have member: "Elem (gi_exact_goodman_denote (gi_basis_internal_constants B) G g A) (pp_e_domain \<sigma>)"
    using gi_basis_native_denote_member[OF language typed] by (simp only: gi_exact_domain_member)
  show ?thesis by (simp only: gi_basis_native_pure_denotation gi_exact_valuation_def pp_e_classifier_holds[OF member])
qed

theorem gi_basis_native_fun_holds:
  assumes language: "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma>"
    and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_valuation w (gi_exact_goodman_denote (gi_basis_internal_constants B) G g (gb_fun \<sigma> A))
    \<longleftrightarrow> gi_basis_fundamental_at B \<sigma> w (gi_exact_goodman_denote (gi_basis_internal_constants B) G g A)"
proof -
  have member: "Elem (gi_exact_goodman_denote (gi_basis_internal_constants B) G g A) (pp_e_domain \<sigma>)"
    using gi_basis_native_denote_member[OF language typed] by (simp only: gi_exact_domain_member)
  show ?thesis by (simp only: gi_basis_native_fun_denotation gi_exact_valuation_def pp_e_classifier_holds[OF member])
qed

section \<open>Every native closed logical term is certified pure\<close>

theorem gi_basis_native_logical_purity_gvalid:
  assumes logical: "gb_closed_logical G \<sigma> A"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G (gb_pure \<sigma> A)"
  unfolding gi_exact_goodman_global_valid_iff
proof (intro allI impI)
  fix w g assume typed: "book_env_typed gi_exact_domain G g"
  have language: "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma>"
    by (rule gb_closed_logical_in_signature[OF logical])
  have pure: "gi_basis_pure B \<sigma> w (gi_exact_goodman_denote (gi_basis_internal_constants B) G g A)"
    by (rule gi_basis_contains_native_closed_logical[OF logical])
  show "gi_exact_valuation w (gi_exact_goodman_denote (gi_basis_internal_constants B) G g (gb_pure \<sigma> A))"
    using gi_basis_native_pure_holds[OF language typed, where w=w] pure by blast
qed

theorem gi_basis_native_purity_schema_gvalid:
  assumes member: "A \<in> gb_purity_schema G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G A"
proof -
  obtain \<sigma> M where logical: "gb_closed_logical G \<sigma> M" and shape: "A = gb_pure \<sigma> M"
    using member unfolding gb_purity_schema_def by blast
  show ?thesis unfolding shape by (rule gi_basis_native_logical_purity_gvalid[OF logical])
qed

section \<open>The other background instances in the exact internal interpretation\<close>

lemma gi_basis_application_holds_iff:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow> (\<forall>f. Elem f (pp_e_domain (Arr \<sigma> \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_e_domain \<sigma>) \<longrightarrow>
        gi_basis_pure B (Arr \<sigma> \<tau>) w f \<and> gi_basis_pure B \<sigma> w x \<longrightarrow>
          gi_basis_pure B \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def gi_basis_eval_Pure
    pp_e_classifier_holds pp_e_app_closed extend_env.simps)

lemma gi_basis_application_holds:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> (pp_application_closure \<sigma> \<tau>)) w"
  unfolding gi_basis_application_holds_iff using gi_basis_pure_application_closed by blast

lemma gi_basis_unique_fundamental_holds:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> (pp_unique_fundamental Prop)) w"
  unfolding pp_unique_fundamental_def
  apply (simp only: pp_e_eval_Exists_holds)
  apply (rule exI[where x="gi_basis_seed_at B w"])
  using gi_basis_seed_at_member[where w=w]
  by (simp add: pp_fun_def gi_basis_eval_Fun pp_e_classifier_holds pp_e_eqv_reflexive extend_env.simps)

lemma gi_basis_no_fundamentals_holds:
  assumes nonprop: "\<sigma> \<noteq> Prop"
  shows "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> (pp_no_fundamentals \<sigma>)) w"
  using nonprop
  by (cases \<sigma>; simp add: pp_no_fundamentals_def pp_fun_def gi_basis_eval_Fun
    pp_e_classifier_holds extend_env.simps)

lemma gi_basis_native_closed_shape_gvalid:
  assumes rich: "sg_rich G" and typed: "[] \<turnstile> M : Prop"
    and names: "gi_goodman_names k" and vocabulary: "consts_of M \<subseteq> {pp_pure_name, pp_fun_name}"
    and shape: "gi_to_book G [] k M = A"
    and truth: "\<And>w. pp_e_holds (pp_e_eval (gi_basis_internal_constants B) pp_e_closed_env M) w"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G A"
  unfolding gi_exact_goodman_global_valid_iff
proof (intro allI impI)
  fix w g assume environment: "book_env_typed gi_exact_domain G g"
  have denotation: "gi_exact_goodman_denote (gi_basis_internal_constants B) G g A =
    pp_e_eval (gi_basis_internal_constants B) pp_e_closed_env M"
    unfolding shape[symmetric]
    by (rule pp_e_constants.gi_exact_goodman_closed_denotation_translation[
      OF gi_basis_internal_constants_locale rich typed environment names vocabulary])
  show "gi_exact_valuation w (gi_exact_goodman_denote (gi_basis_internal_constants B) G g A)"
    by (simp only: denotation gi_exact_valuation_def; rule truth)
qed

theorem gi_basis_native_application_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G (gb_application_closure G \<sigma> \<tau>)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of (pp_application_closure \<sigma> \<tau>) \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_application_closure_def pp_pure_def pp_Pure_def pp_pure_name_def)
  show ?thesis by (rule gi_basis_native_closed_shape_gvalid[OF rich typed_pp_application_closure
    names vocabulary gi_application_translation[OF names] gi_basis_application_holds])
qed

theorem gi_basis_native_application_schema_gvalid:
  assumes rich: "sg_rich G" and member: "A \<in> gb_application_schema G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G A"
  using member unfolding gb_application_schema_def
  by (auto intro: gi_basis_native_application_gvalid[OF rich])

theorem gi_basis_native_unique_fundamental_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G (gb_unique_fundamental G Prop)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of (pp_unique_fundamental Prop) \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_unique_fundamental_def pp_fun_def pp_Fun_def pp_fun_name_def)
  show ?thesis by (rule gi_basis_native_closed_shape_gvalid[OF rich typed_pp_unique_fundamental
    names vocabulary gi_unique_fundamental_translation[OF names] gi_basis_unique_fundamental_holds])
qed

theorem gi_basis_native_no_fundamentals_gvalid:
  assumes rich: "sg_rich G" and nonprop: "\<sigma> \<noteq> Prop"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G (gb_no_fundamentals G \<sigma>)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of (pp_no_fundamentals \<sigma>) \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_no_fundamentals_def pp_fun_def pp_Fun_def pp_fun_name_def)
  show ?thesis by (rule gi_basis_native_closed_shape_gvalid[OF rich typed_pp_no_fundamentals
    names vocabulary gi_no_fundamentals_translation[OF names] gi_basis_no_fundamentals_holds[OF nonprop]])
qed

theorem gi_basis_native_no_other_fundamentals_schema_gvalid:
  assumes rich: "sg_rich G" and member: "A \<in> gb_no_other_fundamentals_schema G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G A"
  using member unfolding gb_no_other_fundamentals_schema_def
  by (auto intro: gi_basis_native_no_fundamentals_gvalid[OF rich])

theorem gi_basis_native_background_gvalid:
  assumes rich: "sg_rich G" and member: "A \<in> gb_background_axioms G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G A"
  using member unfolding gb_background_axioms_def
  by (auto intro: gi_basis_native_purity_schema_gvalid gi_basis_native_application_schema_gvalid[OF rich]
    gi_basis_native_unique_fundamental_gvalid[OF rich] gi_basis_native_no_other_fundamentals_schema_gvalid[OF rich])

end

text \<open>
  The complete native logical-purity schema was proved through closed
  decoding, not just through image instances. B can properly enlarge the
  original closed-logical basis; no equality with that old basis is used.

  These statements concern the native Pure/Fun language. The base internal
  constant assignment gives default values to other names. Interpreting a
  fresh k by a specified exotic value requires a separate overridden
  assignment and agreement proof; this theory does not already certify
  the full expanded-k language. QLN and PP are not part of gb_background_axioms.
\<close>

end
