theory Goodman_Exact_M5_Rebuilt_Model
  imports Goodman_Exact_Rebuilt_Constants Goodman_Exact_Basis_Native_Background
    Goodman_Exact_Basis_QLN Goodman_M5_Exotic_Operators
    Goodman_Integration_Exact_QLN.Goodman_Exact_QLN_Model
begin

section \<open>The actual rebuilt interpreter satisfies the native QLN background\<close>

lemma gi_M5_native_QLN_background_language:
  "sg_rich G \<Longrightarrow> A \<in> gi_native_QLN_background G \<Longrightarrow> book_theory_formula gb_signature G A"
  unfolding gi_native_QLN_background_def gb_recombination_background_def gb_exhaustion_axioms_def
  by (auto intro: gb_background_axioms_language gb_zeroary_recombination_language gb_unary_recombination_language
    gb_zeroary_exhaustion_language gb_unary_exhaustion_language)

context gi_exact_expanded_stock
begin

theorem gi_M5_basis_native_QLN_background_gvalid:
  assumes rich: "sg_rich G" and member: "A \<in> gi_native_QLN_background G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants (gi_M5_expanded_basis k K)) G A"
  using member unfolding gi_native_QLN_background_def gb_recombination_background_def gb_exhaustion_axioms_def
  by (auto intro:
    gi_exact_invariant_basis.gi_basis_native_background_gvalid[OF gi_M5_expanded_invariant_basis rich]
    gi_exact_invariant_basis.gi_basis_native_zeroary_recombination_gvalid[OF gi_M5_expanded_invariant_basis rich]
    gi_exact_invariant_basis.gi_basis_native_unary_recombination_gvalid[OF gi_M5_expanded_invariant_basis rich]
    gi_exact_invariant_basis.gi_basis_native_zeroary_exhaustion_gvalid[OF gi_M5_expanded_invariant_basis rich]
    gi_exact_invariant_basis.gi_basis_native_unary_exhaustion_gvalid[OF gi_M5_expanded_invariant_basis rich])

theorem gi_M5_rebuilt_native_QLN_background_gvalid:
  assumes rich: "sg_rich G" and member: "A \<in> gi_native_QLN_background G"
  shows "gi_exact_goodman_global_valid (gi_M5_rebuilt_constants k K) G A"
  using gi_M5_basis_native_QLN_background_gvalid[OF rich member]
  by (simp only: gi_M5_rebuilt_native_global_valid_iff[OF gi_M5_native_QLN_background_language[OF rich member]])

corollary gi_M5_rebuilt_native_QLN_background_consistent:
  assumes rich: "sg_rich G"
  shows "goodman_book_consistent gb_signature G (gi_native_QLN_background G)"
  by (rule pp_e_constants.gi_exact_goodman_consistent_of_global_axioms[
    OF gi_M5_rebuilt_constants_locale rich gi_M5_rebuilt_native_QLN_background_gvalid[OF rich]])

section \<open>The same interpreter makes every closed k-only term pure\<close>

lemma gi_M5_rebuilt_Pure_value:
  "pp_e_eval (gi_M5_rebuilt_constants k K) \<rho> (pp_Pure \<sigma>) =
    pp_e_classifier \<sigma> (gi_basis_pure (gi_M5_expanded_basis k K) \<sigma>)"
  by (simp add: pp_Pure_def gi_M5_rebuilt_Pure_coordinate)

lemma gi_M5_rebuilt_pure_clause:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>" and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval (gi_M5_rebuilt_constants k K) \<rho> (pp_pure \<sigma> M)) w \<longleftrightarrow>
    gi_basis_pure (gi_M5_expanded_basis k K) \<sigma> w (pp_e_eval (gi_M5_rebuilt_constants k K) \<rho> M)"
proof -
  have member: "Elem (pp_e_eval (gi_M5_rebuilt_constants k K) \<rho> M) (pp_e_domain \<sigma>)"
    using Rebuilt.pp_e_eval_type[OF typed env] by (simp only: pp_e_dom_def)
  show ?thesis by (simp only: pp_pure_def pp_e_eval.simps(3) gi_M5_rebuilt_Pure_value pp_e_classifier_holds[OF member])
qed

theorem gi_M5_rebuilt_closed_term_in_basis:
  assumes typed: "[] \<turnstile> M : \<sigma>" and admitted: "oterm_in_string_signature (gi_M5_expanded_signature k) M"
  shows "pp_e_eval (gi_M5_rebuilt_constants k K) \<rho> M \<in> gi_M5_expanded_basis k K \<sigma>"
  by (simp only: gi_M5_rebuilt_expanded_closed_denotation[OF typed admitted];
    rule gi_M5_expanded_basisI[OF typed admitted])

theorem gi_M5_rebuilt_closed_term_pure:
  assumes typed: "[] \<turnstile> M : \<sigma>" and admitted: "oterm_in_string_signature (gi_M5_expanded_signature k) M"
  shows "pp_e_holds (pp_e_eval (gi_M5_rebuilt_constants k K) \<rho> (pp_pure \<sigma> M)) w"
proof -
  have pure: "gi_basis_pure (gi_M5_expanded_basis k K) \<sigma> w (pp_e_eval (gi_M5_rebuilt_constants k K) \<rho> M)"
    by (rule Expanded.gi_basis_pureI[OF gi_M5_rebuilt_closed_term_in_basis[OF typed admitted]])
  show ?thesis using pure by (simp only: gi_M5_rebuilt_pure_clause[OF typed pp_e_empty_env_typed])
qed

theorem gi_M5_rebuilt_K_pure:
  "gi_basis_pure (gi_M5_expanded_basis k K) gb_unary w K"
  by (rule Expanded.gi_basis_pureI[OF gi_M5_expanded_basis_contains_K])

theorem gi_M5_rebuilt_K_pure_holds:
  "pp_e_holds (pp_e_eval (gi_M5_rebuilt_constants k K) \<rho> (pp_pure gb_unary (Const k gb_unary))) w"
  by (rule gi_M5_rebuilt_closed_term_pure;
    (rule has_type.Const | simp add: gi_M5_expanded_signature_def))

lemma gi_M5_rebuilt_k_named_denotation:
  "gi_exact_named_denote (gi_M5_rebuilt_constants k K) G g (NConst k gb_unary) = K"
  by (simp only: gi_exact_named_denote_const gi_M5_rebuilt_constant_at)

theorem gi_M5_rebuilt_named_closed_term_in_basis:
  assumes rich: "sg_rich G"
    and language: "book_in_language book_minimal_logical_type UNIV (gi_M5_expanded_signature k) G A \<sigma>"
    and closed_term: "named_fv A = {}"
  shows "gi_exact_named_denote (gi_M5_rebuilt_constants k K) G g A \<in> gi_M5_expanded_basis k K \<sigma>"
proof -
  have witness: "gi_exact_named_denote (gi_M5_rebuilt_constants k K) G (gi_exact_default_assignment G) A
    \<in> gi_M5_rebuilt_named_basis k K G \<sigma>"
    unfolding gi_M5_rebuilt_named_basis_def by (rule CollectI, rule exI[where x=A]; use language closed_term in auto)
  have at_default: "gi_exact_named_denote (gi_M5_rebuilt_constants k K) G (gi_exact_default_assignment G) A
    \<in> gi_M5_expanded_basis k K \<sigma>"
    using witness by (simp only: gi_M5_rebuilt_named_basis_equal[OF rich])
  show ?thesis using at_default gi_exact_named_closed_assignment_independent[OF closed_term,
    where C="gi_M5_rebuilt_constants k K" and G=G and g=g and h="gi_exact_default_assignment G"] by simp
qed

theorem gi_M5_rebuilt_named_closed_term_pure:
  assumes rich: "sg_rich G"
    and language: "book_in_language book_minimal_logical_type UNIV (gi_M5_expanded_signature k) G A \<sigma>"
    and closed_term: "named_fv A = {}"
  shows "gi_exact_valuation w (gi_exact_named_denote (gi_M5_rebuilt_constants k K) G g
    (NApp (NConst pp_pure_name (Arr \<sigma> Prop)) A))"
proof -
  let ?a = "gi_exact_named_denote (gi_M5_rebuilt_constants k K) G g A"
  have basis: "?a \<in> gi_M5_expanded_basis k K \<sigma>"
    by (rule gi_M5_rebuilt_named_closed_term_in_basis[OF rich language closed_term])
  have member: "Elem ?a (pp_e_domain \<sigma>)" by (rule gi_M5_expanded_basis_typed[OF basis])
  have pure: "gi_basis_pure (gi_M5_expanded_basis k K) \<sigma> w ?a" by (rule Expanded.gi_basis_pureI[OF basis])
  show ?thesis using pure
    by (simp add: gi_exact_valuation_def gi_exact_named_denote_app[where \<sigma>=\<sigma> and \<tau>=Prop]
      gi_exact_app_value gi_exact_named_denote_const gi_M5_rebuilt_Pure_coordinate
      pp_e_classifier_holds[OF member])
qed

section \<open>The rebuilt generic seed cannot be the old collision input\<close>

lemma gi_M5_identity_in_expanded_raw_stock:
  "id \<in> gi_basis_raw_stock (gi_M5_expanded_basis k K)"
proof -
  have logical: "pp_logical_vocabulary pp_identity_operator"
    by (simp add: pp_logical_vocabulary_def pp_identity_operator_def)
  have member: "pp_e_closed_den pp_identity_operator \<in> gi_M5_expanded_basis k K gb_unary"
    by (rule gi_M5_expanded_basis_contains_logical[OF typed_pp_identity_operator[unfolded pp_unary_ty_def] logical])
  have "pp_e_raw_operator (pp_e_closed_den pp_identity_operator) \<in> gi_basis_raw_stock (gi_M5_expanded_basis k K)"
    unfolding gi_basis_raw_stock_def using member by blast
  then show ?thesis by (simp only: pp_e_raw_operator_identity)
qed

lemma gi_M5_K_in_expanded_raw_stock:
  "pp_e_raw_operator K \<in> gi_basis_raw_stock (gi_M5_expanded_basis k K)"
  unfolding gi_basis_raw_stock_def using gi_M5_expanded_basis_contains_K by blast

theorem gi_M5_rebuilt_seed_changes:
  assumes fixed: "pp_e_raw_operator K R = R" and nonidentity: "pp_e_raw_operator K \<noteq> id"
  shows "gi_basis_raw_seed (gi_M5_expanded_basis k K) \<noteq> R"
proof
  assume same: "gi_basis_raw_seed (gi_M5_expanded_basis k K) = R"
  have agreement: "pp_e_raw_operator K (gi_basis_raw_seed (gi_M5_expanded_basis k K)) =
    id (gi_basis_raw_seed (gi_M5_expanded_basis k K))" by (simp only: same fixed id_apply)
  have identical: "pp_e_raw_operator K = id"
    by (rule Expanded.gi_basis_raw_seed_separates[OF gi_M5_K_in_expanded_raw_stock
      gi_M5_identity_in_expanded_raw_stock agreement])
  show False using identical nonidentity by contradiction
qed

end

section \<open>Instantiate the complete construction with the repaired exotic operator\<close>

definition gi_M5_exotic_name :: string where
  "gi_M5_exotic_name = ''Goodman_M5_exotic''"

lemma gi_exact_M5_exotic_expanded_stock:
  "gi_exact_expanded_stock gi_M5_exotic_name (gi_exact_M5_exotic R)"
proof
  show "gi_M5_exotic_name \<noteq> pp_pure_name" by (simp add: gi_M5_exotic_name_def pp_pure_name_def)
  show "gi_M5_exotic_name \<noteq> pp_fun_name" by (simp add: gi_M5_exotic_name_def pp_fun_name_def)
  show "Elem (gi_exact_M5_exotic R) (pp_e_domain gb_unary)" by (rule gi_exact_M5_exotic_member)
  fix i show "pp_b_action gb_unary i (gi_exact_M5_exotic R) = gi_exact_M5_exotic R"
    by (rule gi_exact_M5_exotic_invariant)
qed

abbreviation gi_M5_exotic_constants where
  "gi_M5_exotic_constants R \<equiv> gi_M5_rebuilt_constants gi_M5_exotic_name (gi_exact_M5_exotic R)"

abbreviation gi_M5_exotic_basis where
  "gi_M5_exotic_basis R \<equiv> gi_M5_expanded_basis gi_M5_exotic_name (gi_exact_M5_exotic R)"

theorem gi_exact_M5_rebuilt_QLN_model:
  assumes rich: "sg_rich G" and member: "A \<in> gi_native_QLN_background G"
  shows "gi_exact_goodman_global_valid (gi_M5_exotic_constants R) G A"
  by (rule gi_exact_expanded_stock.gi_M5_rebuilt_native_QLN_background_gvalid[
    OF gi_exact_M5_exotic_expanded_stock rich member])

theorem gi_exact_M5_rebuilt_exotic_pure:
  "pp_e_holds (pp_e_eval (gi_M5_exotic_constants R) \<rho>
    (pp_pure gb_unary (Const gi_M5_exotic_name gb_unary))) w"
  by (rule gi_exact_expanded_stock.gi_M5_rebuilt_K_pure_holds[OF gi_exact_M5_exotic_expanded_stock])

theorem gi_exact_M5_rebuilt_exotic_denotation:
  "pp_e_eval (gi_M5_exotic_constants R) \<rho> (Const gi_M5_exotic_name gb_unary) = gi_exact_M5_exotic R"
  by (rule gi_exact_expanded_stock.gi_M5_rebuilt_exotic_constant_denotation[OF gi_exact_M5_exotic_expanded_stock])

theorem gi_exact_M5_rebuilt_complete_purity:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and admitted: "oterm_in_string_signature (gi_M5_expanded_signature gi_M5_exotic_name) M"
  shows "pp_e_holds (pp_e_eval (gi_M5_exotic_constants R) \<rho> (pp_pure \<sigma> M)) w"
  by (rule gi_exact_expanded_stock.gi_M5_rebuilt_closed_term_pure[
    OF gi_exact_M5_exotic_expanded_stock typed admitted])

theorem gi_exact_M5_rebuilt_seed_not_old:
  "gi_basis_raw_seed (gi_M5_exotic_basis R) \<noteq> R"
proof (rule gi_exact_expanded_stock.gi_M5_rebuilt_seed_changes[OF gi_exact_M5_exotic_expanded_stock])
  show "pp_e_raw_operator (gi_exact_M5_exotic R) R = R"
    by (simp only: gi_exact_M5_exotic_raw gi_M5_repaired_exotic_fixes_R)
  show "pp_e_raw_operator (gi_exact_M5_exotic R) \<noteq> id"
    by (simp only: gi_exact_M5_exotic_raw; rule gi_M5_repaired_exotic_not_identity)
qed

theorem gi_exact_M5_rebuilt_certificate:
  assumes rich: "sg_rich G"
  shows "pp_e_constants (gi_M5_exotic_constants R)"
    "\<forall>A\<in>gi_native_QLN_background G. gi_exact_goodman_global_valid (gi_M5_exotic_constants R) G A"
    "\<forall>w \<rho>. pp_e_holds (pp_e_eval (gi_M5_exotic_constants R) \<rho>
      (pp_pure gb_unary (Const gi_M5_exotic_name gb_unary))) w"
    "\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow> gi_exact_M5_exotic R \<acute> (gi_exact_M5_exotic R \<acute> p) = p"
    "\<not> (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
        (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> pp_e_holds p []))
      \<and> \<not> (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
        (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> \<not> pp_e_holds p []))"
    "gi_basis_raw_seed (gi_M5_exotic_basis R) \<noteq> R"
proof -
  show "pp_e_constants (gi_M5_exotic_constants R)"
    by (rule gi_exact_expanded_stock.gi_M5_rebuilt_constants_locale[OF gi_exact_M5_exotic_expanded_stock])
  show "\<forall>A\<in>gi_native_QLN_background G. gi_exact_goodman_global_valid (gi_M5_exotic_constants R) G A"
    by (intro ballI; rule gi_exact_M5_rebuilt_QLN_model[OF rich]; assumption)
  show "\<forall>w \<rho>. pp_e_holds (pp_e_eval (gi_M5_exotic_constants R) \<rho>
      (pp_pure gb_unary (Const gi_M5_exotic_name gb_unary))) w"
    by (intro allI; rule gi_exact_M5_rebuilt_exotic_pure)
  show "\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow> gi_exact_M5_exotic R \<acute> (gi_exact_M5_exotic R \<acute> p) = p"
    by (intro allI impI; rule gi_exact_M5_exotic_involution; assumption)
  show "\<not> (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
        (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> pp_e_holds p []))
      \<and> \<not> (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
        (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> \<not> pp_e_holds p []))"
    by (rule gi_exact_M5_exotic_not_truth_uniform)
  show "gi_basis_raw_seed (gi_M5_exotic_basis R) \<noteq> R" by (rule gi_exact_M5_rebuilt_seed_not_old)
qed

text \<open>
  This is an actual rebuilt model on Bacon's exact carriers, not merely
  the auxiliary expanded-language interpreter. Its enlarged pure basis
  contains every closed typed k-only term, including higher-order quantified
  terms. The newly interpreted k denotes the repaired exotic value, which
  is pure and involutive but neither uniformly truth-preserving nor uniformly
  truth-flipping. Its new generic seed is proved different from the old
  collision input R. The no-PP zeroary/unary QLN background holds globally.

  PP is not among the verified axioms: self-membership of the enlarged Pure
  classifier is a separate condition. The displayed operator certificate
  must also be distinguished from a separately encoded root evaluation of
  pp_TU, pp_Inv, or pp_WI. No nonderivability of those formulas is claimed
  merely from the syntax of this certificate. HOL–ZF foundations are retained.
\<close>

end
