theory Goodman_Exact_Generic_Fun_Prime
  imports Goodman_Exact_M3_Algebra
    Goodman_Integration_Exact_L2.Goodman_Exact_Fun_Prime_Root
begin

section \<open>Complement closure of the complete exact logical unary stock\<close>

definition gi_generic_complement_term where
  "gi_generic_complement_term M = Lam Prop (Neg (App (shift M) (Var 0)))"

lemma gi_generic_complement_term_type:
  assumes mt: "[] \<turnstile> M : gb_unary"
  shows "[] \<turnstile> gi_generic_complement_term M : gb_unary"
  unfolding gi_generic_complement_term_def
  by (rule has_type.Lam, rule has_type.Neg,
    rule has_type.App[OF typed_shift_ctx[OF mt] typed_var0])

lemma gi_generic_complement_term_logical:
  "pp_logical_vocabulary M \<Longrightarrow> pp_logical_vocabulary (gi_generic_complement_term M)"
  by (simp add: gi_generic_complement_term_def pp_logical_vocabulary_def shift_def consts_of_rename)

lemma gi_generic_complement_raw:
  assumes mt: "[] \<turnstile> M : gb_unary"
  shows "pp_e_raw_operator (pp_e_closed_den (gi_generic_complement_term M)) =
    (\<lambda>P. - pp_e_raw_operator (pp_e_closed_den M) P)"
proof (rule ext, rule set_eqI)
  fix P i
  have pm: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)"
    using pp_n_bacon_embed_in_domain[of P] by simp
  show "i \<in> pp_e_raw_operator (pp_e_closed_den (gi_generic_complement_term M)) P
    \<longleftrightarrow> i \<in> - pp_e_raw_operator (pp_e_closed_den M) P"
    using pm by (simp add: pp_e_raw_operator_def pp_e_closed_den_def gi_generic_complement_term_def
      Lambda_app pp_e_eval_shift pp_n_bacon_extract_def)
qed

theorem gi_exact_generic_complement_closed:
  assumes stock: "F \<in> pp_e_exact_operator_stock"
  shows "(\<lambda>P. - F P) \<in> pp_e_exact_operator_stock"
proof -
  obtain M where mt: "[] \<turnstile> M : gb_unary" and ml: "pp_logical_vocabulary M"
    and shape: "F = pp_e_raw_operator (pp_e_closed_den M)"
    using stock by (rule pp_e_exact_operator_stockE)
  have member: "pp_e_raw_operator (pp_e_closed_den (gi_generic_complement_term M)) \<in> pp_e_exact_operator_stock"
    by (rule pp_e_exact_operator_stockI[OF gi_generic_complement_term_type[OF mt]
      gi_generic_complement_term_logical[OF ml]])
  show ?thesis using member by (simp only: gi_generic_complement_raw[OF mt] shape)
qed

section \<open>The actual chosen generic seed separates the actual stock\<close>

text \<open>
  The definition pp_e_generic_raw_seed selects a witness for precisely
  pp_e_closed_classifier_indices. We use that very witness, rather than
  appealing to existence of some other separating proposition. Applying
  its Recombination condition to the complement of a vanishing operator
  proves that the operator is identically empty.
\<close>

lemma gi_exact_operator_index_in_generic_stock:
  assumes stock: "F \<in> pp_e_exact_operator_stock"
  shows "pp_operator_index F \<in> pp_e_closed_classifier_indices"
  using stock unfolding pp_e_closed_classifier_indices_def pp_e_exact_operator_stock_def
  by (rule imageI)

lemma gi_exact_generic_seed_index_recombination:
  assumes member: "S \<in> pp_e_closed_classifier_indices"
  shows "pp_orbit pp_e_generic_raw_seed \<subseteq> S \<longleftrightarrow> S = UNIV"
proof -
  have guarded: "pp_guarded_unary_QLN_at_world [] pp_e_generic_raw_seed S"
    using pp_e_generic_raw_seed_spec member by blast
  have root: "pp_root_unary_QLN S pp_e_generic_raw_seed"
    using guarded by (simp only: pp_guarded_unary_QLN_at_world_iff)
  show ?thesis using root by (simp only: pp_root_unary_QLN_iff)
qed

theorem gi_exact_generic_seed_vanishing_operator_zero:
  assumes stock: "F \<in> pp_e_exact_operator_stock" and vanishes: "F pp_e_generic_raw_seed = {}"
  shows "F = (\<lambda>P. {})"
proof -
  let ?N = "\<lambda>P. - F P"
  let ?S = "pp_operator_index ?N"
  have negative_stock: "?N \<in> pp_e_exact_operator_stock"
    by (rule gi_exact_generic_complement_closed[OF stock])
  have index: "?S \<in> pp_e_closed_classifier_indices"
    by (rule gi_exact_operator_index_in_generic_stock[OF negative_stock])
  have equivariant: "pp_equivariant_operator ?N"
    by (rule pp_e_exact_operator_stock_equivariant[OF negative_stock])
  have represented: "?N = pp_classifier ?S"
    by (rule pp_equivariant_operator_is_classifier[OF equivariant])
  have filled: "pp_classifier ?S pp_e_generic_raw_seed = UNIV"
    using fun_cong[OF represented, of pp_e_generic_raw_seed] vanishes by simp
  have contained: "pp_orbit pp_e_generic_raw_seed \<subseteq> ?S"
    using filled by (simp only: pp_classifier_UNIV_iff)
  have universal: "?S = UNIV"
    using contained gi_exact_generic_seed_index_recombination[OF index] by blast
  show ?thesis
  proof (rule ext)
    fix P
    have "- F P = UNIV"
      using fun_cong[OF represented, of P] universal by (simp add: pp_classifier_def)
    then show "F P = {}" by blast
  qed
qed

theorem gi_exact_generic_raw_seed_free:
  "gi_M3_free_for_stock pp_e_exact_operator_stock pp_e_generic_raw_seed"
  unfolding gi_M3_free_for_stock_def
proof (intro ballI impI notI)
  fix F assume stock: "F \<in> pp_e_exact_operator_stock" and nonzero: "F \<noteq> (\<lambda>P. {})"
    and vanishes: "F pp_e_generic_raw_seed = {}"
  have "F = (\<lambda>P. {})" by (rule gi_exact_generic_seed_vanishing_operator_zero[OF stock vanishes])
  then show False using nonzero by contradiction
qed

theorem gi_exact_generic_raw_seed_fun_prime:
  "pp_e_exact_fun_prime pp_e_generic_raw_seed"
  by (simp only: gi_exact_M3_fun_prime_iff_free; rule gi_exact_generic_raw_seed_free)

corollary gi_exact_generic_raw_seed_separates:
  assumes fs: "F \<in> pp_e_exact_operator_stock" and hs: "H \<in> pp_e_exact_operator_stock"
  shows "F pp_e_generic_raw_seed = H pp_e_generic_raw_seed \<longleftrightarrow> F = H"
proof
  assume same: "F pp_e_generic_raw_seed = H pp_e_generic_raw_seed"
  show "F = H" by (rule pp_e_exact_fun_primeD[OF gi_exact_generic_raw_seed_fun_prime fs hs same])
next
  assume "F = H"
  then show "F pp_e_generic_raw_seed = H pp_e_generic_raw_seed" by simp
qed

lemma gi_exact_generic_root_seed_extract:
  "pp_n_bacon_extract pp_e_generic_root_seed = pp_e_generic_raw_seed"
  by (simp add: pp_e_generic_root_seed_def)

theorem gi_exact_generic_root_seed_fun_prime:
  "pp_e_exact_fun_prime (pp_n_bacon_extract pp_e_generic_root_seed)"
  by (simp only: gi_exact_generic_root_seed_extract; rule gi_exact_generic_raw_seed_fun_prime)

corollary gi_exact_generic_seed_native_fun_prime:
  "sg_rich G \<Longrightarrow> gi_stock_fun_prime (gi_exact_native_operator_stock G) pp_e_generic_raw_seed"
  by (simp only: gi_exact_native_fun_prime_iff; rule gi_exact_generic_raw_seed_fun_prime)

section \<open>The chosen generic Fun interpretation at the root\<close>

lemma gi_exact_generic_seed_at_root:
  "pp_e_generic_seed_at [] = pp_e_generic_root_seed"
  using pp_e_generic_seed_at_action[of "[]"]
  by (simp only: rev.simps pp_b_action_one_all[OF pp_e_generic_seed_at_in_domain])

theorem gi_exact_generic_fundamental_root_fun_prime:
  assumes member: "Elem R (pp_e_domain Prop)"
    and fundamental: "pp_e_generic_fundamental_at Prop [] R"
  shows "pp_e_exact_fun_prime (pp_n_bacon_extract R)"
proof -
  have related: "pp_e_eqv Prop [] R pp_e_generic_root_seed"
    using fundamental by (simp only: pp_e_generic_fundamental_at.simps gi_exact_generic_seed_at_root)
  have equal: "R = pp_e_generic_root_seed"
    using related by (simp only: gi_exact_root_eqv[OF member pp_e_generic_root_seed_in_domain])
  show ?thesis by (simp only: equal; rule gi_exact_generic_root_seed_fun_prime)
qed

theorem gi_exact_generic_Fun_implies_fun_prime_root:
  assumes typed: "\<Gamma> \<turnstile> M : Prop" and env: "pp_e_env_typed \<Gamma> \<rho>"
    and fundamental: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_fun Prop M)) []"
  shows "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_fun_prime M)) []"
proof -
  have member: "Elem (pp_e_eval pp_e_generic_internal_constants \<rho> M) (pp_e_domain Prop)"
    using GenericExactBaconConstants.pp_e_eval_type[OF typed env] by (simp only: pp_e_dom_def)
  have fundamental_value: "pp_e_generic_fundamental_at Prop [] (pp_e_eval pp_e_generic_internal_constants \<rho> M)"
    using fundamental by (simp only: pp_e_generic_eval_fun_holds[OF typed env])
  have free: "pp_e_exact_fun_prime (pp_n_bacon_extract (pp_e_eval pp_e_generic_internal_constants \<rho> M))"
    by (rule gi_exact_generic_fundamental_root_fun_prime[OF member fundamental_value])
  show ?thesis by (simp only: gi_exact_fun_prime_root_iff[OF typed env]; rule free)
qed

text \<open>
  This identifies the actual generic seed used by the verified exact QLN
  interpretation. It does not identify every arbitrary Theorem 10.1 glued
  assignment with this seed, nor assert that every view of this one fixed
  seed is fun′. That latter statement is different from the root Fun
  clause of the moving-seed interpretation.
\<close>

end
