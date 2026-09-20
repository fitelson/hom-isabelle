theory Bacon_PP_ZF_Exact_L2_Child_Variation
  imports 
    "Goodman_Exact_Stock_Legacy_01.Bacon_PP_ZF_Exact_L2_Child_Variation_Semantics"
begin

subsection \<open>Cancellation and reversibility\<close>

definition pp_e_child_variation_preimage :: pp_e_operator where
  "pp_e_child_variation_preimage S =
    {0 # v |v. v \<in> S}"

lemma pp_e_child_variation_preimage_mem[simp]:
  "n # i \<in> pp_e_child_variation_preimage S
    \<longleftrightarrow> n = 0 \<and> i \<in> S"
proof
  assume membership: "n # i \<in> pp_e_child_variation_preimage S"
  then obtain v where v: "v \<in> S"
    and equality: "n # i = 0 # v"
    unfolding pp_e_child_variation_preimage_def by blast
  then show "n = 0 \<and> i \<in> S"
    using v by simp
next
  assume "n = 0 \<and> i \<in> S"
  then show "n # i \<in> pp_e_child_variation_preimage S"
    unfolding pp_e_child_variation_preimage_def by blast
qed

lemma pp_e_child_variation_preimage_right_inverse:
  "pp_e_child_variation (pp_e_child_variation_preimage S) = S"
proof (rule set_eqI)
  fix i
  show "i \<in> pp_e_child_variation
      (pp_e_child_variation_preimage S) \<longleftrightarrow> i \<in> S"
  proof
    assume membership:
        "i \<in> pp_e_child_variation
          (pp_e_child_variation_preimage S)"
    then obtain n where
        "n # i \<in> pp_e_child_variation_preimage S"
      unfolding pp_e_child_variation_def by blast
    then show "i \<in> S" by simp
  next
    assume i: "i \<in> S"
    have positive: "0 # i \<in> pp_e_child_variation_preimage S"
      using i by simp
    have negative: "1 # i \<notin> pp_e_child_variation_preimage S"
      by simp
    show "i \<in> pp_e_child_variation
        (pp_e_child_variation_preimage S)"
      unfolding pp_e_child_variation_def using positive negative by blast
  qed
qed

theorem pp_e_child_variation_surjective:
  "surj pp_e_child_variation"
  unfolding surj_def
  using pp_e_child_variation_preimage_right_inverse by blast

lemma pp_e_child_variation_complement:
  "pp_e_child_variation (- P) = pp_e_child_variation P"
  unfolding pp_e_child_variation_def
  by (rule set_eqI) auto

theorem pp_e_child_variation_not_injective:
  "\<not> inj pp_e_child_variation"
proof -
  have same: "pp_e_child_variation {} = pp_e_child_variation UNIV"
    using pp_e_child_variation_complement[of "{}"] by simp
  have distinct: "({} :: pp_sem_prop) \<noteq> UNIV"
    by simp
  show ?thesis
    using same distinct unfolding inj_def by blast
qed

corollary pp_e_child_variation_not_bijective:
  "\<not> bij pp_e_child_variation"
  using pp_e_child_variation_not_injective unfolding bij_def by blast

theorem pp_e_exact_child_variation_right_cancellative:
  "pp_e_exact_right_cancellative pp_e_child_variation"
  unfolding pp_e_exact_right_cancellative_def
proof (intro ballI impI)
  fix A B
  assume equality:
      "A \<circ> pp_e_child_variation = B \<circ> pp_e_child_variation"
  show "A = B"
  proof (rule ext)
    fix S
    let ?P = "pp_e_child_variation_preimage S"
    have preimage: "pp_e_child_variation ?P = S"
      by (rule pp_e_child_variation_preimage_right_inverse)
    have at_preimage:
        "A (pp_e_child_variation ?P) = B (pp_e_child_variation ?P)"
      using fun_cong[OF equality, of ?P] by simp
    show "A S = B S"
      using at_preimage preimage by simp
  qed
qed

theorem pp_e_child_variation_not_exact_reversible:
  "\<not> pp_e_exact_reversible pp_e_child_variation"
proof
  assume reversible:
      "pp_e_exact_reversible pp_e_child_variation"
  have inverse_exists:
      "\<exists>W \<in> pp_e_exact_operator_stock.
        pp_e_child_variation \<circ> W = id \<and>
        W \<circ> pp_e_child_variation = id"
    using reversible unfolding pp_e_exact_reversible_def
    by (elim conjE)
  then obtain W where left_inverse:
      "W \<circ> pp_e_child_variation = id"
    by blast
  have at_empty:
      "W (pp_e_child_variation {}) = ({} :: pp_sem_prop)"
    using fun_cong[OF left_inverse, of "{}"] by simp
  have at_univ:
      "W (pp_e_child_variation UNIV) = (UNIV :: pp_sem_prop)"
    using fun_cong[OF left_inverse, of UNIV] by simp
  have collision:
      "pp_e_child_variation {} = pp_e_child_variation UNIV"
    using pp_e_child_variation_complement[of "{}"] by simp
  have "({} :: pp_sem_prop) = UNIV"
    using at_empty at_univ collision by simp
  show False
    using \<open>({} :: pp_sem_prop) = UNIV\<close> by simp
qed

corollary pp_e_child_variation_not_in_exact_G:
  "pp_e_child_variation \<notin> pp_e_exact_G"
  using pp_e_child_variation_not_exact_reversible
  unfolding pp_e_exact_G_def by simp

corollary pp_e_child_variation_preserves_fun_prime:
  assumes "pp_e_exact_fun_prime p"
  shows "pp_e_exact_fun_prime (pp_e_child_variation p)"
  using pp_e_exact_fun_prime_image_iff_right_cancellative[
      OF pp_e_child_variation_in_exact_stock assms]
    pp_e_exact_child_variation_right_cancellative
  by blast

theorem pp_e_child_variation_refutes_exact_L2:
  "\<not> pp_e_exact_L2"
  using pp_e_child_variation_in_exact_stock
    pp_e_exact_child_variation_right_cancellative
    pp_e_child_variation_not_in_exact_G
  by (rule pp_e_exact_right_cancellative_nonreversible_refutes_L2)

corollary pp_e_child_variation_refutes_exact_strong_L2:
  "\<not> pp_e_exact_strong_L2"
  using pp_e_child_variation_refutes_exact_L2
    pp_e_exact_strong_L2_imp_L2 by blast

end
