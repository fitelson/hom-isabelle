theory Bacon_PP_ZF_Exact_L2_Generic
  imports 
    "Goodman_Exact_Stock_Legacy_01.Bacon_PP_ZF_Exact_L2_Generic_Prelim"
begin

theorem pp_e_generic_separator_for_exact_stock:
  "\<exists>R. \<forall>F \<in> pp_e_exact_operator_stock.
    \<forall>G \<in> pp_e_exact_operator_stock.
      (F R = G R \<longleftrightarrow> F = G)"
proof -
  obtain R where generic:
      "\<forall>S \<in> pp_e_exact_distinct_equalizers.
        \<not> pp_orbit R \<subseteq> S"
    using pp_generic_witness_for_countable_proper_stock[
      OF pp_e_exact_distinct_equalizers_countable
        pp_e_exact_distinct_equalizers_proper] by blast
  show ?thesis
  proof (intro exI[of _ R] ballI allI)
    fix F G
    assume F: "F \<in> pp_e_exact_operator_stock"
      and G: "G \<in> pp_e_exact_operator_stock"
    show "F R = G R \<longleftrightarrow> F = G"
    proof
      assume outputs: "F R = G R"
      show "F = G"
      proof (rule ccontr)
        assume distinct: "F \<noteq> G"
        let ?S = "pp_e_operator_equalizer F G"
        have S_bad: "?S \<in> pp_e_exact_distinct_equalizers"
          unfolding pp_e_exact_distinct_equalizers_def
          using F G distinct by auto
        have orbit_subset: "pp_orbit R \<subseteq> ?S"
        proof
          fix Q
          assume "Q \<in> pp_orbit R"
          then obtain i where Q: "Q = pp_view i R"
            unfolding pp_orbit_def by blast
          have F_view: "pp_view i (F R) = F (pp_view i R)"
            using pp_e_exact_operator_stock_equivariant[OF F]
            unfolding pp_equivariant_operator_def by blast
          have G_view: "pp_view i (G R) = G (pp_view i R)"
            using pp_e_exact_operator_stock_equivariant[OF G]
            unfolding pp_equivariant_operator_def by blast
          have roots:
              "pp_root_true (F (pp_view i R)) =
               pp_root_true (G (pp_view i R))"
            using outputs F_view G_view by simp
          show "Q \<in> ?S"
            unfolding Q pp_e_operator_equalizer_def using roots by simp
        qed
        show False using generic S_bad orbit_subset by blast
      qed
    next
      assume "F = G"
      then show "F R = G R" by simp
    qed
  qed
qed

definition pp_e_exact_fun_prime :: "pp_sem_prop \<Rightarrow> bool" where
  "pp_e_exact_fun_prime p \<longleftrightarrow>
    pp_stock_fun_prime pp_e_exact_operator_stock p"

lemma pp_e_exact_fun_primeI:
  assumes "\<And>F G. F \<in> pp_e_exact_operator_stock \<Longrightarrow>
    G \<in> pp_e_exact_operator_stock \<Longrightarrow>
    F p = G p \<Longrightarrow> F = G"
  shows "pp_e_exact_fun_prime p"
  using assms unfolding pp_e_exact_fun_prime_def
  by (rule pp_stock_fun_primeI)

lemma pp_e_exact_fun_primeD:
  assumes "pp_e_exact_fun_prime p"
    "F \<in> pp_e_exact_operator_stock"
    "G \<in> pp_e_exact_operator_stock"
    "F p = G p"
  shows "F = G"
  using assms unfolding pp_e_exact_fun_prime_def
  by (rule pp_stock_fun_primeD)

theorem pp_e_exact_fun_prime_exists:
  "\<exists>p. pp_e_exact_fun_prime p"
  using pp_e_generic_separator_for_exact_stock
  unfolding pp_e_exact_fun_prime_def pp_stock_fun_prime_def by blast

end
