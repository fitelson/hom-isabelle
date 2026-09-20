theory Bacon_PP_ZF_Exact_L2_Generic_Prelim
  imports 
    "Goodman_Exact_Stock_Legacy_01.Bacon_PP_ZF_Exact_L2_Model"
begin

subsection \<open>A fun-prime proposition for the exact stock\<close>

definition pp_e_operator_equalizer ::
    "pp_e_operator \<Rightarrow> pp_e_operator \<Rightarrow> pp_sem_prop set"
  where
  "pp_e_operator_equalizer F G =
    {P. pp_root_true (F P) = pp_root_true (G P)}"

lemma pp_e_distinct_equivariant_equalizer_proper:
  assumes F_eqv: "pp_equivariant_operator F"
    and G_eqv: "pp_equivariant_operator G"
    and distinct: "F \<noteq> G"
  shows "pp_e_operator_equalizer F G \<noteq> UNIV"
proof
  assume universal: "pp_e_operator_equalizer F G = UNIV"
  have indices: "pp_operator_index F = pp_operator_index G"
    unfolding pp_operator_index_def
  proof (rule set_eqI)
    fix P
    have "P \<in> pp_e_operator_equalizer F G"
      using universal by simp
    then show "(P \<in> {P. pp_root_true (F P)}) =
        (P \<in> {P. pp_root_true (G P)})"
      unfolding pp_e_operator_equalizer_def by simp
  qed
  have F_classifier: "F = pp_classifier (pp_operator_index F)"
    by (rule pp_equivariant_operator_is_classifier[OF F_eqv])
  have G_classifier: "G = pp_classifier (pp_operator_index G)"
    by (rule pp_equivariant_operator_is_classifier[OF G_eqv])
  have "F = G"
  proof -
    have "F = pp_classifier (pp_operator_index F)"
      by (rule F_classifier)
    also have "... = pp_classifier (pp_operator_index G)"
      using indices by simp
    also have "... = G"
      using G_classifier by simp
    finally show ?thesis .
  qed
  then show False using distinct by contradiction
qed

definition pp_e_exact_distinct_equalizers :: "pp_sem_prop set set" where
  "pp_e_exact_distinct_equalizers =
    (\<lambda>(F,G). pp_e_operator_equalizer F G) `
      {(F,G) \<in>
        pp_e_exact_operator_stock \<times> pp_e_exact_operator_stock.
        F \<noteq> G}"

lemma pp_e_exact_distinct_equalizers_countable:
  "countable pp_e_exact_distinct_equalizers"
proof -
  have pairs:
      "countable
        (pp_e_exact_operator_stock \<times> pp_e_exact_operator_stock)"
    using pp_e_exact_operator_stock_countable by simp
  have distinct_pairs:
      "countable
        {(F,G) \<in>
          pp_e_exact_operator_stock \<times> pp_e_exact_operator_stock.
          F \<noteq> G}"
    by (rule countable_subset[OF _ pairs]) auto
  show ?thesis
    unfolding pp_e_exact_distinct_equalizers_def
    by (rule countable_image[OF distinct_pairs])
qed

lemma pp_e_exact_distinct_equalizers_proper:
  assumes "S \<in> pp_e_exact_distinct_equalizers"
  shows "S \<noteq> UNIV"
proof -
  obtain F G where F: "F \<in> pp_e_exact_operator_stock"
    and G: "G \<in> pp_e_exact_operator_stock"
    and distinct: "F \<noteq> G"
    and S: "S = pp_e_operator_equalizer F G"
    using assms unfolding pp_e_exact_distinct_equalizers_def by auto
  show ?thesis
    unfolding S
    by (rule pp_e_distinct_equivariant_equalizer_proper[
        OF pp_e_exact_operator_stock_equivariant[OF F]
          pp_e_exact_operator_stock_equivariant[OF G] distinct])
qed

end
