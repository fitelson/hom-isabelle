theory Bacon_PP_ZF_Exact_L2_Reduction
  imports 
    "Goodman_Exact_Stock_Legacy_01.Bacon_PP_ZF_Exact_L2_Generic"
begin

subsection \<open>Reversibility, kinds, and L2\<close>

definition pp_e_exact_reversible :: "pp_e_operator \<Rightarrow> bool" where
  "pp_e_exact_reversible Z \<longleftrightarrow>
    Z \<in> pp_e_exact_operator_stock \<and>
    (\<exists>W \<in> pp_e_exact_operator_stock.
      Z \<circ> W = id \<and> W \<circ> Z = id)"

definition pp_e_exact_G :: "pp_e_operator set" where
  "pp_e_exact_G = {Z. pp_e_exact_reversible Z}"

definition pp_e_exact_same_kind ::
    "pp_e_operator \<Rightarrow> pp_e_operator \<Rightarrow> bool" where
  "pp_e_exact_same_kind X Y \<longleftrightarrow>
    (\<exists>Z \<in> pp_e_exact_G. X = Y \<circ> Z)"

definition pp_e_exact_L2_pair ::
    "pp_e_operator \<Rightarrow> pp_e_operator \<Rightarrow> bool" where
  "pp_e_exact_L2_pair X Y \<longleftrightarrow>
    X \<in> pp_e_exact_operator_stock \<and>
    Y \<in> pp_e_exact_operator_stock \<and>
    (\<forall>p q.
      pp_e_exact_fun_prime p \<longrightarrow>
      pp_e_exact_fun_prime q \<longrightarrow>
      X p = Y q \<longrightarrow>
      pp_e_exact_same_kind X Y)"

definition pp_e_exact_L2 :: bool where
  "pp_e_exact_L2 \<longleftrightarrow>
    (\<forall>X \<in> pp_e_exact_operator_stock.
      \<forall>Y \<in> pp_e_exact_operator_stock.
        pp_e_exact_L2_pair X Y)"

definition pp_e_exact_strong_L2_pair ::
    "pp_e_operator \<Rightarrow> pp_e_operator \<Rightarrow> bool" where
  "pp_e_exact_strong_L2_pair X Y \<longleftrightarrow>
    X \<in> pp_e_exact_operator_stock \<and>
    Y \<in> pp_e_exact_operator_stock \<and>
    (\<forall>p q.
      pp_e_exact_fun_prime p \<longrightarrow>
      pp_e_exact_fun_prime q \<longrightarrow>
      X p = Y q \<longrightarrow>
      (\<exists>Z \<in> pp_e_exact_G.
        X = Y \<circ> Z \<and> q = Z p))"

definition pp_e_exact_strong_L2 :: bool where
  "pp_e_exact_strong_L2 \<longleftrightarrow>
    (\<forall>X \<in> pp_e_exact_operator_stock.
      \<forall>Y \<in> pp_e_exact_operator_stock.
        pp_e_exact_strong_L2_pair X Y)"

lemma pp_e_exact_strong_L2_imp_L2:
  assumes "pp_e_exact_strong_L2"
  shows "pp_e_exact_L2"
  using assms
  unfolding pp_e_exact_strong_L2_def pp_e_exact_strong_L2_pair_def
    pp_e_exact_L2_def pp_e_exact_L2_pair_def pp_e_exact_same_kind_def
  by blast

end
