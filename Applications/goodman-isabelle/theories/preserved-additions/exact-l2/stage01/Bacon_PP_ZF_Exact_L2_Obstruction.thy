theory Bacon_PP_ZF_Exact_L2_Obstruction
  imports 
    "Goodman_Exact_Stock_Legacy_01.Bacon_PP_ZF_Exact_L2_Cancellation"
begin

lemma pp_e_exact_same_kind_id_imp_reversible:
  assumes kind: "pp_e_exact_same_kind id Z"
  shows "Z \<in> pp_e_exact_G"
proof -
  obtain W where W_G: "W \<in> pp_e_exact_G"
    and id_ZW: "id = Z \<circ> W"
    using kind unfolding pp_e_exact_same_kind_def by blast
  obtain V where W_stock: "W \<in> pp_e_exact_operator_stock"
    and V_stock: "V \<in> pp_e_exact_operator_stock"
    and WV: "W \<circ> V = id"
    and VW: "V \<circ> W = id"
    using W_G unfolding pp_e_exact_G_def pp_e_exact_reversible_def by blast
  have Z_V: "Z = V"
  proof (rule ext)
    fix x
    have wv: "W (V x) = x"
      using fun_cong[OF WV, of x] by simp
    have zw: "Z (W (V x)) = V x"
      using fun_cong[OF id_ZW, of "V x"] by simp
    show "Z x = V x" using wv zw by simp
  qed
  have V_G: "V \<in> pp_e_exact_G"
    unfolding pp_e_exact_G_def pp_e_exact_reversible_def
    using V_stock W_stock VW WV by blast
  show ?thesis using V_G Z_V by simp
qed

end
