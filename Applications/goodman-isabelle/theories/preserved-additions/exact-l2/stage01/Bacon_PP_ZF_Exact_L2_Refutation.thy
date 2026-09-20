theory Bacon_PP_ZF_Exact_L2_Refutation
  imports 
    "Goodman_Exact_Stock_Legacy_01.Bacon_PP_ZF_Exact_L2_Obstruction"
begin

theorem pp_e_exact_right_cancellative_nonreversible_refutes_L2:
  assumes Z: "Z \<in> pp_e_exact_operator_stock"
    and cancellation: "pp_e_exact_right_cancellative Z"
    and nonreversible: "Z \<notin> pp_e_exact_G"
  shows "\<not> pp_e_exact_L2"
proof -
  obtain p where p: "pp_e_exact_fun_prime p"
    using pp_e_exact_fun_prime_exists by blast
  have Zp: "pp_e_exact_fun_prime (Z p)"
    using pp_e_exact_fun_prime_image_iff_right_cancellative[OF Z p]
      cancellation by blast
  have not_kind: "\<not> pp_e_exact_same_kind id Z"
    using nonreversible pp_e_exact_same_kind_id_imp_reversible by blast
  have not_pair: "\<not> pp_e_exact_L2_pair id Z"
  proof
    assume pair: "pp_e_exact_L2_pair id Z"
    have collisions:
        "\<forall>a b.
          pp_e_exact_fun_prime a \<longrightarrow>
          pp_e_exact_fun_prime b \<longrightarrow>
          id a = Z b \<longrightarrow>
          pp_e_exact_same_kind id Z"
      using pair unfolding pp_e_exact_L2_pair_def by (elim conjE) assumption
    have kind: "pp_e_exact_same_kind id Z"
      using collisions[rule_format, OF Zp p] by simp
    show False using not_kind kind by contradiction
  qed
  show ?thesis
  proof
    assume L2: "pp_e_exact_L2"
    have all_pairs:
        "\<forall>X \<in> pp_e_exact_operator_stock.
          \<forall>Y \<in> pp_e_exact_operator_stock.
            pp_e_exact_L2_pair X Y"
      using L2 unfolding pp_e_exact_L2_def .
    have pair: "pp_e_exact_L2_pair id Z"
      using all_pairs pp_e_exact_identity_in_stock Z by blast
    show False using not_pair pair by contradiction
  qed
qed

end
