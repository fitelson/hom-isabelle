theory Bacon_PP_ZF_Exact_L2_Cancellation
  imports 
    "Goodman_Exact_Stock_Legacy_01.Bacon_PP_ZF_Exact_L2_Reduction"
begin

definition pp_e_exact_right_cancellative ::
    "pp_e_operator \<Rightarrow> bool" where
  "pp_e_exact_right_cancellative X \<longleftrightarrow>
    (\<forall>A \<in> pp_e_exact_operator_stock.
      \<forall>B \<in> pp_e_exact_operator_stock.
        A \<circ> X = B \<circ> X \<longrightarrow> A = B)"

theorem pp_e_exact_fun_prime_image_iff_right_cancellative:
  assumes X: "X \<in> pp_e_exact_operator_stock"
    and p: "pp_e_exact_fun_prime p"
  shows "pp_e_exact_fun_prime (X p) \<longleftrightarrow>
    pp_e_exact_right_cancellative X"
proof
  assume image: "pp_e_exact_fun_prime (X p)"
  show "pp_e_exact_right_cancellative X"
  proof (unfold pp_e_exact_right_cancellative_def, intro ballI impI)
    fix A B
    assume A: "A \<in> pp_e_exact_operator_stock"
      and B: "B \<in> pp_e_exact_operator_stock"
      and equality: "A \<circ> X = B \<circ> X"
    have at_image: "A (X p) = B (X p)"
      using fun_cong[OF equality, of p] by simp
    show "A = B"
      using image A B at_image by (rule pp_e_exact_fun_primeD)
  qed
next
  assume cancellation: "pp_e_exact_right_cancellative X"
  show "pp_e_exact_fun_prime (X p)"
  proof (rule pp_e_exact_fun_primeI)
    fix A B
    assume A: "A \<in> pp_e_exact_operator_stock"
      and B: "B \<in> pp_e_exact_operator_stock"
      and at_image: "A (X p) = B (X p)"
    have AX: "A \<circ> X \<in> pp_e_exact_operator_stock"
      using A X by (rule pp_e_exact_operator_stock_compose)
    have BX: "B \<circ> X \<in> pp_e_exact_operator_stock"
      using B X by (rule pp_e_exact_operator_stock_compose)
    have at_p: "(A \<circ> X) p = (B \<circ> X) p"
      using at_image by simp
    have composition: "A \<circ> X = B \<circ> X"
      using p AX BX at_p by (rule pp_e_exact_fun_primeD)
    show "A = B"
      using cancellation A B composition
      unfolding pp_e_exact_right_cancellative_def by blast
  qed
qed

end
