theory Goodman_Exact_M3_Algebra
  imports Goodman_Integration_Exact_L2.Goodman_Exact_L2_Transfer
    Goodman_Exact_Recombination.Bacon_PP_ZF_Exact_Recombination
begin

section \<open>Actual closed logical witnesses for the M3 closure premises\<close>

definition gi_M3_zero_term where
  "gi_M3_zero_term = Lam Prop (Neg (Eq Prop (Var 0) (Var 0)))"

definition gi_M3_difference_term where
  "gi_M3_difference_term M N = Lam Prop
    (Disj (Conj (App (shift M) (Var 0)) (Neg (App (shift N) (Var 0))))
      (Conj (App (shift N) (Var 0)) (Neg (App (shift M) (Var 0)))))"

definition gi_M3_difference :: "pp_e_operator \<Rightarrow> pp_e_operator \<Rightarrow> pp_e_operator" where
  "gi_M3_difference F H = (\<lambda>P. (F P - H P) \<union> (H P - F P))"

lemma gi_M3_zero_term_type:
  "[] \<turnstile> gi_M3_zero_term : gb_unary"
  unfolding gi_M3_zero_term_def
  by (intro has_type.Lam has_type.Neg has_type.Eq has_type.Var; simp add: lookup_def)

lemma gi_M3_zero_term_logical:
  "pp_logical_vocabulary gi_M3_zero_term"
  by (simp add: gi_M3_zero_term_def pp_logical_vocabulary_def)

lemma gi_M3_difference_term_type:
  assumes mt: "[] \<turnstile> M : gb_unary" and nt: "[] \<turnstile> N : gb_unary"
  shows "[] \<turnstile> gi_M3_difference_term M N : gb_unary"
proof -
  have ms: "[Prop] \<turnstile> shift M : gb_unary" by (rule typed_shift_ctx[OF mt])
  have ns: "[Prop] \<turnstile> shift N : gb_unary" by (rule typed_shift_ctx[OF nt])
  have ma: "[Prop] \<turnstile> App (shift M) (Var 0) : Prop"
    by (rule has_type.App[OF ms typed_var0])
  have na: "[Prop] \<turnstile> App (shift N) (Var 0) : Prop"
    by (rule has_type.App[OF ns typed_var0])
  show ?thesis unfolding gi_M3_difference_term_def
    by (intro has_type.Lam has_type.Disj has_type.Conj has_type.Neg ma na)
qed

lemma gi_M3_difference_term_logical:
  "pp_logical_vocabulary M \<Longrightarrow> pp_logical_vocabulary N \<Longrightarrow>
    pp_logical_vocabulary (gi_M3_difference_term M N)"
  by (simp add: gi_M3_difference_term_def pp_logical_vocabulary_def shift_def consts_of_rename)

lemma gi_M3_zero_raw:
  "pp_e_raw_operator (pp_e_closed_den gi_M3_zero_term) = (\<lambda>P. {})"
proof (rule ext, rule set_eqI)
  fix P i
  have pm: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)"
    using pp_n_bacon_embed_in_domain[of P] by simp
  show "i \<in> pp_e_raw_operator (pp_e_closed_den gi_M3_zero_term) P \<longleftrightarrow> i \<in> (\<lambda>P. {}) P"
    using pm by (simp add: pp_e_raw_operator_def pp_e_closed_den_def gi_M3_zero_term_def
      Lambda_app pp_n_bacon_extract_def)
qed

lemma gi_M3_difference_raw:
  assumes mt: "[] \<turnstile> M : gb_unary" and nt: "[] \<turnstile> N : gb_unary"
  shows "pp_e_raw_operator (pp_e_closed_den (gi_M3_difference_term M N)) =
    gi_M3_difference (pp_e_raw_operator (pp_e_closed_den M)) (pp_e_raw_operator (pp_e_closed_den N))"
proof (rule ext, rule set_eqI)
  fix P i
  have pm: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)"
    using pp_n_bacon_embed_in_domain[of P] by simp
  have mm: "Elem (pp_e_closed_den M) (pp_e_domain gb_unary)"
    by (rule pp_e_closed_den_in_domain[OF mt])
  have nm: "Elem (pp_e_closed_den N) (pp_e_domain gb_unary)"
    by (rule pp_e_closed_den_in_domain[OF nt])
  have dm: "Elem (pp_e_closed_den (gi_M3_difference_term M N)) (pp_e_domain gb_unary)"
    by (rule pp_e_closed_den_in_domain[OF gi_M3_difference_term_type[OF mt nt]])
  have evaluation: "pp_e_holds (pp_e_closed_den (gi_M3_difference_term M N) \<acute> pp_n_bacon_embed P) (rev i) =
    ((pp_e_holds (pp_e_closed_den M \<acute> pp_n_bacon_embed P) (rev i) \<and>
       \<not> pp_e_holds (pp_e_closed_den N \<acute> pp_n_bacon_embed P) (rev i)) \<or>
     (pp_e_holds (pp_e_closed_den N \<acute> pp_n_bacon_embed P) (rev i) \<and>
       \<not> pp_e_holds (pp_e_closed_den M \<acute> pp_n_bacon_embed P) (rev i)))"
    using pm by (simp add: pp_e_closed_den_def gi_M3_difference_term_def Lambda_app pp_e_eval_shift)
  show "i \<in> pp_e_raw_operator (pp_e_closed_den (gi_M3_difference_term M N)) P \<longleftrightarrow>
      i \<in> gi_M3_difference (pp_e_raw_operator (pp_e_closed_den M)) (pp_e_raw_operator (pp_e_closed_den N)) P"
    using evaluation pp_e_raw_operator_mem_iff[OF dm pm, of i]
      pp_e_raw_operator_mem_iff[OF mm pm, of i] pp_e_raw_operator_mem_iff[OF nm pm, of i]
    by (simp add: gi_M3_difference_def)
qed

theorem gi_exact_M3_zero_in_stock:
  "(\<lambda>P. {}) \<in> pp_e_exact_operator_stock"
  using pp_e_exact_operator_stockI[OF gi_M3_zero_term_type gi_M3_zero_term_logical]
  by (simp only: gi_M3_zero_raw)

theorem gi_exact_M3_difference_closed:
  assumes fs: "F \<in> pp_e_exact_operator_stock" and hs: "H \<in> pp_e_exact_operator_stock"
  shows "gi_M3_difference F H \<in> pp_e_exact_operator_stock"
proof -
  obtain M where mt: "[] \<turnstile> M : gb_unary" and ml: "pp_logical_vocabulary M"
    and f: "F = pp_e_raw_operator (pp_e_closed_den M)" using fs by (rule pp_e_exact_operator_stockE)
  obtain N where nt: "[] \<turnstile> N : gb_unary" and nl: "pp_logical_vocabulary N"
    and h: "H = pp_e_raw_operator (pp_e_closed_den N)" using hs by (rule pp_e_exact_operator_stockE)
  have member: "pp_e_raw_operator (pp_e_closed_den (gi_M3_difference_term M N)) \<in> pp_e_exact_operator_stock"
    by (rule pp_e_exact_operator_stockI[OF gi_M3_difference_term_type[OF mt nt]
      gi_M3_difference_term_logical[OF ml nl]])
  show ?thesis using member by (simp only: gi_M3_difference_raw[OF mt nt] f h)
qed

section \<open>The free-generator characterization with premises discharged\<close>

definition gi_M3_free_for_stock where
  "gi_M3_free_for_stock S p \<longleftrightarrow> (\<forall>F\<in>S. F \<noteq> (\<lambda>P. {}) \<longrightarrow> F p \<noteq> {})"

lemma gi_M3_difference_zero_iff:
  "gi_M3_difference F H = (\<lambda>P. {}) \<longleftrightarrow> F = H"
proof
  assume zero: "gi_M3_difference F H = (\<lambda>P. {})"
  show "F = H"
  proof (rule ext, rule set_eqI)
    fix P i
    have "(F P - H P) \<union> (H P - F P) = {}"
      using fun_cong[OF zero, of P] by (simp only: gi_M3_difference_def)
    then show "i \<in> F P \<longleftrightarrow> i \<in> H P" by blast
  qed
next
  assume "F = H"
  then show "gi_M3_difference F H = (\<lambda>P. {})" by (simp add: gi_M3_difference_def)
qed

theorem gi_exact_M3_fun_prime_iff_free:
  "pp_e_exact_fun_prime p \<longleftrightarrow> gi_M3_free_for_stock pp_e_exact_operator_stock p"
proof
  assume fp: "pp_e_exact_fun_prime p"
  show "gi_M3_free_for_stock pp_e_exact_operator_stock p"
    unfolding gi_M3_free_for_stock_def
  proof (intro ballI impI notI)
    fix F assume fs: "F \<in> pp_e_exact_operator_stock" and nz: "F \<noteq> (\<lambda>P. {})" and zero: "F p = {}"
    have "F = (\<lambda>P. {})"
      by (rule pp_e_exact_fun_primeD[OF fp fs gi_exact_M3_zero_in_stock]; rule zero)
    then show False using nz by contradiction
  qed
next
  assume free: "gi_M3_free_for_stock pp_e_exact_operator_stock p"
  show "pp_e_exact_fun_prime p"
  proof (rule pp_e_exact_fun_primeI)
    fix F H assume fs: "F \<in> pp_e_exact_operator_stock" and hs: "H \<in> pp_e_exact_operator_stock"
      and equal: "F p = H p"
    have ds: "gi_M3_difference F H \<in> pp_e_exact_operator_stock"
      by (rule gi_exact_M3_difference_closed[OF fs hs])
    have "gi_M3_difference F H p = {}" using equal by (simp add: gi_M3_difference_def)
    then have "gi_M3_difference F H = (\<lambda>P. {})" using free ds unfolding gi_M3_free_for_stock_def by blast
    then show "F = H" by (simp only: gi_M3_difference_zero_iff)
  qed
qed

corollary gi_native_M3_fun_prime_iff_free:
  assumes rich: "sg_rich G"
  shows "gi_stock_fun_prime (gi_exact_native_operator_stock G) p
    \<longleftrightarrow> gi_M3_free_for_stock (gi_exact_native_operator_stock G) p"
  using gi_exact_native_fun_prime_iff[OF rich, of p] gi_exact_M3_fun_prime_iff_free[of p]
  by (simp only: gi_exact_native_operator_stock_eq[OF rich]; blast)

corollary gi_native_M3_free_generator_exists:
  "sg_rich G \<Longrightarrow> \<exists>p. gi_M3_free_for_stock (gi_exact_native_operator_stock G) p"
  using gi_exact_native_fun_prime_exists gi_native_M3_fun_prime_iff_free by blast

text \<open>
  This instantiates the algebraic part of M3 for the COMPLETE exact logical
  stock: zero and Boolean difference are represented by closed logical
  terms, not left as unproved closure assumptions. Freeness means absence
  of a nonzero unary law at p. Extreme-view and product-topology claims,
  and identification with a particular glued fundamental proposition,
  remain separate obligations. No PP assumption is used.
\<close>

end
