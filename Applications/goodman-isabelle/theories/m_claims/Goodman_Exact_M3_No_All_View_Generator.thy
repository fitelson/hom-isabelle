theory Goodman_Exact_M3_No_All_View_Generator
  imports Goodman_Exact_Generic_Fun_Prime Goodman_Exact_M3_Extreme_Views
begin

section \<open>The empty proposition is not a generator for the complete exact stock\<close>

lemma gi_exact_M3_empty_not_fun_prime:
  "\<not> pp_e_exact_fun_prime {}"
proof
  assume fp: "pp_e_exact_fun_prime {}"
  have equal: "(id :: pp_e_operator) = (\<lambda>P. {})"
    by (rule pp_e_exact_fun_primeD[OF fp pp_e_exact_identity_in_stock gi_exact_M3_zero_in_stock]; simp)
  have at_top: "(id :: pp_e_operator) UNIV = (\<lambda>P. {}) UNIV"
    by (rule fun_cong[OF equal])
  then show False by simp
qed

section \<open>No fixed proposition has only fun′ views\<close>

theorem gi_exact_M3_no_all_view_generator:
  "\<not> (\<forall>i. pp_e_exact_fun_prime (pp_view i R))"
proof
  assume all: "\<forall>i. pp_e_exact_fun_prime (pp_view i R)"
  have root: "pp_e_exact_fun_prime R" using all[rule_format, of "[]"] by simp
  have empty_orbit: "{} \<in> pp_orbit R"
    using gi_exact_M3_fun_prime_has_extreme_views[OF root] by blast
  obtain i where empty: "pp_view i R = {}"
    using empty_orbit unfolding pp_orbit_def by blast
  have "pp_e_exact_fun_prime {}" using all[rule_format, of i] by (simp only: empty)
  then show False using gi_exact_M3_empty_not_fun_prime by contradiction
qed

corollary gi_exact_M3_some_view_not_fun_prime:
  "\<exists>i. \<not> pp_e_exact_fun_prime (pp_view i R)"
  using gi_exact_M3_no_all_view_generator[of R] by blast

theorem gi_exact_M3_fixed_necessitated_QSS_impossible:
  "\<not> pp_stock_necessitated_QSS pp_e_exact_operator_stock R"
proof
  assume qss: "pp_stock_necessitated_QSS pp_e_exact_operator_stock R"
  have all: "\<forall>i. pp_e_exact_fun_prime (pp_view i R)"
    using qss unfolding pp_stock_necessitated_QSS_def pp_e_exact_fun_prime_def .
  show False using all gi_exact_M3_no_all_view_generator[of R] by contradiction
qed

corollary gi_native_M3_no_all_view_generator:
  assumes rich: "sg_rich G"
  shows "\<not> (\<forall>i. gi_stock_fun_prime (gi_exact_native_operator_stock G) (pp_view i R))"
  by (simp only: gi_exact_native_fun_prime_iff[OF rich]; rule gi_exact_M3_no_all_view_generator)

theorem gi_exact_generic_root_and_views_differ:
  "pp_e_exact_fun_prime pp_e_generic_raw_seed \<and>
    (\<exists>i. \<not> pp_e_exact_fun_prime (pp_view i pp_e_generic_raw_seed))"
  by (rule conjI[OF gi_exact_generic_raw_seed_fun_prime gi_exact_M3_some_view_not_fun_prime])

text \<open>
  This refutes the literal fixed-R premise pp_stock_necessitated_QSS
  for the complete exact closed-logical stock. It does not refute the
  object-language theorem □QSS: that formula retains a Fun antecedent,
  whereas the displayed fixed-R condition quantifies over every view
  of one proposition without requiring that view to be fundamental.

  In particular, the verified generic moving-seed interpretation does
  not identify Fun at every world with a fixed R's entire orbit. Its
  actual root seed is fun′, but some views of that same fixed raw seed
  are not. The two statements are compatible.

  Conditional M4/M6 results using this fixed-R premise cannot be
  instantiated with this exact stock. This does not show their intended
  conclusions false. A new construction may use preimage heredity from
  a single free view, without requiring every view of R to be free.
\<close>

end
