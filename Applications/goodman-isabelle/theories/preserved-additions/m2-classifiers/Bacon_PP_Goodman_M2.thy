theory Bacon_PP_Goodman_M2
  imports
    
    "Goodman_Exact_Stock_Legacy_01.Bacon_PP_Heredity_Semantics"
    "HOL-Library.Equipollence"
begin

section \<open>Goodman M2: invariance is not purity\<close>

text \<open>
  Goodman's M2 has three mathematically distinct parts.  First, the invariant
  members of Bacon's unary function space are exactly the classifiers
  \<open>G\<^sub>T p = {i. i \<cdot> p \<in> T}\<close>.  Second, there are strictly more such
  classifiers than propositions.  Third, evaluation at any proposed
  fundamental proposition fails to be injective on the invariant stock.

  The first part is already the representation theorem
  \<open>pp_fun_invariant_is_classifier\<close>.  We package its exact range and then
  prove the cardinal and QSS consequences.  No interpretation of invariant
  operators as certified pure is made.
\<close>

definition pp_invariant_unary_stock ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) set" where
  "pp_invariant_unary_stock =
    {F. pp_function_space_member F \<and> pp_fun_invariant F}"

theorem pp_M2_classifier_bijection:
  "bij_betw pp_classifier
    (UNIV :: pp_sem_prop set set)
    pp_invariant_unary_stock"
  unfolding bij_betw_def
proof
  show "inj_on pp_classifier (UNIV :: pp_sem_prop set set)"
    using pp_classifier_injective by (simp add: inj_on_def inj_def)
next
  show "pp_classifier ` (UNIV :: pp_sem_prop set set) =
      pp_invariant_unary_stock"
  proof
    show "pp_classifier ` (UNIV :: pp_sem_prop set set)
        \<subseteq> pp_invariant_unary_stock"
      unfolding pp_invariant_unary_stock_def
      using pp_classifier_is_function_space_invariant by blast
  next
    show "pp_invariant_unary_stock
        \<subseteq> pp_classifier ` (UNIV :: pp_sem_prop set set)"
    proof
      fix F
      assume F_stock: "F \<in> pp_invariant_unary_stock"
      then have member: "pp_function_space_member F"
        and invariant: "pp_fun_invariant F"
        unfolding pp_invariant_unary_stock_def by blast+
      have "F = pp_classifier (pp_operator_index F)"
        using member invariant by (rule pp_fun_invariant_is_classifier)
      then show "F \<in> pp_classifier ` (UNIV :: pp_sem_prop set set)"
        by blast
    qed
  qed
qed

theorem pp_M2_invariant_operators_outnumber_propositions:
  "(UNIV :: pp_sem_prop set) \<prec> pp_invariant_unary_stock"
proof -
  have cantor:
      "(UNIV :: pp_sem_prop set) \<prec>
       (UNIV :: pp_sem_prop set set)"
    using lesspoll_Pow_self[of "(UNIV :: pp_sem_prop set)"]
    by simp
  have classifiers:
      "(UNIV :: pp_sem_prop set set) \<approx>
       pp_invariant_unary_stock"
    unfolding eqpoll_def
    by (rule exI[of _ pp_classifier],
        rule pp_M2_classifier_bijection)
  show ?thesis
    using cantor classifiers by (rule lesspoll_eq_trans)
qed

text \<open>
  We do not need a nonconstructive cardinality choice to find a proposition
  outside the orbit of \<open>R\<close>.  The following proposition is the direct Cantor
  diagonal against the orbit map \<open>i \<mapsto> i \<cdot> R\<close>.
\<close>

definition pp_M2_orbit_diagonal ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_M2_orbit_diagonal R =
    {i. i \<notin> pp_view i R}"

lemma pp_M2_orbit_diagonal_differs:
  "pp_M2_orbit_diagonal R \<noteq> pp_view i R"
proof
  assume equality:
      "pp_M2_orbit_diagonal R = pp_view i R"
  have "i \<in> pp_M2_orbit_diagonal R \<longleftrightarrow>
      i \<notin> pp_view i R"
    by (simp add: pp_M2_orbit_diagonal_def)
  also have "... \<longleftrightarrow>
      i \<notin> pp_M2_orbit_diagonal R"
    using equality by simp
  finally show False by blast
qed

theorem pp_M2_orbit_diagonal_outside:
  "pp_M2_orbit_diagonal R \<notin> pp_orbit R"
  unfolding pp_orbit_def
  using pp_M2_orbit_diagonal_differs by blast

lemma pp_M2_singleton_classifier_vanishes_at_R:
  "pp_classifier {pp_M2_orbit_diagonal R} R = {}"
proof (rule set_eqI)
  fix i
  have "i \<in> pp_classifier {pp_M2_orbit_diagonal R} R
      \<longleftrightarrow> pp_view i R = pp_M2_orbit_diagonal R"
    by (simp add: pp_classifier_def)
  also have "... \<longleftrightarrow> False"
    using pp_M2_orbit_diagonal_differs[of R i] by blast
  finally show "i \<in> pp_classifier {pp_M2_orbit_diagonal R} R
      \<longleftrightarrow> i \<in> {}"
    by simp
qed

lemma pp_M2_empty_classifier[simp]:
  "pp_classifier {} = (\<lambda>P. {})"
  by (rule ext) (simp add: pp_classifier_def)

lemma pp_M2_singleton_classifier_distinct:
  "pp_classifier {pp_M2_orbit_diagonal R} \<noteq> pp_classifier {}"
  using pp_classifier_injective
  unfolding inj_def by blast

theorem pp_M2_evaluation_not_injective:
  "\<not> inj_on (\<lambda>F. F R) pp_invariant_unary_stock"
proof
  let ?F = "pp_classifier {pp_M2_orbit_diagonal R}"
  let ?Z = "pp_classifier {}"
  assume injective:
      "inj_on (\<lambda>F. F R) pp_invariant_unary_stock"
  have F_stock: "?F \<in> pp_invariant_unary_stock"
    unfolding pp_invariant_unary_stock_def
    using pp_classifier_is_function_space_invariant by blast
  have Z_stock: "?Z \<in> pp_invariant_unary_stock"
    unfolding pp_invariant_unary_stock_def
    using pp_classifier_is_function_space_invariant by blast
  have agreement: "?F R = ?Z R"
    by (simp add: pp_M2_singleton_classifier_vanishes_at_R)
  have "?F = ?Z"
    using injective F_stock Z_stock agreement
    unfolding inj_on_def by blast
  then show False
    using pp_M2_singleton_classifier_distinct[of R] by contradiction
qed

corollary pp_M2_invariance_QSS_fails:
  "\<not> pp_stock_fun_prime pp_invariant_unary_stock R"
  unfolding pp_stock_fun_prime_def
proof
  assume qss:
      "\<forall>F\<in>pp_invariant_unary_stock.
       \<forall>G\<in>pp_invariant_unary_stock. F R = G R \<longrightarrow> F = G"
  have "inj_on (\<lambda>F. F R) pp_invariant_unary_stock"
    using qss unfolding inj_on_def by blast
  then show False
    using pp_M2_evaluation_not_injective[of R] by contradiction
qed

text \<open>
  Thus M2 is verified at the ambient semantic level.  The invariant unary
  stock is equipollent with the powerset of the propositions and is strictly
  larger than the proposition domain.  More decisively, for every candidate
  \<open>R\<close>, the distinct invariant operators
  \<open>G\<^sub>{X}\<close> and \<open>G\<^sub>{}\<close>, where \<open>X\<close> is the orbit diagonal, agree at
  \<open>R\<close>.  Consequently invariance cannot be the interpretation of certified
  purity in any model validating QSS at a fundamental proposition.
\<close>

end
