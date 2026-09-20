theory Goodman_Exact_M6_Repair
  imports Goodman_Exact_M3_Extreme_Views
begin

section \<open>M6 without the impossible fixed-witness necessitated-QSS premise\<close>

text \<open>
  The historical M6 construction used pp_stock_necessitated_QSS Stock r,
  requiring fun′ at every view of one fixed r. That is not the premise used
  here. For the actual exact closed-logical stock, we need only one existing
  fun′ proposition and equivariance of each stock operator. A proposition
  with one fun′ view is itself fun′. Copies on a fresh branch therefore give
  the separation and inclusion constructions directly.

  We reconstruct the geometric argument of Bacon_PP_Goodman_M6 without
  importing its comparison-model/M5 chain. Words act by right division:
  view_i(P) = {u : u @ i ∈ P}. No particular glued fundamental proposition
  is identified with the chosen fun′ witness.
\<close>

theorem gi_exact_M6_fun_prime_preimage:
  assumes view: "pp_e_exact_fun_prime (pp_view i p)"
  shows "pp_e_exact_fun_prime p"
proof (rule pp_e_exact_fun_primeI)
  fix F H
  assume fs: "F \<in> pp_e_exact_operator_stock" and hs: "H \<in> pp_e_exact_operator_stock"
    and same: "F p = H p"
  have fe: "pp_equivariant_operator F" by (rule pp_e_exact_operator_stock_equivariant[OF fs])
  have he: "pp_equivariant_operator H" by (rule pp_e_exact_operator_stock_equivariant[OF hs])
  have fv: "F (pp_view i p) = pp_view i (F p)" using fe unfolding pp_equivariant_operator_def by blast
  have hv: "H (pp_view i p) = pp_view i (H p)" using he unfolding pp_equivariant_operator_def by blast
  have same_at_view: "F (pp_view i p) = H (pp_view i p)" using fv hv same by simp
  show "F = H" by (rule pp_e_exact_fun_primeD[OF view fs hs same_at_view])
qed

lemma gi_exact_M6_fun_prime_not_extreme:
  assumes fp: "pp_e_exact_fun_prime p"
  shows "p \<noteq> {}" "p \<noteq> UNIV"
  using gi_exact_M3_fun_prime_has_extreme_views[OF fp]
  by (auto simp: pp_orbit_def pp_view_def)

section \<open>Fun′ propositions separate every two distinct substitutions\<close>

lemma gi_M6_fresh_letter:
  fixes i j :: pp_word
  obtains n :: nat where "n \<notin> set i \<union> set j"
proof -
  let ?n = "Suc (Max (insert 0 (set i \<union> set j)))"
  have fresh: "?n \<notin> set i \<union> set j"
  proof
    assume member: "?n \<in> set i \<union> set j"
    have "?n \<le> Max (insert 0 (set i \<union> set j))"
      by (rule Max_ge) (use member in auto)
    then show False by simp
  qed
  show thesis by (rule that[OF fresh])
qed

lemma gi_M6_fresh_branch_view:
  assumes fresh: "n \<notin> set i"
  shows "pp_view [n] (pp_lift [n] r \<union> {i}) = r"
proof -
  have marker: "pp_view [n] {i} = {}"
    using fresh by (auto simp: pp_view_def)
  have distribution: "pp_view [n] (pp_lift [n] r \<union> {i}) =
    pp_view [n] (pp_lift [n] r) \<union> pp_view [n] {i}"
    by (auto simp: pp_view_def)
  show ?thesis by (simp only: distribution pp_view_lift marker Un_empty_right)
qed

lemma gi_M6_fresh_branch_excludes:
  assumes fresh: "n \<notin> set j" and distinct: "i \<noteq> j"
  shows "j \<notin> pp_lift [n] r \<union> {i}"
  using assms by (auto simp: pp_lift_def)

theorem gi_exact_M6_fun_prime_truth_separates:
  assumes distinct: "i \<noteq> j"
  shows "\<exists>p. pp_e_exact_fun_prime p \<and> i \<in> p \<and> j \<notin> p"
proof -
  obtain r where fp: "pp_e_exact_fun_prime r" using pp_e_exact_fun_prime_exists by blast
  obtain n :: nat where fresh: "n \<notin> set i \<union> set j" by (rule gi_M6_fresh_letter)
  have fi: "n \<notin> set i" and fj: "n \<notin> set j" using fresh by auto
  let ?p = "pp_lift [n] r \<union> {i}"
  have view: "pp_view [n] ?p = r" by (rule gi_M6_fresh_branch_view[OF fi])
  have view_fp: "pp_e_exact_fun_prime (pp_view [n] ?p)" using fp by (simp only: view)
  have pfp: "pp_e_exact_fun_prime ?p" by (rule gi_exact_M6_fun_prime_preimage[OF view_fp])
  have out: "j \<notin> ?p" by (rule gi_M6_fresh_branch_excludes[OF fj distinct])
  show ?thesis using pfp out by (intro exI[where x="?p"]; auto)
qed

theorem gi_exact_M6_fun_prime_separates_distinct_substitutions:
  assumes distinct: "i \<noteq> j"
  shows "\<exists>p. pp_e_exact_fun_prime p \<and> pp_view i p \<noteq> pp_view j p"
proof -
  obtain p where fp: "pp_e_exact_fun_prime p" and at_i: "i \<in> p" and at_j: "j \<notin> p"
    using gi_exact_M6_fun_prime_truth_separates[OF distinct] by blast
  have i_root: "[] \<in> pp_view i p" using at_i by (simp add: pp_view_def)
  have j_root: "[] \<notin> pp_view j p" using at_j by (simp add: pp_view_def)
  have different: "pp_view i p \<noteq> pp_view j p" using i_root j_root by blast
  show ?thesis using fp different by blast
qed

corollary gi_native_M6_fun_prime_separates_distinct_substitutions:
  assumes rich: "sg_rich G" and distinct: "i \<noteq> j"
  shows "\<exists>p. gi_stock_fun_prime (gi_exact_native_operator_stock G) p \<and> pp_view i p \<noteq> pp_view j p"
  using gi_exact_M6_fun_prime_separates_distinct_substitutions[OF distinct]
  by (simp only: gi_exact_native_fun_prime_iff[OF rich])

section \<open>Even one coordinate cannot realize every arbitrary target\<close>

definition gi_M6_orbit_diagonal :: "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "gi_M6_orbit_diagonal p = {i. i \<notin> pp_view i p}"

lemma gi_M6_orbit_diagonal_differs:
  "pp_view i p \<noteq> gi_M6_orbit_diagonal p"
proof
  assume same: "pp_view i p = gi_M6_orbit_diagonal p"
  have diagonal: "i \<in> gi_M6_orbit_diagonal p \<longleftrightarrow> i \<notin> pp_view i p"
    by (simp only: gi_M6_orbit_diagonal_def mem_Collect_eq)
  show False using same diagonal by blast
qed

theorem gi_M6_single_proposition_independence_fails:
  "\<exists>q. \<forall>i. pp_view i p \<noteq> q"
  by (rule exI[where x="gi_M6_orbit_diagonal p"], rule allI, rule gi_M6_orbit_diagonal_differs)

text \<open>
  This is the original single-coordinate claim: the target q is an arbitrary
  proposition, not asserted to be fun′ or pure. The diagonal proves failure
  of surjectivity of a fixed proposition's substitution orbit; it does not
  claim the stronger failure to cover every fun′ target.
\<close>

section \<open>Equivariance forces extreme inputs to have extreme outputs\<close>

lemma gi_M6_equivariant_empty_extreme:
  assumes equivariant: "pp_equivariant_operator F"
  shows "F {} = {} \<or> F {} = UNIV"
proof -
  have invariant: "pp_view i (F {}) = F {}" for i
  proof -
    have commutes: "pp_view i (F {}) = F (pp_view i {})"
      using equivariant unfolding pp_equivariant_operator_def by blast
    show ?thesis using commutes by (simp add: pp_view_def)
  qed
  have root: "i \<in> F {} \<longleftrightarrow> [] \<in> F {}" for i
  proof -
    have "i \<in> F {} \<longleftrightarrow> [] \<in> pp_view i (F {})" by (simp add: pp_view_def)
    then show ?thesis by (simp only: invariant)
  qed
  show ?thesis
  proof (cases "[] \<in> F {}")
    case True
    have "F {} = UNIV" using root True by blast
    then show ?thesis by blast
  next
    case False
    have "F {} = {}" using root False by blast
    then show ?thesis by blast
  qed
qed

corollary gi_exact_M6_pure_empty_extreme:
  "F \<in> pp_e_exact_operator_stock \<Longrightarrow> F {} = {} \<or> F {} = UNIV"
  by (rule gi_M6_equivariant_empty_extreme, rule pp_e_exact_operator_stock_equivariant; assumption)

definition gi_M6_pure_images :: "pp_e_operator set \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop set" where
  "gi_M6_pure_images S p = (\<lambda>F. F p) ` S"

definition gi_M6_pure_reversible_orbit :: "pp_e_operator set \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop set" where
  "gi_M6_pure_reversible_orbit S p = (\<lambda>F. F p) ` gi_stock_group S"

lemma gi_M6_reversible_orbit_subset_images:
  "gi_M6_pure_reversible_orbit S p \<subseteq> gi_M6_pure_images S p"
  unfolding gi_M6_pure_reversible_orbit_def gi_M6_pure_images_def gi_stock_group_def gi_stock_reversible_def by blast

definition gi_M6_left_copy :: "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "gi_M6_left_copy r = pp_lift [0] r"

definition gi_M6_two_copies :: "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "gi_M6_two_copies r = pp_lift [0] r \<union> pp_lift [1] r"

lemma gi_M6_copy_views:
  "pp_view [0] (gi_M6_left_copy r) = r"
  "pp_view [1] (gi_M6_left_copy r) = {}"
  "pp_view [0] (gi_M6_two_copies r) = r"
  "pp_view [1] (gi_M6_two_copies r) = r"
  by (auto simp: gi_M6_left_copy_def gi_M6_two_copies_def pp_view_def pp_lift_def append_singleton_eq_iff)

lemma gi_M6_views_preserve_inclusion:
  "p \<subseteq> q \<Longrightarrow> pp_view i p \<subseteq> pp_view i q"
  by (auto simp: pp_view_def)

theorem gi_exact_M6_fun_prime_strict_pair:
  assumes fp: "pp_e_exact_fun_prime r"
  shows "pp_e_exact_fun_prime (gi_M6_left_copy r) \<and>
    pp_e_exact_fun_prime (gi_M6_two_copies r) \<and>
    gi_M6_left_copy r \<subset> gi_M6_two_copies r \<and>
    gi_M6_two_copies r \<notin> gi_M6_pure_images pp_e_exact_operator_stock (gi_M6_left_copy r) \<and>
    (\<forall>i. pp_view i (gi_M6_left_copy r) \<subseteq> pp_view i (gi_M6_two_copies r))"
proof -
  have left_fp: "pp_e_exact_fun_prime (gi_M6_left_copy r)"
    by (rule gi_exact_M6_fun_prime_preimage[where i="[0]"]; simp only: gi_M6_copy_views; rule fp)
  have right_fp: "pp_e_exact_fun_prime (gi_M6_two_copies r)"
    by (rule gi_exact_M6_fun_prime_preimage[where i="[0]"]; simp only: gi_M6_copy_views; rule fp)
  have nonempty: "r \<noteq> {}" and nonuniversal: "r \<noteq> UNIV"
    by (rule gi_exact_M6_fun_prime_not_extreme[OF fp])+
  have subset: "gi_M6_left_copy r \<subseteq> gi_M6_two_copies r"
    unfolding gi_M6_left_copy_def gi_M6_two_copies_def by blast
  have proper: "gi_M6_left_copy r \<subset> gi_M6_two_copies r"
  proof -
    obtain w where member: "w \<in> r" using nonempty by blast
    have right: "w @ [1] \<in> gi_M6_two_copies r"
      unfolding gi_M6_two_copies_def pp_lift_def using member by blast
    have left: "w @ [1] \<notin> gi_M6_left_copy r"
      by (auto simp: gi_M6_left_copy_def pp_lift_def append_singleton_eq_iff)
    show ?thesis using subset right left by blast
  qed
  have outside: "gi_M6_two_copies r \<notin> gi_M6_pure_images pp_e_exact_operator_stock (gi_M6_left_copy r)"
  proof
    assume member: "gi_M6_two_copies r \<in> gi_M6_pure_images pp_e_exact_operator_stock (gi_M6_left_copy r)"
    then obtain F where fs: "F \<in> pp_e_exact_operator_stock"
      and image_value: "gi_M6_two_copies r = F (gi_M6_left_copy r)"
      unfolding gi_M6_pure_images_def by blast
    have equivariant: "pp_equivariant_operator F" by (rule pp_e_exact_operator_stock_equivariant[OF fs])
    have commutes: "pp_view [1] (F (gi_M6_left_copy r)) = F (pp_view [1] (gi_M6_left_copy r))"
      using equivariant unfolding pp_equivariant_operator_def by blast
    have extreme: "F {} = {} \<or> F {} = UNIV" by (rule gi_exact_M6_pure_empty_extreme[OF fs])
    have "r = F {}" using image_value commutes by (metis gi_M6_copy_views(2,4))
    then show False using extreme nonempty nonuniversal by blast
  qed
  have preserved: "\<forall>i. pp_view i (gi_M6_left_copy r) \<subseteq> pp_view i (gi_M6_two_copies r)"
    by (intro allI; rule gi_M6_views_preserve_inclusion[OF subset])
  show ?thesis using left_fp right_fp proper outside preserved by blast
qed

corollary gi_exact_M6_strict_pair_exists:
  "\<exists>p q. pp_e_exact_fun_prime p \<and> pp_e_exact_fun_prime q \<and> p \<subset> q \<and>
    q \<notin> gi_M6_pure_reversible_orbit pp_e_exact_operator_stock p \<and>
    (\<forall>i. pp_view i p \<subseteq> pp_view i q)"
proof -
  obtain r where fp: "pp_e_exact_fun_prime r" using pp_e_exact_fun_prime_exists by blast
  show ?thesis using gi_exact_M6_fun_prime_strict_pair[OF fp]
    gi_M6_reversible_orbit_subset_images[where S=pp_e_exact_operator_stock and p="gi_M6_left_copy r"]
    by blast
qed

corollary gi_native_M6_strict_pair_exists:
  assumes rich: "sg_rich G"
  shows "\<exists>p q. gi_stock_fun_prime (gi_exact_native_operator_stock G) p \<and>
    gi_stock_fun_prime (gi_exact_native_operator_stock G) q \<and> p \<subset> q \<and>
    q \<notin> gi_M6_pure_reversible_orbit (gi_exact_native_operator_stock G) p \<and>
    (\<forall>i. pp_view i p \<subseteq> pp_view i q)"
  using gi_exact_M6_strict_pair_exists
  by (simp only: gi_exact_native_operator_stock_eq[OF rich] gi_stock_fun_prime_def
    pp_e_exact_fun_prime_def pp_stock_fun_prime_def)

lemma gi_M6_joint_assignment_blocked_by_inclusion:
  assumes relation: "\<forall>i. pp_view i p \<subseteq> pp_view i q" and target_breaks: "\<not> A \<subseteq> B"
  shows "\<not> (\<exists>i. pp_view i p = A \<and> pp_view i q = B)"
  using relation target_breaks by blast

corollary gi_exact_M6_joint_assignment_counterexample:
  "\<exists>p q. pp_e_exact_fun_prime p \<and> pp_e_exact_fun_prime q \<and>
    q \<notin> gi_M6_pure_reversible_orbit pp_e_exact_operator_stock p \<and>
    \<not> (\<exists>i. pp_view i p = UNIV \<and> pp_view i q = {})"
proof -
  obtain p q where fp: "pp_e_exact_fun_prime p" and fq: "pp_e_exact_fun_prime q"
    and separate: "q \<notin> gi_M6_pure_reversible_orbit pp_e_exact_operator_stock p"
    and relation: "\<forall>i. pp_view i p \<subseteq> pp_view i q"
    using gi_exact_M6_strict_pair_exists by blast
  have target: "\<not> (UNIV :: pp_word set) \<subseteq> {}" by simp
  have blocked: "\<not> (\<exists>i. pp_view i p = UNIV \<and> pp_view i q = {})"
    by (rule gi_M6_joint_assignment_blocked_by_inclusion[OF relation target])
  show ?thesis using fp fq separate blocked by blast
qed

text \<open>
  The actual exact stock now supplies both parts of M6 without a fixed-r
  necessitated-QSS assumption. Its fun′ propositions separate substitutions,
  but need not vary independently. The strict pair is outside even the full
  pure-operator image, hence outside the pure-invertible orbit. Inclusion
  prevents the displayed joint target assignment. The single-coordinate
  diagonal has an unrestricted target, as in the historical statement.

  These are metatheorems about the fixed complete exact logical stock, with
  its native denotational counterpart identified. They are not PP models,
  results for arbitrary stock enlargements, or identifications of the
  separately glued fundamental proposition. HOL–ZF foundations remain.
\<close>

end
