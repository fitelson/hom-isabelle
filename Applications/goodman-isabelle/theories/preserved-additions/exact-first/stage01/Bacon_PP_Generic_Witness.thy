theory Bacon_PP_Generic_Witness
  imports 
    "Goodman_Legacy_01.Bacon_PP_Diagonal"
    "HOL-Library.Countable_Set"
begin

section \<open>A generic witness for the Bacon word action\<close>

text \<open>
  This theory isolates the semantic core needed for the consistency question.
  It does not import the quarantined action-model development.  Propositions
  are sets of finite words.  A world sees a proposition through right
  division, and an invariant unary classifier is determined by a set of
  propositional views.
\<close>

type_synonym pp_word = "nat list"
type_synonym pp_sem_prop = "pp_word set"

definition pp_view ::
    "pp_word \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_view i P = {j. j @ i \<in> P}"

definition pp_lift ::
    "pp_word \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_lift i P = {j @ i | j. j \<in> P}"

definition pp_orbit ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop set" where
  "pp_orbit R = range (\<lambda>i. pp_view i R)"

definition pp_classifier ::
    "pp_sem_prop set \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_classifier S P = {i. pp_view i P \<in> S}"

definition pp_sem_box ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_sem_box P = {i. pp_view i P = UNIV}"

definition pp_root_true :: "pp_sem_prop \<Rightarrow> bool" where
  "pp_root_true P \<longleftrightarrow> [] \<in> P"

definition pp_accessible :: "pp_word \<Rightarrow> pp_word \<Rightarrow> bool" where
  "pp_accessible i j \<longleftrightarrow> (\<exists>k. j = k @ i)"

lemma pp_view_root[simp]:
  "pp_view [] P = P"
  by (auto simp: pp_view_def)

lemma pp_view_compose:
  "pp_view i (pp_view j P) = pp_view (i @ j) P"
  by (auto simp: pp_view_def append_assoc)

lemma pp_view_lift[simp]:
  "pp_view i (pp_lift i P) = P"
  by (auto simp: pp_view_def pp_lift_def)

theorem pp_view_surjective:
  "surj (pp_view i)"
proof (rule surjI)
  fix P
  show "pp_view i (pp_lift i P) = P"
    by simp
qed

lemma pp_accessible_refl:
  "pp_accessible i i"
  unfolding pp_accessible_def
  by (intro exI[of _ "[]"]) simp

lemma pp_accessible_trans:
  assumes "pp_accessible i j"
    and "pp_accessible j k"
  shows "pp_accessible i k"
  using assms
  unfolding pp_accessible_def
  by (auto simp: append_assoc)

lemma pp_accessible_not_symmetric:
  "pp_accessible [] [0] \<and> \<not> pp_accessible [0] []"
  by (auto simp: pp_accessible_def)

lemma pp_sem_box_accessible_iff:
  "i \<in> pp_sem_box P \<longleftrightarrow>
    (\<forall>j. pp_accessible i j \<longrightarrow> j \<in> P)"
  by (auto simp: pp_sem_box_def pp_view_def pp_accessible_def)

lemma pp_sem_box_T:
  "pp_sem_box P \<subseteq> P"
proof
  fix i
  assume "i \<in> pp_sem_box P"
  then have "pp_view i P = UNIV"
    by (simp add: pp_sem_box_def)
  then have "[] \<in> pp_view i P"
    by simp
  then show "i \<in> P"
    by (simp add: pp_view_def)
qed

lemma pp_sem_box_4:
  "pp_sem_box P \<subseteq> pp_sem_box (pp_sem_box P)"
  unfolding subset_iff
  by (meson pp_accessible_trans pp_sem_box_accessible_iff)

lemma pp_sem_box_equivariant:
  "pp_view i (pp_sem_box P) =
    pp_sem_box (pp_view i P)"
  by (auto simp: pp_view_def pp_sem_box_def append_assoc)

lemma pp_classifier_equivariant:
  "pp_view i (pp_classifier S P) =
    pp_classifier S (pp_view i P)"
  by (auto simp: pp_view_def pp_classifier_def append_assoc)

definition pp_invariant_proposition :: "pp_sem_prop \<Rightarrow> bool" where
  "pp_invariant_proposition P \<longleftrightarrow> (\<forall>i. pp_view i P = P)"

definition pp_equivariant_operator ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> bool" where
  "pp_equivariant_operator F \<longleftrightarrow>
    (\<forall>i P. pp_view i (F P) = F (pp_view i P))"

lemma pp_classifier_equivariant_operator:
  "pp_equivariant_operator (pp_classifier S)"
  unfolding pp_equivariant_operator_def
  by (rule allI)+ (rule pp_classifier_equivariant)

lemma pp_view_membership_at_root:
  "[] \<in> pp_view i P \<longleftrightarrow> i \<in> P"
  by (simp add: pp_view_def)

theorem pp_invariant_proposition_iff_extreme:
  "pp_invariant_proposition P \<longleftrightarrow> P = {} \<or> P = UNIV"
proof
  assume invariant: "pp_invariant_proposition P"
  have membership_constant: "i \<in> P \<longleftrightarrow> [] \<in> P" for i
  proof -
    have "pp_view i P = P"
      using invariant
      unfolding pp_invariant_proposition_def by blast
    then show ?thesis
      using pp_view_membership_at_root[of i P] by simp
  qed
  show "P = {} \<or> P = UNIV"
  proof (cases "[] \<in> P")
    case True
    then have "\<forall>i. i \<in> P"
      using membership_constant by blast
    then show ?thesis
      by auto
  next
    case False
    then have "\<forall>i. i \<notin> P"
      using membership_constant by blast
    then show ?thesis
      by auto
  qed
next
  assume "P = {} \<or> P = UNIV"
  then show "pp_invariant_proposition P"
    by (auto simp: pp_invariant_proposition_def pp_view_def)
qed

lemma pp_classifier_root[simp]:
  "pp_root_true (pp_classifier S P) \<longleftrightarrow> P \<in> S"
  by (simp add: pp_root_true_def pp_classifier_def)

lemma pp_classifier_injective:
  "inj pp_classifier"
proof (rule injI)
  fix S T
  assume classifiers:
    "pp_classifier S = pp_classifier T"
  show "S = T"
  proof
    show "S \<subseteq> T"
    proof
      fix P
      assume "P \<in> S"
      then have "pp_root_true (pp_classifier S P)"
        by simp
      then have "pp_root_true (pp_classifier T P)"
        using classifiers by simp
      then show "P \<in> T"
        by simp
    qed
  next
    show "T \<subseteq> S"
    proof
      fix P
      assume "P \<in> T"
      then have "pp_root_true (pp_classifier T P)"
        by simp
      then have "pp_root_true (pp_classifier S P)"
        using classifiers by simp
      then show "P \<in> S"
        by simp
    qed
  qed
qed

subsection \<open>The QLN collapse\<close>

definition pp_root_unary_recombination ::
    "pp_sem_prop set \<Rightarrow> pp_sem_prop \<Rightarrow> bool" where
  "pp_root_unary_recombination S R \<longleftrightarrow>
    (pp_root_true (pp_sem_box (pp_classifier S R)) \<longrightarrow>
      (\<forall>P. pp_root_true (pp_classifier S P)))"

definition pp_root_unary_exhaustion ::
    "pp_sem_prop set \<Rightarrow> pp_sem_prop \<Rightarrow> bool" where
  "pp_root_unary_exhaustion S R \<longleftrightarrow>
    ((\<forall>P. pp_root_true (pp_classifier S P)) \<longrightarrow>
      pp_root_true (pp_sem_box (pp_classifier S R)))"

definition pp_root_unary_QLN ::
    "pp_sem_prop set \<Rightarrow> pp_sem_prop \<Rightarrow> bool" where
  "pp_root_unary_QLN S R \<longleftrightarrow>
    (pp_root_true (pp_sem_box (pp_classifier S R)) =
      (\<forall>P. pp_root_true (pp_classifier S P)))"

lemma pp_box_classifier_root_iff:
  "pp_root_true (pp_sem_box (pp_classifier S R)) \<longleftrightarrow>
    pp_orbit R \<subseteq> S"
proof -
  have "pp_root_true (pp_sem_box (pp_classifier S R)) \<longleftrightarrow>
      pp_classifier S R = UNIV"
    by (simp add: pp_root_true_def pp_sem_box_def)
  also have "... \<longleftrightarrow> (\<forall>i. pp_view i R \<in> S)"
    by (auto simp: pp_classifier_def)
  also have "... \<longleftrightarrow> pp_orbit R \<subseteq> S"
    by (auto simp: pp_orbit_def)
  finally show ?thesis .
qed

lemma pp_classifier_universal_root_iff:
  "(\<forall>P. pp_root_true (pp_classifier S P)) \<longleftrightarrow>
    S = UNIV"
  by auto

lemma pp_all_sem_props_mem_iff[simp]:
  "(\<forall>P :: pp_sem_prop. P \<in> S) \<longleftrightarrow> S = UNIV"
  by blast

theorem pp_root_unary_recombination_iff:
  "pp_root_unary_recombination S R \<longleftrightarrow>
    (pp_orbit R \<subseteq> S \<longrightarrow> S = UNIV)"
  unfolding pp_root_unary_recombination_def
  by (simp add: pp_box_classifier_root_iff
      pp_classifier_universal_root_iff)

theorem pp_root_unary_exhaustion:
  "pp_root_unary_exhaustion S R"
  unfolding pp_root_unary_exhaustion_def
  by (simp add: pp_box_classifier_root_iff
      pp_classifier_universal_root_iff)

theorem pp_root_unary_QLN_iff:
  "pp_root_unary_QLN S R \<longleftrightarrow>
    ((pp_orbit R \<subseteq> S) = (S = UNIV))"
  unfolding pp_root_unary_QLN_def
  by (simp add: pp_box_classifier_root_iff
      pp_classifier_universal_root_iff)

subsection \<open>World-relative equality and the shifting witness\<close>

definition pp_equal_at ::
    "pp_word \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> bool" where
  "pp_equal_at i P Q \<longleftrightarrow> pp_view i P = pp_view i Q"

definition pp_fundamental_at ::
    "pp_word \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> bool" where
  "pp_fundamental_at i r P \<longleftrightarrow> pp_view i P = r"

definition pp_fundamental_classifier ::
    "pp_sem_prop \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_fundamental_classifier r = pp_classifier {r}"

definition pp_world_witness ::
    "pp_word \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_world_witness i r = pp_lift i r"

lemma pp_world_witness_fundamental:
  "pp_fundamental_at i r (pp_world_witness i r)"
  by (simp add: pp_fundamental_at_def pp_world_witness_def)

lemma pp_fundamental_classifier_at_world:
  "i \<in> pp_fundamental_classifier r P \<longleftrightarrow>
    pp_fundamental_at i r P"
  by (simp add: pp_fundamental_classifier_def pp_classifier_def
      pp_fundamental_at_def)

theorem pp_fundamental_exists_at_every_world:
  "\<exists>P. pp_fundamental_at i r P"
  using pp_world_witness_fundamental by blast

theorem pp_fundamental_unique_up_to_local_equality:
  assumes "pp_fundamental_at i r P"
    and "pp_fundamental_at i r Q"
  shows "pp_equal_at i P Q"
  using assms
  by (simp add: pp_fundamental_at_def pp_equal_at_def)

lemma pp_classifier_UNIV_iff:
  "pp_classifier S R = UNIV \<longleftrightarrow> pp_orbit R \<subseteq> S"
  by (auto simp: pp_classifier_def pp_orbit_def)

lemma pp_all_views_mem_iff:
  "(\<forall>P. pp_view i P \<in> S) \<longleftrightarrow> S = UNIV"
proof
  assume all_views: "\<forall>P. pp_view i P \<in> S"
  show "S = UNIV"
  proof
    show "S \<subseteq> UNIV"
      by simp
  next
    show "UNIV \<subseteq> S"
    proof
      fix Q :: pp_sem_prop
      assume "Q \<in> UNIV"
      have "pp_view i (pp_lift i Q) \<in> S"
        by (rule all_views[rule_format])
      then show "Q \<in> S"
        by simp
    qed
  qed
next
  assume "S = UNIV"
  then show "\<forall>P. pp_view i P \<in> S"
    by simp
qed

definition pp_guarded_unary_QLN_at_world ::
    "pp_word \<Rightarrow> pp_sem_prop \<Rightarrow>
      pp_sem_prop set \<Rightarrow> bool" where
  "pp_guarded_unary_QLN_at_world i r S \<longleftrightarrow>
    (\<forall>P.
      pp_fundamental_at i r P \<longrightarrow>
      ((i \<in> pp_sem_box (pp_classifier S P)) =
        (\<forall>Q. i \<in> pp_classifier S Q)))"

theorem pp_guarded_unary_QLN_at_world_iff:
  "pp_guarded_unary_QLN_at_world i r S \<longleftrightarrow>
    pp_root_unary_QLN S r"
proof -
  have box_at:
    "i \<in> pp_sem_box (pp_classifier S P) \<longleftrightarrow>
      pp_orbit (pp_view i P) \<subseteq> S" for P
    by (simp add: pp_sem_box_def pp_classifier_equivariant
        pp_classifier_UNIV_iff)
  have universal_at:
    "(\<forall>Q. i \<in> pp_classifier S Q) \<longleftrightarrow> S = UNIV"
    by (simp add: pp_classifier_def pp_all_views_mem_iff)
  have guarded_condition:
    "(\<forall>P.
        pp_view i P = r \<longrightarrow>
        ((i \<in> pp_sem_box (pp_classifier S P)) =
          (\<forall>Q. i \<in> pp_classifier S Q))) \<longleftrightarrow>
      ((pp_orbit r \<subseteq> S) = (S = UNIV))"
  proof
    assume guarded:
      "\<forall>P.
        pp_view i P = r \<longrightarrow>
        ((i \<in> pp_sem_box (pp_classifier S P)) =
          (\<forall>Q. i \<in> pp_classifier S Q))"
    let ?P = "pp_world_witness i r"
    have view: "pp_view i ?P = r"
      by (simp add: pp_world_witness_def)
    have equality:
      "(i \<in> pp_sem_box (pp_classifier S ?P)) =
        (\<forall>Q. i \<in> pp_classifier S Q)"
      using guarded view by blast
    show "(pp_orbit r \<subseteq> S) = (S = UNIV)"
      using equality box_at[of ?P] universal_at view by simp
  next
    assume condition:
      "(pp_orbit r \<subseteq> S) = (S = UNIV)"
    show "\<forall>P.
        pp_view i P = r \<longrightarrow>
        ((i \<in> pp_sem_box (pp_classifier S P)) =
          (\<forall>Q. i \<in> pp_classifier S Q))"
    proof (intro allI impI)
      fix P
      assume view: "pp_view i P = r"
      show "(i \<in> pp_sem_box (pp_classifier S P)) =
          (\<forall>Q. i \<in> pp_classifier S Q)"
        using condition box_at[of P] universal_at view by simp
    qed
  qed
  have root_condition:
    "pp_root_unary_QLN S r \<longleftrightarrow>
      ((pp_orbit r \<subseteq> S) = (S = UNIV))"
    by (rule pp_root_unary_QLN_iff)
  show ?thesis
    unfolding pp_guarded_unary_QLN_at_world_def
      pp_fundamental_at_def
    using guarded_condition root_condition by blast
qed

subsection \<open>Gluing independently chosen views\<close>

definition pp_glued_witness ::
    "(nat \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop" where
  "pp_glued_witness q = (\<Union>n. pp_lift [n] (q n))"

lemma append_singleton_eq_iff:
  "xs @ [m] = ys @ [n] \<longleftrightarrow> xs = ys \<and> m = n"
proof
  assume equality: "xs @ [m] = ys @ [n]"
  have last_equality:
    "last (xs @ [m]) = last (ys @ [n])"
    by (rule arg_cong[where f = last, OF equality])
  then have last: "m = n"
    by simp
  with equality have "xs = ys"
    by simp
  with last show "xs = ys \<and> m = n"
    by simp
next
  assume "xs = ys \<and> m = n"
  then show "xs @ [m] = ys @ [n]"
    by simp
qed

theorem pp_view_glued_witness[simp]:
  "pp_view [n] (pp_glued_witness q) = q n"
  by (auto simp: pp_view_def pp_glued_witness_def pp_lift_def
      append_singleton_eq_iff)

definition pp_outside_choice ::
    "(nat \<Rightarrow> pp_sem_prop set) \<Rightarrow> nat \<Rightarrow> pp_sem_prop" where
  "pp_outside_choice E n = (SOME P. P \<notin> E n)"

lemma pp_outside_choice_notin:
  assumes "E n \<noteq> UNIV"
  shows "pp_outside_choice E n \<notin> E n"
proof -
  have "\<exists>P. P \<notin> E n"
    using assms by blast
  then show ?thesis
    unfolding pp_outside_choice_def by (rule someI_ex)
qed

theorem pp_generic_witness_for_sequence:
  fixes E :: "nat \<Rightarrow> pp_sem_prop set"
  assumes proper: "\<And>n. E n \<noteq> UNIV"
  shows "\<exists>R. \<forall>n. \<not> pp_orbit R \<subseteq> E n"
proof -
  let ?q = "pp_outside_choice E"
  let ?R = "pp_glued_witness ?q"
  have outside: "?q n \<notin> E n" for n
    using proper by (rule pp_outside_choice_notin)
  have orbit: "?q n \<in> pp_orbit ?R" for n
    unfolding pp_orbit_def
    using pp_view_glued_witness[of n ?q]
    by (intro range_eqI[where x = "[n]"]) simp
  have generic: "\<not> pp_orbit ?R \<subseteq> E n" for n
    using orbit[of n] outside[of n] by blast
  show ?thesis
    using generic by blast
qed

theorem pp_generic_witness_for_countable_proper_stock:
  fixes Stock :: "pp_sem_prop set set"
  assumes countable: "countable Stock"
    and proper: "\<And>S. S \<in> Stock \<Longrightarrow> S \<noteq> UNIV"
  shows "\<exists>R. \<forall>S \<in> Stock. \<not> pp_orbit R \<subseteq> S"
proof (cases "Stock = {}")
  case True
  show ?thesis
    by (simp add: True)
next
  case False
  let ?E = "from_nat_into Stock"
  have E_range: "range ?E = Stock"
    using False countable by (rule range_from_nat_into)
  have E_mem: "?E n \<in> Stock" for n
    using E_range by blast
  have E_proper: "?E n \<noteq> UNIV" for n
    using E_mem by (rule proper)
  have exists_R:
    "\<exists>R. \<forall>n. \<not> pp_orbit R \<subseteq> ?E n"
  proof (rule pp_generic_witness_for_sequence)
    fix n
    show "?E n \<noteq> UNIV"
      by (rule E_proper)
  qed
  obtain R where generic:
    "\<forall>n. \<not> pp_orbit R \<subseteq> ?E n"
    using exists_R by blast
  show ?thesis
  proof (intro exI[of _ R] ballI)
    fix S
    assume S_mem: "S \<in> Stock"
    have "S \<in> range ?E"
      using S_mem E_range by simp
    then obtain n where "?E n = S"
      by auto
    then show "\<not> pp_orbit R \<subseteq> S"
      using generic by blast
  qed
qed

subsection \<open>A generic QLN witness for a countable stock\<close>

theorem pp_countable_stock_has_generic_QLN_witness:
  fixes Stock :: "pp_sem_prop set set"
  assumes "countable Stock"
  shows "\<exists>R. \<forall>S \<in> Stock. pp_root_unary_QLN S R"
proof -
  let ?Proper = "Stock - {UNIV}"
  have proper_countable: "countable ?Proper"
    using assms by (rule countable_subset[rotated]) auto
  have proper_member:
    "\<And>S. S \<in> ?Proper \<Longrightarrow> S \<noteq> UNIV"
    by simp
  obtain R where generic:
    "\<forall>S \<in> ?Proper. \<not> pp_orbit R \<subseteq> S"
    using proper_countable proper_member
      pp_generic_witness_for_countable_proper_stock
    by blast
  show ?thesis
  proof (intro exI[of _ R] ballI)
    fix S
    assume S_mem: "S \<in> Stock"
    show "pp_root_unary_QLN S R"
    proof (cases "S = UNIV")
      case True
      show ?thesis
        using True by (simp add: pp_root_unary_QLN_iff)
    next
      case False
      then have "S \<in> ?Proper"
        using S_mem by simp
      then have "\<not> pp_orbit R \<subseteq> S"
        using generic by blast
      with False show ?thesis
        by (simp add: pp_root_unary_QLN_iff)
    qed
  qed
qed

theorem pp_countable_stock_has_all_worlds_guarded_QLN_witness:
  fixes Stock :: "pp_sem_prop set set"
  assumes "countable Stock"
  shows "\<exists>r. \<forall>S \<in> Stock. \<forall>i.
    pp_guarded_unary_QLN_at_world i r S"
proof -
  obtain r where root_QLN:
    "\<forall>S \<in> Stock. pp_root_unary_QLN S r"
    using pp_countable_stock_has_generic_QLN_witness[OF assms]
    by blast
  show ?thesis
  proof (intro exI[of _ r] ballI allI)
    fix S i
    assume "S \<in> Stock"
    then have "pp_root_unary_QLN S r"
      using root_QLN by blast
    then show "pp_guarded_unary_QLN_at_world i r S"
      using pp_guarded_unary_QLN_at_world_iff by blast
  qed
qed

corollary pp_enumerated_stock_has_all_worlds_guarded_QLN_witness:
  fixes classifier_index :: "nat \<Rightarrow> pp_sem_prop set"
  shows "\<exists>r. \<forall>S \<in> range classifier_index. \<forall>i.
    pp_guarded_unary_QLN_at_world i r S"
  by (rule pp_countable_stock_has_all_worlds_guarded_QLN_witness)
    simp

theorem pp_countable_stock_shifting_witness_core:
  fixes Stock :: "pp_sem_prop set set"
  assumes "countable Stock"
  shows "\<exists>r.
    (\<forall>i. \<exists>P. pp_fundamental_at i r P) \<and>
    (\<forall>i P Q.
      pp_fundamental_at i r P \<longrightarrow>
      pp_fundamental_at i r Q \<longrightarrow>
      pp_equal_at i P Q) \<and>
    (\<forall>S \<in> Stock. \<forall>i.
      pp_guarded_unary_QLN_at_world i r S)"
proof -
  obtain r where guarded:
    "\<forall>S \<in> Stock. \<forall>i.
      pp_guarded_unary_QLN_at_world i r S"
    using pp_countable_stock_has_all_worlds_guarded_QLN_witness[
      OF assms]
    by blast
  show ?thesis
  proof (rule exI[of _ r], rule conjI)
    show "\<forall>i. \<exists>P. pp_fundamental_at i r P"
      using pp_fundamental_exists_at_every_world by blast
  next
    show "(\<forall>i P Q.
        pp_fundamental_at i r P \<longrightarrow>
        pp_fundamental_at i r Q \<longrightarrow>
        pp_equal_at i P Q) \<and>
      (\<forall>S \<in> Stock. \<forall>i.
        pp_guarded_unary_QLN_at_world i r S)"
    proof
      show "\<forall>i P Q.
          pp_fundamental_at i r P \<longrightarrow>
          pp_fundamental_at i r Q \<longrightarrow>
          pp_equal_at i P Q"
        using pp_fundamental_unique_up_to_local_equality by blast
    next
      show "\<forall>S \<in> Stock. \<forall>i.
          pp_guarded_unary_QLN_at_world i r S"
        by (rule guarded)
    qed
  qed
qed

definition pp_nonuniversal_views :: "pp_sem_prop set" where
  "pp_nonuniversal_views = UNIV - {UNIV}"

definition pp_nonempty_views :: "pp_sem_prop set" where
  "pp_nonempty_views = UNIV - {{}}"

lemma pp_nonuniversal_views_not_UNIV:
  "pp_nonuniversal_views \<noteq> UNIV"
  by (auto simp: pp_nonuniversal_views_def)

lemma pp_nonempty_views_not_UNIV:
  "pp_nonempty_views \<noteq> UNIV"
  by (auto simp: pp_nonempty_views_def)

lemma pp_QLN_nonuniversal_forces_universal_view:
  assumes "pp_root_unary_QLN pp_nonuniversal_views r"
  shows "UNIV \<in> pp_orbit r"
proof -
  have "\<not> pp_orbit r \<subseteq> pp_nonuniversal_views"
    using assms pp_nonuniversal_views_not_UNIV
    by (simp add: pp_root_unary_QLN_iff)
  then show ?thesis
    by (auto simp: pp_nonuniversal_views_def)
qed

lemma pp_QLN_nonempty_forces_empty_view:
  assumes "pp_root_unary_QLN pp_nonempty_views r"
  shows "{} \<in> pp_orbit r"
proof -
  have "\<not> pp_orbit r \<subseteq> pp_nonempty_views"
    using assms pp_nonempty_views_not_UNIV
    by (simp add: pp_root_unary_QLN_iff)
  then show ?thesis
    by (auto simp: pp_nonempty_views_def)
qed

corollary pp_generic_witness_has_extreme_views:
  fixes Stock :: "pp_sem_prop set set"
  assumes countable: "countable Stock"
    and nonuniversal: "pp_nonuniversal_views \<in> Stock"
    and nonempty: "pp_nonempty_views \<in> Stock"
  shows "\<exists>r.
    (\<forall>S \<in> Stock. pp_root_unary_QLN S r) \<and>
    UNIV \<in> pp_orbit r \<and>
    {} \<in> pp_orbit r"
proof -
  obtain r where qln:
    "\<forall>S \<in> Stock. pp_root_unary_QLN S r"
    using pp_countable_stock_has_generic_QLN_witness[OF countable]
    by blast
  have qln_nonuniversal:
    "pp_root_unary_QLN pp_nonuniversal_views r"
    using qln nonuniversal by blast
  have qln_nonempty:
    "pp_root_unary_QLN pp_nonempty_views r"
    using qln nonempty by blast
  have "UNIV \<in> pp_orbit r"
    using qln_nonuniversal
    by (rule pp_QLN_nonuniversal_forces_universal_view)
  moreover have "{} \<in> pp_orbit r"
    using qln_nonempty by (rule pp_QLN_nonempty_forces_empty_view)
  ultimately show ?thesis
    using qln by blast
qed

corollary pp_countable_stock_has_recombination_and_exhaustion_witness:
  fixes Stock :: "pp_sem_prop set set"
  assumes "countable Stock"
  shows "\<exists>R. \<forall>S \<in> Stock.
      pp_root_unary_recombination S R \<and>
      pp_root_unary_exhaustion S R"
proof -
  obtain R where qln:
    "\<forall>S \<in> Stock. pp_root_unary_QLN S R"
    using pp_countable_stock_has_generic_QLN_witness[OF assms]
    by blast
  show ?thesis
  proof (intro exI[of _ R] ballI)
    fix S
    assume "S \<in> Stock"
    then have "pp_root_unary_QLN S R"
      using qln by blast
    then show "pp_root_unary_recombination S R \<and>
        pp_root_unary_exhaustion S R"
      unfolding pp_root_unary_QLN_def
        pp_root_unary_recombination_def
        pp_root_unary_exhaustion_def
      by blast
  qed
qed

text \<open>
  The theorem above is the precise generic-witness result needed on the unary
  QLN side.  For every countable stock of invariant classifiers, one
  proposition has an orbit that escapes every proper classifier extension.
  Exhaustion is automatic, and Recombination follows.  The remaining
  consistency problem is therefore not witness rigidity; it is whether a pure
  stock satisfying the closure axioms can contain its own classifier.
\<close>

end
