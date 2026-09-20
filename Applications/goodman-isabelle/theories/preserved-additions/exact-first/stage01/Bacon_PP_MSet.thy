theory Bacon_PP_MSet
  imports 
    "Goodman_Exact_Legacy_01.Bacon_PP_Generic_Witness"
begin

section \<open>Bacon's function-space action at the propositional unary type\<close>

text \<open>
  Bacon's Definition 7.2 does not take every set-theoretic function from
  propositions to propositions.  It takes exactly those functions that respect
  identifications made by each substitution.  The action on such a function is
  then computed by choosing a preimage of its argument under the substitution.

  For the finite-word action, \<open>pp_lift i P\<close> is a canonical preimage of
  \<open>P\<close> under \<open>pp_view i\<close>.  The following definitions therefore give a
  choice-free presentation of Bacon's function-space domain and action at type
  \<open>Prop \<rightarrow> Prop\<close>.
\<close>

definition pp_function_space_member ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> bool" where
  "pp_function_space_member F \<longleftrightarrow>
    (\<forall>i P Q. pp_view i P = pp_view i Q \<longrightarrow>
      pp_view i (F P) = pp_view i (F Q))"

definition pp_fun_view ::
    "pp_word \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_fun_view i F =
    (\<lambda>P. pp_view i (F (pp_lift i P)))"

lemma pp_lift_root[simp]:
  "pp_lift [] P = P"
  by (auto simp: pp_lift_def)

lemma pp_lift_compose:
  "pp_lift j (pp_lift i P) = pp_lift (i @ j) P"
  by (auto simp: pp_lift_def append_assoc)

lemma pp_fun_view_apply:
  "pp_fun_view i F P = pp_view i (F (pp_lift i P))"
  by (simp add: pp_fun_view_def)

lemma pp_fun_view_preimage_independent:
  assumes member: "pp_function_space_member F"
    and preimage: "pp_view i Q = P"
  shows "pp_fun_view i F P = pp_view i (F Q)"
proof -
  have same_view:
      "pp_view i (pp_lift i P) = pp_view i Q"
    using preimage by simp
  have "pp_view i (F (pp_lift i P)) = pp_view i (F Q)"
    using member same_view
    unfolding pp_function_space_member_def by blast
  then show ?thesis
    by (simp add: pp_fun_view_apply)
qed

lemma pp_fun_view_root[simp]:
  "pp_fun_view [] F = F"
  by (rule ext) (simp add: pp_fun_view_apply)

lemma pp_fun_view_compose:
  "pp_fun_view i (pp_fun_view j F) =
    pp_fun_view (i @ j) F"
proof (rule ext)
  fix P
  show "pp_fun_view i (pp_fun_view j F) P =
      pp_fun_view (i @ j) F P"
    by (simp add: pp_fun_view_apply pp_view_compose pp_lift_compose)
qed

lemma pp_fun_view_member:
  assumes member: "pp_function_space_member F"
  shows "pp_function_space_member (pp_fun_view i F)"
proof (unfold pp_function_space_member_def, intro allI impI)
  fix j P Q
  assume views: "pp_view j P = pp_view j Q"
  have lifted_views:
      "pp_view (j @ i) (pp_lift i P) =
       pp_view (j @ i) (pp_lift i Q)"
  proof -
    have "pp_view (j @ i) (pp_lift i P) = pp_view j P"
      by (auto simp: pp_view_def pp_lift_def append_assoc)
    moreover have "pp_view (j @ i) (pp_lift i Q) = pp_view j Q"
      by (auto simp: pp_view_def pp_lift_def append_assoc)
    ultimately show ?thesis
      using views by simp
  qed
  have
      "pp_view (j @ i) (F (pp_lift i P)) =
       pp_view (j @ i) (F (pp_lift i Q))"
    using member lifted_views
    unfolding pp_function_space_member_def by blast
  then show
      "pp_view j (pp_fun_view i F P) =
       pp_view j (pp_fun_view i F Q)"
    by (simp add: pp_fun_view_apply pp_view_compose)
qed

subsection \<open>Surjectivity of Bacon's unary function-space action\<close>

text \<open>
  Proposition 8 of Bacon's appendix says that the function-space action is
  itself surjective.  At the word model there is a canonical preimage: move
  the argument down to its \<open>i\<close>-view, apply the target function, and lift the
  resulting proposition back into the cone determined by \<open>i\<close>.  The
  nontrivial obligation is that this preimage still belongs to Bacon's
  restricted function space.  The following three cone calculations discharge
  that obligation without appealing to an unrestricted function space.
\<close>

definition pp_fun_lift ::
    "pp_word \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      (pp_sem_prop \<Rightarrow> pp_sem_prop)" where
  "pp_fun_lift i F = (\<lambda>P. pp_lift i (F (pp_view i P)))"

lemma pp_view_lift_longer_suffix:
  "pp_view (k @ i) (pp_lift i P) = pp_view k P"
  by (auto simp: pp_view_def pp_lift_def append_assoc)

lemma pp_view_lift_shorter_suffix:
  "pp_view j (pp_lift (k @ j) P) = pp_lift k P"
  by (auto simp: pp_view_def pp_lift_def append_assoc)

lemma pp_view_lift_incomparable_suffixes:
  assumes not_ji: "\<nexists>k. j = k @ i"
    and not_ij: "\<nexists>k. i = k @ j"
  shows "pp_view j (pp_lift i P) = {}"
proof (rule set_eqI)
  fix x
  show "x \<in> pp_view j (pp_lift i P) \<longleftrightarrow> x \<in> {}"
  proof
    assume "x \<in> pp_view j (pp_lift i P)"
    then obtain y where y: "y \<in> P" and equation: "x @ j = y @ i"
      by (auto simp: pp_view_def pp_lift_def)
    have "(\<exists>k. j = k @ i) \<or> (\<exists>k. i = k @ j)"
      using equation
      by (metis append_eq_append_conv2)
    then show "x \<in> {}"
      using not_ji not_ij by blast
  next
    assume "x \<in> {}"
    then show "x \<in> pp_view j (pp_lift i P)" by simp
  qed
qed

theorem pp_fun_lift_member:
  assumes member: "pp_function_space_member F"
  shows "pp_function_space_member (pp_fun_lift i F)"
proof (unfold pp_function_space_member_def, intro allI impI)
  fix j P Q
  assume views: "pp_view j P = pp_view j Q"
  show "pp_view j (pp_fun_lift i F P) =
      pp_view j (pp_fun_lift i F Q)"
  proof (cases "\<exists>k. j = k @ i")
    case True
    then obtain k where j: "j = k @ i" by blast
    have input_views:
        "pp_view k (pp_view i P) = pp_view k (pp_view i Q)"
      using views j by (simp add: pp_view_compose)
    have output_views:
        "pp_view k (F (pp_view i P)) =
         pp_view k (F (pp_view i Q))"
      using member input_views
      unfolding pp_function_space_member_def by blast
    show ?thesis
      using output_views j
      by (simp add: pp_fun_lift_def pp_view_lift_longer_suffix)
  next
    case not_ji: False
    show ?thesis
    proof (cases "\<exists>k. i = k @ j")
      case True
      then obtain k where i: "i = k @ j" by blast
      have input_equal: "pp_view i P = pp_view i Q"
        using views i by (metis pp_view_compose)
      show ?thesis
        using input_equal i
        by (simp add: pp_fun_lift_def pp_view_lift_shorter_suffix)
    next
      case not_ij: False
      have left: "pp_view j (pp_lift i (F (pp_view i P))) = {}"
        using not_ji not_ij
        by (rule pp_view_lift_incomparable_suffixes)
      have right: "pp_view j (pp_lift i (F (pp_view i Q))) = {}"
        using not_ji not_ij
        by (rule pp_view_lift_incomparable_suffixes)
      show ?thesis
        using left right by (simp add: pp_fun_lift_def)
    qed
  qed
qed

lemma pp_fun_view_fun_lift[simp]:
  "pp_fun_view i (pp_fun_lift i F) = F"
proof (rule ext)
  fix P
  have "pp_fun_view i (pp_fun_lift i F) P =
      pp_view i (pp_lift i (F (pp_view i (pp_lift i P))))"
    by (simp add: pp_fun_view_apply pp_fun_lift_def)
  also have "... = F P"
    by simp
  finally show "pp_fun_view i (pp_fun_lift i F) P = F P" .
qed

theorem pp_fun_view_surjective_on_function_space:
  assumes member: "pp_function_space_member F"
  shows "\<exists>G. pp_function_space_member G \<and>
    pp_fun_view i G = F"
  using pp_fun_lift_member[OF member, of i]
  by (intro exI[of _ "pp_fun_lift i F"]) simp

definition pp_fun_invariant ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> bool" where
  "pp_fun_invariant F \<longleftrightarrow>
    (\<forall>i. pp_fun_view i F = F)"

lemma pp_equivariant_operator_member:
  assumes equivariant: "pp_equivariant_operator F"
  shows "pp_function_space_member F"
proof (unfold pp_function_space_member_def, intro allI impI)
  fix i P Q
  assume same_view: "pp_view i P = pp_view i Q"
  have "pp_view i (F P) = F (pp_view i P)"
    using equivariant unfolding pp_equivariant_operator_def by blast
  also have "... = F (pp_view i Q)"
    using same_view by simp
  also have "... = pp_view i (F Q)"
    using equivariant unfolding pp_equivariant_operator_def by blast
  finally show "pp_view i (F P) = pp_view i (F Q)" .
qed

theorem pp_fun_invariant_iff_equivariant:
  assumes member: "pp_function_space_member F"
  shows "pp_fun_invariant F \<longleftrightarrow>
    pp_equivariant_operator F"
proof
  assume invariant: "pp_fun_invariant F"
  show "pp_equivariant_operator F"
  proof (unfold pp_equivariant_operator_def, intro allI)
    fix i P
    have action:
        "pp_fun_view i F (pp_view i P) = pp_view i (F P)"
      using member
      by (rule pp_fun_view_preimage_independent) simp
    have "pp_fun_view i F = F"
      using invariant unfolding pp_fun_invariant_def by blast
    then show "pp_view i (F P) = F (pp_view i P)"
      using action by simp
  qed
next
  assume equivariant: "pp_equivariant_operator F"
  show "pp_fun_invariant F"
  proof (unfold pp_fun_invariant_def, intro allI)
    fix i
    show "pp_fun_view i F = F"
    proof (rule ext)
      fix P
      have "pp_fun_view i F P =
          pp_view i (F (pp_lift i P))"
        by (simp add: pp_fun_view_apply)
      also have "... = F (pp_view i (pp_lift i P))"
        using equivariant
        unfolding pp_equivariant_operator_def by blast
      also have "... = F P"
        by simp
      finally show "pp_fun_view i F P = F P" .
    qed
  qed
qed

corollary pp_equivariant_operator_invariant:
  assumes "pp_equivariant_operator F"
  shows "pp_fun_invariant F"
  using pp_fun_invariant_iff_equivariant[
      OF pp_equivariant_operator_member[OF assms]]
    assms by blast

subsection \<open>Invariant unary operations are exactly classifiers\<close>

definition pp_operator_index ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop set" where
  "pp_operator_index F =
    {P. pp_root_true (F P)}"

theorem pp_equivariant_operator_is_classifier:
  assumes equivariant: "pp_equivariant_operator F"
  shows "F = pp_classifier (pp_operator_index F)"
proof (rule ext, rule set_eqI)
  fix P i
  have action:
      "pp_view i (F P) = F (pp_view i P)"
    using equivariant unfolding pp_equivariant_operator_def by blast
  have "i \<in> F P \<longleftrightarrow>
      pp_root_true (pp_view i (F P))"
    by (simp add: pp_root_true_def pp_view_membership_at_root)
  also have "... \<longleftrightarrow>
      pp_root_true (F (pp_view i P))"
    using action by simp
  also have "... \<longleftrightarrow>
      pp_view i P \<in> pp_operator_index F"
    by (simp add: pp_operator_index_def)
  also have "... \<longleftrightarrow>
      i \<in> pp_classifier (pp_operator_index F) P"
    by (simp add: pp_classifier_def)
  finally show
      "i \<in> F P \<longleftrightarrow>
       i \<in> pp_classifier (pp_operator_index F) P" .
qed

lemma pp_classifier_index[simp]:
  "pp_operator_index (pp_classifier S) = S"
  by (auto simp: pp_operator_index_def)

theorem pp_fun_invariant_is_classifier:
  assumes member: "pp_function_space_member F"
    and invariant: "pp_fun_invariant F"
  shows "F = pp_classifier (pp_operator_index F)"
  using pp_equivariant_operator_is_classifier
    pp_fun_invariant_iff_equivariant[OF member] invariant
  by blast

theorem pp_classifier_is_function_space_invariant:
  "pp_function_space_member (pp_classifier S) \<and>
   pp_fun_invariant (pp_classifier S)"
  using pp_classifier_equivariant_operator
    pp_equivariant_operator_member
    pp_equivariant_operator_invariant
  by blast

subsection \<open>QLN stated directly for Bacon function-space elements\<close>

definition pp_root_unary_QLN_operator ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> pp_sem_prop \<Rightarrow> bool" where
  "pp_root_unary_QLN_operator F R \<longleftrightarrow>
    (pp_root_true (pp_sem_box (F R)) =
      (\<forall>P. pp_root_true (F P)))"

lemma pp_root_unary_QLN_operator_classifier:
  "pp_root_unary_QLN_operator (pp_classifier S) R =
    pp_root_unary_QLN S R"
  by (simp add: pp_root_unary_QLN_operator_def pp_root_unary_QLN_def)

theorem pp_invariant_operator_QLN_iff_orbit_escape:
  assumes member: "pp_function_space_member F"
    and invariant: "pp_fun_invariant F"
  shows "pp_root_unary_QLN_operator F R \<longleftrightarrow>
    ((pp_orbit R \<subseteq> pp_operator_index F) =
      (pp_operator_index F = UNIV))"
proof -
  have representation:
      "F = pp_classifier (pp_operator_index F)"
    using member invariant by (rule pp_fun_invariant_is_classifier)
  have classifier_QLN:
      "pp_root_unary_QLN
        (pp_operator_index F) R \<longleftrightarrow>
       ((pp_orbit R \<subseteq> pp_operator_index F) =
        (pp_operator_index F = UNIV))"
    by (rule pp_root_unary_QLN_iff)
  have operator_QLN:
      "pp_root_unary_QLN_operator F R =
       pp_root_unary_QLN (pp_operator_index F) R"
  proof -
    have "pp_root_unary_QLN_operator F R =
        pp_root_unary_QLN_operator
          (pp_classifier (pp_operator_index F)) R"
      using representation by (rule arg_cong)
    also have "... =
        pp_root_unary_QLN (pp_operator_index F) R"
      by (rule pp_root_unary_QLN_operator_classifier)
    finally show ?thesis .
  qed
  show ?thesis
    using classifier_QLN operator_QLN by blast
qed

corollary pp_invariant_operator_recombination_iff_orbit_escape:
  "pp_root_unary_recombination
      (pp_operator_index F) R \<longleftrightarrow>
    (pp_operator_index F = UNIV \<or>
      \<not> pp_orbit R \<subseteq> pp_operator_index F)"
  using pp_root_unary_recombination_iff[
      of "pp_operator_index F" R]
  by blast

theorem pp_countable_invariant_function_stock_has_QLN_witness:
  fixes Stock ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) set"
  assumes countable: "countable Stock"
    and member:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_function_space_member F"
    and invariant:
      "\<And>F. F \<in> Stock \<Longrightarrow> pp_fun_invariant F"
  shows "\<exists>R. \<forall>F \<in> Stock.
    pp_root_unary_QLN_operator F R"
proof -
  let ?Indices = "pp_operator_index ` Stock"
  have indices_countable: "countable ?Indices"
    using countable by (rule countable_image)
  obtain R where index_QLN:
      "\<forall>S \<in> ?Indices. pp_root_unary_QLN S R"
    using pp_countable_stock_has_generic_QLN_witness[
        OF indices_countable]
    by blast
  show ?thesis
  proof (intro exI[of _ R] ballI)
    fix F
    assume F_stock: "F \<in> Stock"
    have qln:
        "pp_root_unary_QLN (pp_operator_index F) R"
      using index_QLN F_stock by blast
    have orbit_condition:
        "(pp_orbit R \<subseteq> pp_operator_index F) =
         (pp_operator_index F = UNIV)"
      using qln by (simp add: pp_root_unary_QLN_iff)
    show "pp_root_unary_QLN_operator F R"
      using pp_invariant_operator_QLN_iff_orbit_escape[
          OF member[OF F_stock] invariant[OF F_stock],
          of R]
        orbit_condition
      by blast
  qed
qed

text \<open>
  Hence the classifier representation used in the generic-witness development
  is not an additional semantic assumption.  It is the exact representation of
  the invariant elements of Bacon's function-space M-set at type
  \<open>Prop \<rightarrow> Prop\<close>.  The last theorem also transfers the generic-witness
  orbit criterion directly to those function-space elements.
\<close>

end
