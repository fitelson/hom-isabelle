theory Bacon_Finite_CEV_Model
  imports Bacon_Supported_Canonical
begin

section \<open>A finite full-function model of CEV\<close>

text \<open>
  Since the object language has only the two base types \<open>Ind\<close> and
  \<open>Prop\<close>, we can interpret every object type by a finite full function
  space.  A single Isabelle datatype carries the disjoint union of those
  spaces.  Function denotations are canonical finite tables.

  In standard notation, D_e = {*}, D_t = {0,1}, and D_(sigma -> tau) is the
  full function space from D_sigma to D_tau.  Each type domain is finite;
  there is no bound on type depth, and the carrier collecting all types is
  not asserted to be finite.  The table enumeration uses Hilbert choice
  (\<open>SOME\<close>), not an executable enumeration algorithm.  Arbitrary
  off-domain defaults do not affect the typed evaluation theorems.

  This is an extensional calibration model, analogous to a full Henkin
  model in Bacon--Dorr Section 3.2 (pp. 47--49).  The concrete interpretations
  \<open>Finite\<close> and \<open>FiniteCEV\<close> discharge the applicative and vector-equivalence
  locale assumptions.  They certify CEV's nonderivability of falsity and
  the applicability of the supported successor construction.  They do not
  establish BBK/action-model completeness or provide a non-extensional
  model of Classicism.
\<close>

datatype finite_den =
    FDInd
  | FDBool bool
  | FDTable "(finite_den \<times> finite_den) list"

definition finite_enum_set :: "'a set \<Rightarrow> 'a list" where
  "finite_enum_set S =
    (SOME xs. set xs = S \<and> distinct xs)"

lemma finite_enum_set_set:
  assumes "finite S"
  shows "set (finite_enum_set S) = S"
proof -
  obtain xs where "set xs = S" and "distinct xs"
    using finite_distinct_list[OF assms] by blast
  then have "\<exists>xs. set xs = S \<and> distinct xs"
    by blast
  then have "set (SOME xs. set xs = S \<and> distinct xs) = S \<and>
      distinct (SOME xs. set xs = S \<and> distinct xs)"
    by (rule someI_ex)
  then show ?thesis
    unfolding finite_enum_set_def by blast
qed

lemma finite_enum_set_distinct:
  assumes "finite S"
  shows "distinct (finite_enum_set S)"
proof -
  obtain xs where "set xs = S" and "distinct xs"
    using finite_distinct_list[OF assms] by blast
  then have "\<exists>xs. set xs = S \<and> distinct xs"
    by blast
  then have "set (SOME xs. set xs = S \<and> distinct xs) = S \<and>
      distinct (SOME xs. set xs = S \<and> distinct xs)"
    by (rule someI_ex)
  then show ?thesis
    unfolding finite_enum_set_def by blast
qed

fun finite_D :: "otype \<Rightarrow> finite_den set" where
  "finite_D Ind = {FDInd}"
| "finite_D Prop = {FDBool False, FDBool True}"
| "finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    {FDTable (map (\<lambda>x. (x, F x)) (finite_enum_set (finite_D \<sigma>))) |
      F. \<forall>x \<in> finite_D \<sigma>. F x \<in> finite_D \<tau>}"

definition finite_enum :: "otype \<Rightarrow> finite_den list" where
  "finite_enum \<sigma> = finite_enum_set (finite_D \<sigma>)"

definition finite_lam ::
    "otype \<Rightarrow> (finite_den \<Rightarrow> finite_den) \<Rightarrow> finite_den" where
  "finite_lam \<sigma> F =
    FDTable (map (\<lambda>x. (x, F x)) (finite_enum \<sigma>))"

fun finite_app :: "finite_den \<Rightarrow> finite_den \<Rightarrow> finite_den" where
  "finite_app (FDTable table) x =
    (case map_of table x of Some y \<Rightarrow> y | None \<Rightarrow> FDInd)"
| "finite_app FDInd x = FDInd"
| "finite_app (FDBool b) x = FDInd"

fun finite_holds :: "finite_den \<Rightarrow> bool" where
  "finite_holds (FDBool b) = b"
| "finite_holds FDInd = False"
| "finite_holds (FDTable table) = False"

definition finite_truth :: "bool \<Rightarrow> finite_den" where
  "finite_truth b = FDBool b"

definition finite_eq ::
    "otype \<Rightarrow> finite_den \<Rightarrow> finite_den \<Rightarrow> bool" where
  "finite_eq \<sigma> x y \<longleftrightarrow> x = y"

definition finite_const :: "string \<Rightarrow> otype \<Rightarrow> finite_den" where
  "finite_const c \<sigma> = (SOME x. x \<in> finite_D \<sigma>)"

lemma zip_map_same:
  "zip xs (map F xs) = map (\<lambda>x. (x, F x)) xs"
  by (induction xs) simp_all

lemma finite_D_finite:
  "finite (finite_D \<sigma>)"
proof (induction \<sigma>)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by simp
next
  case (Arr \<sigma> \<tau>)
  let ?xs = "finite_enum_set (finite_D \<sigma>)"
  let ?Y = "{ys. set ys \<subseteq> finite_D \<tau> \<and> length ys = length ?xs}"
  have finite_Y: "finite ?Y"
    using Arr.IH(2) by (rule finite_lists_length_eq)
  have target_subset:
      "finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<subseteq>
        (\<lambda>ys. FDTable (zip ?xs ys)) ` ?Y"
  proof
    fix f
    assume "f \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    then obtain F where
        f: "f = FDTable (map (\<lambda>x. (x, F x)) ?xs)"
      and F: "\<forall>x \<in> finite_D \<sigma>. F x \<in> finite_D \<tau>"
      by auto
    let ?ys = "map F ?xs"
    have enum_set: "set ?xs = finite_D \<sigma>"
      using Arr.IH(1) by (rule finite_enum_set_set)
    have ys: "?ys \<in> ?Y"
      using F enum_set by auto
    have "f = FDTable (zip ?xs ?ys)"
      using f by (simp add: zip_map_same)
    then show "f \<in> (\<lambda>ys. FDTable (zip ?xs ys)) ` ?Y"
      using ys by blast
  qed
  have finite_image: "finite ((\<lambda>ys. FDTable (zip ?xs ys)) ` ?Y)"
    using finite_Y by blast
  show ?case
    by (rule finite_subset[OF target_subset finite_image])
qed

lemma finite_D_nonempty:
  "finite_D \<sigma> \<noteq> {}"
proof (induction \<sigma>)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by simp
next
  case (Arr \<sigma> \<tau>)
  obtain y where y: "y \<in> finite_D \<tau>"
    using Arr.IH(2) by blast
  have "FDTable
      (map (\<lambda>x. (x, y)) (finite_enum_set (finite_D \<sigma>)))
      \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    by (simp, rule exI[of _ "\<lambda>_. y"]) (simp add: y)
  then show ?case
    by blast
qed

lemma finite_enum_set[simp]:
  "set (finite_enum \<sigma>) = finite_D \<sigma>"
  unfolding finite_enum_def
  using finite_D_finite by (rule finite_enum_set_set)

lemma finite_enum_distinct[simp]:
  "distinct (finite_enum \<sigma>)"
  unfolding finite_enum_def
  using finite_D_finite by (rule finite_enum_set_distinct)

lemma finite_const_type:
  "finite_const c \<sigma> \<in> finite_D \<sigma>"
proof -
  have "\<exists>x. x \<in> finite_D \<sigma>"
    using finite_D_nonempty by blast
  then have "(SOME x. x \<in> finite_D \<sigma>) \<in> finite_D \<sigma>"
    by (rule someI_ex)
  then show ?thesis
    unfolding finite_const_def .
qed

lemma map_of_canonical_table:
  assumes "distinct xs" and "x \<in> set xs"
  shows "map_of (map (\<lambda>z. (z, F z)) xs) x = Some (F x)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases "x = a") auto
qed

lemma finite_app_lam:
  assumes "x \<in> finite_D \<sigma>"
  shows "finite_app (finite_lam \<sigma> F) x = F x"
  unfolding finite_lam_def
  using assms
  by (simp add: map_of_canonical_table)

lemma finite_lam_type:
  assumes "\<And>x. x \<in> finite_D \<sigma> \<Longrightarrow> F x \<in> finite_D \<tau>"
  shows "finite_lam \<sigma> F \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
  unfolding finite_lam_def finite_enum_def
  using assms by auto

lemma finite_D_arrow_iff:
  assumes "f \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
  shows "\<exists>F. f = finite_lam \<sigma> F \<and>
    (\<forall>x \<in> finite_D \<sigma>. F x \<in> finite_D \<tau>)"
proof -
  from assms obtain F where
      f: "f = FDTable
        (map (\<lambda>x. (x, F x)) (finite_enum_set (finite_D \<sigma>)))"
    and F: "\<And>x. x \<in> finite_D \<sigma> \<Longrightarrow> F x \<in> finite_D \<tau>"
    by auto
  have "f = finite_lam \<sigma> F"
    using f unfolding finite_lam_def finite_enum_def .
  then show ?thesis
    using F by blast
qed

lemma finite_app_type:
  assumes "f \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and "x \<in> finite_D \<sigma>"
  shows "finite_app f x \<in> finite_D \<tau>"
proof -
  obtain F where f: "f = finite_lam \<sigma> F"
    and F: "\<And>x. x \<in> finite_D \<sigma> \<Longrightarrow> F x \<in> finite_D \<tau>"
    using finite_D_arrow_iff[OF assms(1)] by blast
  show ?thesis
    unfolding f using assms(2) F by (simp add: finite_app_lam)
qed

lemma finite_lam_cong:
  assumes "\<And>x. x \<in> finite_D \<sigma> \<Longrightarrow> F x = G x"
  shows "finite_lam \<sigma> F = finite_lam \<sigma> G"
  unfolding finite_lam_def
  using assms by (intro arg_cong[where f=FDTable] map_cong) auto

lemma finite_eta:
  assumes "f \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
  shows "finite_lam \<sigma> (\<lambda>x. finite_app f x) = f"
proof -
  obtain F where f: "f = finite_lam \<sigma> F"
    and F: "\<And>x. x \<in> finite_D \<sigma> \<Longrightarrow> F x \<in> finite_D \<tau>"
    using finite_D_arrow_iff[OF assms] by blast
  have "finite_lam \<sigma> (\<lambda>x. finite_app f x) = finite_lam \<sigma> F"
    by (rule finite_lam_cong) (simp add: f finite_app_lam)
  then show ?thesis
    by (simp add: f)
qed

lemma finite_function_extensionality:
  assumes f: "f \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and g: "g \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and agree:
      "\<And>x. x \<in> finite_D \<sigma> \<Longrightarrow>
        finite_app f x = finite_app g x"
  shows "f = g"
proof -
  have "finite_lam \<sigma> (\<lambda>x. finite_app f x) =
      finite_lam \<sigma> (\<lambda>x. finite_app g x)"
    by (rule finite_lam_cong) (simp add: agree)
  then show ?thesis
    using finite_eta[OF f] finite_eta[OF g] by simp
qed

lemma finite_truth_type:
  "finite_truth b \<in> finite_D Prop"
  by (simp add: finite_truth_def)

lemma finite_truth_holds[simp]:
  "finite_holds (finite_truth b) = b"
  by (simp add: finite_truth_def)

lemma finite_eq_refl:
  assumes "x \<in> finite_D \<sigma>"
  shows "finite_eq \<sigma> x x"
  by (simp add: finite_eq_def)

lemma finite_eq_subst:
  assumes "finite_eq \<sigma> x y"
    and "f \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o Prop)"
    and "x \<in> finite_D \<sigma>"
    and "y \<in> finite_D \<sigma>"
    and "finite_holds (finite_app f x)"
  shows "finite_holds (finite_app f y)"
  using assms by (simp add: finite_eq_def)

interpretation Finite:
  applicative_structure finite_D finite_const finite_app finite_lam
    finite_truth finite_holds finite_eq
proof
  show "finite_const c \<sigma> \<in> finite_D \<sigma>" for c \<sigma>
    by (rule finite_const_type)
next
  show "finite_app f x \<in> finite_D \<tau>"
    if "f \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and "x \<in> finite_D \<sigma>"
    for f \<sigma> \<tau> x
    using that by (rule finite_app_type)
next
  show "finite_lam \<sigma> F \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    if "\<And>x. x \<in> finite_D \<sigma> \<Longrightarrow> F x \<in> finite_D \<tau>"
    for F \<sigma> \<tau>
    using that by (rule finite_lam_type)
next
  show "finite_truth b \<in> finite_D Prop" for b
    by (rule finite_truth_type)
next
  show "finite_holds (finite_truth b) = b" for b
    by simp
next
  show "finite_lam \<sigma> F = finite_lam \<sigma> G"
    if "\<And>x. x \<in> finite_D \<sigma> \<Longrightarrow> F x = G x"
    for F G \<sigma>
    using that by (rule finite_lam_cong)
next
  show "finite_app (finite_lam \<sigma> F) x = F x"
    if "x \<in> finite_D \<sigma>" for x \<sigma> F
    using that by (rule finite_app_lam)
next
  show "finite_lam \<sigma> (\<lambda>x. finite_app f x) = f"
    if "f \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o \<tau>)" for f \<sigma> \<tau>
    using that by (rule finite_eta)
next
  show "finite_eq \<sigma> x x"
    if "x \<in> finite_D \<sigma>" for x \<sigma>
    using that by (rule finite_eq_refl)
next
  show "finite_holds (finite_app f y)"
    if "finite_eq \<sigma> x y"
      "f \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o Prop)"
      "x \<in> finite_D \<sigma>"
      "y \<in> finite_D \<sigma>"
      "finite_holds (finite_app f x)"
    for \<sigma> x y f
    using that by (rule finite_eq_subst)
qed

lemma finite_predicates_separate:
  assumes x: "x \<in> finite_D \<sigma>"
    and y: "y \<in> finite_D \<sigma>"
    and agree:
      "\<And>p. p \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o Prop) \<Longrightarrow>
        finite_holds (finite_app p x) =
        finite_holds (finite_app p y)"
  shows "x = y"
proof -
  let ?p = "finite_lam \<sigma> (\<lambda>z. finite_truth (z = x))"
  have p_type: "?p \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o Prop)"
    by (rule finite_lam_type) (simp add: finite_truth_type finite_truth_def)
  have "finite_holds (finite_app ?p x) =
      finite_holds (finite_app ?p y)"
    using p_type by (rule agree)
  then have "(x = x) = (y = x)"
    using x y by (simp add: finite_app_lam)
  then show ?thesis
    by simp
qed

lemma finite_identity_characterization:
  assumes "x \<in> finite_D \<sigma>" and "y \<in> finite_D \<sigma>"
  shows "(x = y) \<longleftrightarrow>
    (\<forall>p \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o Prop).
      finite_holds (finite_app p x) =
      finite_holds (finite_app p y))"
  using assms finite_predicates_separate by blast

lemma finite_prop_holds_injective:
  assumes "x \<in> finite_D Prop" and "y \<in> finite_D Prop"
    and "finite_holds x = finite_holds y"
  shows "x = y"
  using assms by auto

lemma finite_vector_extensionality:
  assumes f: "f \<in> finite_D (arrow_type \<sigma>s Prop)"
    and g: "g \<in> finite_D (arrow_type \<sigma>s Prop)"
    and agree:
      "\<And>xs. list_all2 (\<lambda>x \<sigma>. x \<in> finite_D \<sigma>) xs \<sigma>s \<Longrightarrow>
        finite_holds (app_den_vec finite_app f xs) =
        finite_holds (app_den_vec finite_app g xs)"
  shows "f = g"
  using f g agree
proof (induction \<sigma>s arbitrary: f g)
  case Nil
  have f_type: "f \<in> finite_D Prop"
    using Nil.prems(1) by simp
  have g_type: "g \<in> finite_D Prop"
    using Nil.prems(2) by simp
  have same_holds: "finite_holds f = finite_holds g"
    using Nil.prems(3)[of "[]"] by simp
  show ?case
    using f_type g_type same_holds by (rule finite_prop_holds_injective)
next
  case (Cons \<sigma> \<sigma>s)
  have f_type: "f \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o arrow_type \<sigma>s Prop)"
    using Cons.prems(1) by simp
  have g_type: "g \<in> finite_D (\<sigma> \<rightarrow>\<^sub>o arrow_type \<sigma>s Prop)"
    using Cons.prems(2) by simp
  show ?case
  proof (rule finite_function_extensionality[OF f_type g_type])
    fix x
    assume x: "x \<in> finite_D \<sigma>"
    have app_f: "finite_app f x \<in> finite_D (arrow_type \<sigma>s Prop)"
      using f_type x by (rule finite_app_type)
    have app_g: "finite_app g x \<in> finite_D (arrow_type \<sigma>s Prop)"
      using g_type x by (rule finite_app_type)
    show "finite_app f x = finite_app g x"
    proof (rule Cons.IH[OF app_f app_g])
      fix xs
      assume xs: "list_all2 (\<lambda>x \<sigma>. x \<in> finite_D \<sigma>) xs \<sigma>s"
      have "list_all2 (\<lambda>x \<sigma>. x \<in> finite_D \<sigma>)
          (x # xs) (\<sigma> # \<sigma>s)"
        using x xs by simp
      then show "finite_holds
          (app_den_vec finite_app (finite_app f x) xs) =
          finite_holds
          (app_den_vec finite_app (finite_app g x) xs)"
        using Cons.prems(3)[of "x # xs"] by simp
    qed
  qed
qed

lemma finite_classic_identity_identity_valid:
  "Finite.valid_in_context \<Gamma> (classic_identity_identity \<sigma>)"
proof (unfold Finite.valid_in_context_def, intro conjI)
  show "\<Gamma> \<turnstile> classic_identity_identity \<sigma> : Prop"
    by (rule typed_classic_identity_identity)
next
  show "\<forall>\<rho>. Finite.env_typed \<Gamma> \<rho> \<longrightarrow>
      finite_holds (Finite.eval \<rho> (classic_identity_identity \<sigma>))"
  proof (intro allI impI)
    fix \<rho>
    assume env: "Finite.env_typed \<Gamma> \<rho>"
    show "finite_holds (Finite.eval \<rho> (classic_identity_identity \<sigma>))"
      unfolding classic_identity_identity_def identity_ty_def pred_ty_def
      apply (simp only: Finite.eval.simps finite_truth_holds)
      apply (unfold finite_eq_def)
      apply (simp only: extend_env.simps)
      apply (rule finite_function_extensionality[
        where \<sigma>=\<sigma> and \<tau>="\<sigma> \<rightarrow>\<^sub>o Prop"])
        apply (rule finite_lam_type)
        apply (rule finite_lam_type)
        apply (rule finite_truth_type)
       apply (rule finite_lam_type)
       apply (rule finite_lam_type)
       apply (rule finite_truth_type)
      apply (simp only: finite_app_lam)
      apply (rule finite_function_extensionality[
        where \<sigma>=\<sigma> and \<tau>=Prop])
        apply (rule finite_lam_type)
        apply (rule finite_truth_type)
       apply (rule finite_lam_type)
       apply (rule finite_truth_type)
      apply (simp only: finite_app_lam)
      apply (simp add: finite_eq_def finite_truth_def
        finite_identity_characterization eval_nat_numeral)
      apply blast
      done
  qed
qed

lemma finite_bool_comm_conj_valid:
  "Finite.valid_in_context \<Gamma> bool_comm_conj"
proof (unfold Finite.valid_in_context_def, intro conjI)
  show "\<Gamma> \<turnstile> bool_comm_conj : Prop"
    by (rule typed_bool_comm_conj)
next
  show "\<forall>\<rho>. Finite.env_typed \<Gamma> \<rho> \<longrightarrow>
      finite_holds (Finite.eval \<rho> bool_comm_conj)"
  proof (intro allI impI)
    fix \<rho>
    assume "Finite.env_typed \<Gamma> \<rho>"
    show "finite_holds (Finite.eval \<rho> bool_comm_conj)"
      unfolding bool_comm_conj_def prop_bin_ty_def
      apply (simp only: Finite.eval.simps finite_truth_holds)
      apply (unfold finite_eq_def)
      apply (rule finite_vector_extensionality[where \<sigma>s="[Prop, Prop]"])
        apply (simp only: arrow_type.simps)
        apply (rule finite_lam_type)
        apply (rule finite_lam_type)
        apply (rule finite_truth_type)
       apply (simp only: arrow_type.simps)
       apply (rule finite_lam_type)
       apply (rule finite_lam_type)
       apply (rule finite_truth_type)
      apply (rename_tac xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac x xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac y xs)
      apply (case_tac xs)
       apply (auto simp: finite_app_lam eval_nat_numeral)
      done
  qed
qed

lemma finite_bool_comm_disj_valid:
  "Finite.valid_in_context \<Gamma> bool_comm_disj"
proof (unfold Finite.valid_in_context_def, intro conjI)
  show "\<Gamma> \<turnstile> bool_comm_disj : Prop"
    by (rule typed_bool_comm_disj)
next
  show "\<forall>\<rho>. Finite.env_typed \<Gamma> \<rho> \<longrightarrow>
      finite_holds (Finite.eval \<rho> bool_comm_disj)"
  proof (intro allI impI)
    fix \<rho>
    assume "Finite.env_typed \<Gamma> \<rho>"
    show "finite_holds (Finite.eval \<rho> bool_comm_disj)"
      unfolding bool_comm_disj_def prop_bin_ty_def
      apply (simp only: Finite.eval.simps finite_truth_holds)
      apply (unfold finite_eq_def)
      apply (rule finite_vector_extensionality[where \<sigma>s="[Prop, Prop]"])
        apply (simp only: arrow_type.simps)
        apply (rule finite_lam_type)
        apply (rule finite_lam_type)
        apply (rule finite_truth_type)
       apply (simp only: arrow_type.simps)
       apply (rule finite_lam_type)
       apply (rule finite_lam_type)
       apply (rule finite_truth_type)
      apply (rename_tac xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac x xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac y xs)
      apply (case_tac xs)
       apply (auto simp: finite_app_lam eval_nat_numeral)
      done
  qed
qed

lemma finite_bool_dist_conj_disj_valid:
  "Finite.valid_in_context \<Gamma> bool_dist_conj_disj"
proof (unfold Finite.valid_in_context_def, intro conjI)
  show "\<Gamma> \<turnstile> bool_dist_conj_disj : Prop"
    by (rule typed_bool_dist_conj_disj)
next
  show "\<forall>\<rho>. Finite.env_typed \<Gamma> \<rho> \<longrightarrow>
      finite_holds (Finite.eval \<rho> bool_dist_conj_disj)"
  proof (intro allI impI)
    fix \<rho>
    assume "Finite.env_typed \<Gamma> \<rho>"
    show "finite_holds (Finite.eval \<rho> bool_dist_conj_disj)"
      unfolding bool_dist_conj_disj_def
      apply (simp only: Finite.eval.simps finite_truth_holds)
      apply (unfold finite_eq_def)
      apply (rule finite_vector_extensionality[
        where \<sigma>s="[Prop, Prop, Prop]"])
        apply (simp only: arrow_type.simps)
        apply (rule finite_lam_type)+
        apply (rule finite_truth_type)
       apply (simp only: arrow_type.simps)
       apply (rule finite_lam_type)+
       apply (rule finite_truth_type)
      apply (rename_tac xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac x xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac y xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac z xs)
      apply (case_tac xs)
       apply (auto simp: finite_app_lam eval_nat_numeral)
      done
  qed
qed

lemma finite_bool_dist_disj_conj_valid:
  "Finite.valid_in_context \<Gamma> bool_dist_disj_conj"
proof (unfold Finite.valid_in_context_def, intro conjI)
  show "\<Gamma> \<turnstile> bool_dist_disj_conj : Prop"
    by (rule typed_bool_dist_disj_conj)
next
  show "\<forall>\<rho>. Finite.env_typed \<Gamma> \<rho> \<longrightarrow>
      finite_holds (Finite.eval \<rho> bool_dist_disj_conj)"
  proof (intro allI impI)
    fix \<rho>
    assume "Finite.env_typed \<Gamma> \<rho>"
    show "finite_holds (Finite.eval \<rho> bool_dist_disj_conj)"
      unfolding bool_dist_disj_conj_def
      apply (simp only: Finite.eval.simps finite_truth_holds)
      apply (unfold finite_eq_def)
      apply (rule finite_vector_extensionality[
        where \<sigma>s="[Prop, Prop, Prop]"])
        apply (simp only: arrow_type.simps)
        apply (rule finite_lam_type)+
        apply (rule finite_truth_type)
       apply (simp only: arrow_type.simps)
       apply (rule finite_lam_type)+
       apply (rule finite_truth_type)
      apply (rename_tac xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac x xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac y xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac z xs)
      apply (case_tac xs)
       apply (auto simp: finite_app_lam eval_nat_numeral)
      done
  qed
qed

lemma finite_bool_dissolve_conj_disj_valid:
  "Finite.valid_in_context \<Gamma> bool_dissolve_conj_disj"
proof (unfold Finite.valid_in_context_def, intro conjI)
  show "\<Gamma> \<turnstile> bool_dissolve_conj_disj : Prop"
    by (rule typed_bool_dissolve_conj_disj)
next
  show "\<forall>\<rho>. Finite.env_typed \<Gamma> \<rho> \<longrightarrow>
      finite_holds (Finite.eval \<rho> bool_dissolve_conj_disj)"
  proof (intro allI impI)
    fix \<rho>
    assume "Finite.env_typed \<Gamma> \<rho>"
    show "finite_holds (Finite.eval \<rho> bool_dissolve_conj_disj)"
      unfolding bool_dissolve_conj_disj_def prop_bin_ty_def
      apply (simp only: Finite.eval.simps finite_truth_holds)
      apply (unfold finite_eq_def)
      apply (rule finite_vector_extensionality[where \<sigma>s="[Prop, Prop]"])
        apply (simp only: arrow_type.simps)
        apply (rule finite_lam_type)+
        apply (rule finite_truth_type)
       apply (simp only: arrow_type.simps)
       apply (rule finite_lam_type)+
       apply (simp add: eval_nat_numeral)
      apply (rename_tac xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac x xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac y xs)
      apply (case_tac xs)
       apply (auto simp: finite_app_lam eval_nat_numeral)
      done
  qed
qed

lemma finite_bool_dissolve_disj_conj_valid:
  "Finite.valid_in_context \<Gamma> bool_dissolve_disj_conj"
proof (unfold Finite.valid_in_context_def, intro conjI)
  show "\<Gamma> \<turnstile> bool_dissolve_disj_conj : Prop"
    by (rule typed_bool_dissolve_disj_conj)
next
  show "\<forall>\<rho>. Finite.env_typed \<Gamma> \<rho> \<longrightarrow>
      finite_holds (Finite.eval \<rho> bool_dissolve_disj_conj)"
  proof (intro allI impI)
    fix \<rho>
    assume "Finite.env_typed \<Gamma> \<rho>"
    show "finite_holds (Finite.eval \<rho> bool_dissolve_disj_conj)"
      unfolding bool_dissolve_disj_conj_def prop_bin_ty_def
      apply (simp only: Finite.eval.simps finite_truth_holds)
      apply (unfold finite_eq_def)
      apply (rule finite_vector_extensionality[where \<sigma>s="[Prop, Prop]"])
        apply (simp only: arrow_type.simps)
        apply (rule finite_lam_type)+
        apply (rule finite_truth_type)
       apply (simp only: arrow_type.simps)
       apply (rule finite_lam_type)+
       apply (simp add: eval_nat_numeral)
      apply (rename_tac xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac x xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac y xs)
      apply (case_tac xs)
       apply (auto simp: finite_app_lam eval_nat_numeral)
      done
  qed
qed

lemma finite_bool_material_imp_valid:
  "Finite.valid_in_context \<Gamma> bool_material_imp"
proof (unfold Finite.valid_in_context_def, intro conjI)
  show "\<Gamma> \<turnstile> bool_material_imp : Prop"
    by (rule typed_bool_material_imp)
next
  show "\<forall>\<rho>. Finite.env_typed \<Gamma> \<rho> \<longrightarrow>
      finite_holds (Finite.eval \<rho> bool_material_imp)"
  proof (intro allI impI)
    fix \<rho>
    assume "Finite.env_typed \<Gamma> \<rho>"
    show "finite_holds (Finite.eval \<rho> bool_material_imp)"
      unfolding bool_material_imp_def prop_bin_ty_def
      apply (simp only: Finite.eval.simps finite_truth_holds)
      apply (unfold finite_eq_def)
      apply (rule finite_vector_extensionality[where \<sigma>s="[Prop, Prop]"])
        apply (simp only: arrow_type.simps)
        apply (rule finite_lam_type)+
        apply (rule finite_truth_type)
       apply (simp only: arrow_type.simps)
       apply (rule finite_lam_type)+
       apply (rule finite_truth_type)
      apply (rename_tac xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac x xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac y xs)
      apply (case_tac xs)
       apply (auto simp: finite_app_lam eval_nat_numeral)
      done
  qed
qed

lemma finite_boolean_identity_valid:
  assumes "A \<in> set all_boolean_identities"
  shows "Finite.valid_in_context \<Gamma> A"
  using assms
  unfolding all_boolean_identities_def
  using finite_bool_comm_conj_valid finite_bool_comm_disj_valid
    finite_bool_dist_conj_disj_valid finite_bool_dist_disj_conj_valid
    finite_bool_dissolve_conj_disj_valid
    finite_bool_dissolve_disj_conj_valid finite_bool_material_imp_valid
  by auto

lemma finite_classic_absorb_disj_forall_valid:
  "Finite.valid_in_context \<Gamma> (classic_absorb_disj_forall \<sigma>)"
proof (unfold Finite.valid_in_context_def, intro conjI)
  show "\<Gamma> \<turnstile> classic_absorb_disj_forall \<sigma> : Prop"
    by (rule typed_classic_absorb_disj_forall)
next
  show "\<forall>\<rho>. Finite.env_typed \<Gamma> \<rho> \<longrightarrow>
      finite_holds
        (Finite.eval \<rho> (classic_absorb_disj_forall \<sigma>))"
  proof (intro allI impI)
    fix \<rho>
    assume "Finite.env_typed \<Gamma> \<rho>"
    show "finite_holds
        (Finite.eval \<rho> (classic_absorb_disj_forall \<sigma>))"
      unfolding classic_absorb_disj_forall_def pred_ty_def
      apply (simp only: Finite.eval.simps finite_truth_holds)
      apply (unfold finite_eq_def)
      apply (rule finite_vector_extensionality[
        where \<sigma>s="[\<sigma> \<rightarrow>\<^sub>o Prop, \<sigma>]"])
        apply (simp only: arrow_type.simps)
        apply (rule finite_lam_type)+
        apply (rule finite_truth_type)
       apply (simp only: arrow_type.simps)
       apply (rule finite_lam_type)+
       apply (rule finite_app_type[where \<sigma>=\<sigma> and \<tau>=Prop])
        apply (simp add: eval_nat_numeral)
       apply (simp add: eval_nat_numeral)
      apply (rename_tac xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac p xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac x xs)
      apply (case_tac xs)
       apply (auto simp: finite_app_lam eval_nat_numeral)
      done
  qed
qed

lemma finite_classic_dist_disj_forall_valid:
  "Finite.valid_in_context \<Gamma> (classic_dist_disj_forall \<sigma>)"
proof (unfold Finite.valid_in_context_def, intro conjI)
  show "\<Gamma> \<turnstile> classic_dist_disj_forall \<sigma> : Prop"
    by (rule typed_classic_dist_disj_forall)
next
  show "\<forall>\<rho>. Finite.env_typed \<Gamma> \<rho> \<longrightarrow>
      finite_holds
        (Finite.eval \<rho> (classic_dist_disj_forall \<sigma>))"
  proof (intro allI impI)
    fix \<rho>
    assume "Finite.env_typed \<Gamma> \<rho>"
    show "finite_holds
        (Finite.eval \<rho> (classic_dist_disj_forall \<sigma>))"
      unfolding classic_dist_disj_forall_def pred_ty_def
      apply (simp only: Finite.eval.simps finite_truth_holds)
      apply (unfold finite_eq_def)
      apply (rule finite_vector_extensionality[
        where \<sigma>s="[\<sigma> \<rightarrow>\<^sub>o Prop, Prop]"])
        apply (simp only: arrow_type.simps)
        apply (rule finite_lam_type)+
        apply (rule finite_truth_type)
       apply (simp only: arrow_type.simps)
       apply (rule finite_lam_type)+
       apply (rule finite_truth_type)
      apply (rename_tac xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac p xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac q xs)
      apply (case_tac xs)
       apply (auto simp: finite_app_lam eval_nat_numeral)
      done
  qed
qed

lemma finite_classic_absorb_conj_exists_valid:
  "Finite.valid_in_context \<Gamma> (classic_absorb_conj_exists \<sigma>)"
proof (unfold Finite.valid_in_context_def, intro conjI)
  show "\<Gamma> \<turnstile> classic_absorb_conj_exists \<sigma> : Prop"
    by (rule typed_classic_absorb_conj_exists)
next
  show "\<forall>\<rho>. Finite.env_typed \<Gamma> \<rho> \<longrightarrow>
      finite_holds
        (Finite.eval \<rho> (classic_absorb_conj_exists \<sigma>))"
  proof (intro allI impI)
    fix \<rho>
    assume "Finite.env_typed \<Gamma> \<rho>"
    show "finite_holds
        (Finite.eval \<rho> (classic_absorb_conj_exists \<sigma>))"
      unfolding classic_absorb_conj_exists_def pred_ty_def
      apply (simp only: Finite.eval.simps finite_truth_holds)
      apply (unfold finite_eq_def)
      apply (rule finite_vector_extensionality[
        where \<sigma>s="[\<sigma> \<rightarrow>\<^sub>o Prop, \<sigma>]"])
        apply (simp only: arrow_type.simps)
        apply (rule finite_lam_type)+
        apply (rule finite_truth_type)
       apply (simp only: arrow_type.simps)
       apply (rule finite_lam_type)+
       apply (rule finite_app_type[where \<sigma>=\<sigma> and \<tau>=Prop])
        apply (simp add: eval_nat_numeral)
       apply (simp add: eval_nat_numeral)
      apply (rename_tac xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac p xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac x xs)
      apply (case_tac xs)
       apply (auto simp: finite_app_lam eval_nat_numeral)
      done
  qed
qed

lemma finite_classic_dist_conj_exists_valid:
  "Finite.valid_in_context \<Gamma> (classic_dist_conj_exists \<sigma>)"
proof (unfold Finite.valid_in_context_def, intro conjI)
  show "\<Gamma> \<turnstile> classic_dist_conj_exists \<sigma> : Prop"
    by (rule typed_classic_dist_conj_exists)
next
  show "\<forall>\<rho>. Finite.env_typed \<Gamma> \<rho> \<longrightarrow>
      finite_holds
        (Finite.eval \<rho> (classic_dist_conj_exists \<sigma>))"
  proof (intro allI impI)
    fix \<rho>
    assume "Finite.env_typed \<Gamma> \<rho>"
    show "finite_holds
        (Finite.eval \<rho> (classic_dist_conj_exists \<sigma>))"
      unfolding classic_dist_conj_exists_def pred_ty_def
      apply (simp only: Finite.eval.simps finite_truth_holds)
      apply (unfold finite_eq_def)
      apply (rule finite_vector_extensionality[
        where \<sigma>s="[\<sigma> \<rightarrow>\<^sub>o Prop, Prop]"])
        apply (simp only: arrow_type.simps)
        apply (rule finite_lam_type)+
        apply (rule finite_truth_type)
       apply (simp only: arrow_type.simps)
       apply (rule finite_lam_type)+
       apply (rule finite_truth_type)
      apply (rename_tac xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac p xs)
      apply (case_tac xs)
       apply simp
      apply (rename_tac q xs)
      apply (case_tac xs)
       apply (auto simp: finite_app_lam eval_nat_numeral)
      done
  qed
qed

interpretation FiniteCEV:
  vector_equivalence_structure finite_D finite_const finite_app finite_lam
    finite_truth finite_holds finite_eq
proof
  show "A \<in> set all_boolean_identities \<Longrightarrow>
      Finite.valid_in_context \<Gamma> A" for A \<Gamma>
    by (rule finite_boolean_identity_valid)
next
  show "Finite.valid_in_context \<Gamma> (classic_identity_identity \<sigma>)"
    for \<Gamma> \<sigma>
    by (rule finite_classic_identity_identity_valid)
next
  show "Finite.valid_in_context \<Gamma> (classic_absorb_disj_forall \<sigma>)"
    for \<Gamma> \<sigma>
    by (rule finite_classic_absorb_disj_forall_valid)
next
  show "Finite.valid_in_context \<Gamma> (classic_dist_disj_forall \<sigma>)"
    for \<Gamma> \<sigma>
    by (rule finite_classic_dist_disj_forall_valid)
next
  show "Finite.valid_in_context \<Gamma> (classic_absorb_conj_exists \<sigma>)"
    for \<Gamma> \<sigma>
    by (rule finite_classic_absorb_conj_exists_valid)
next
  show "Finite.valid_in_context \<Gamma> (classic_dist_conj_exists \<sigma>)"
    for \<Gamma> \<sigma>
    by (rule finite_classic_dist_conj_exists_valid)
next
  show "finite_eq Prop x y"
    if "x \<in> finite_D Prop" and "y \<in> finite_D Prop"
      and "finite_holds x = finite_holds y"
    for x y
    using finite_prop_holds_injective[OF that]
    by (simp add: finite_eq_def)
next
  show "finite_eq (arrow_type \<sigma>s Prop) f g"
    if "f \<in> finite_D (arrow_type \<sigma>s Prop)"
      "g \<in> finite_D (arrow_type \<sigma>s Prop)"
      "\<And>xs. list_all2 (\<lambda>x \<sigma>. x \<in> finite_D \<sigma>) xs \<sigma>s \<Longrightarrow>
        finite_holds (app_den_vec finite_app f xs) =
        finite_holds (app_den_vec finite_app g xs)"
    for f \<sigma>s g
    using finite_vector_extensionality[OF that]
    by (simp add: finite_eq_def)
qed

section \<open>Certified nonvacuity\<close>

theorem CEV_not_proves_ObjFalse:
  "\<not> [] \<turnstile>\<^sub>CEV ObjFalse"
proof
  assume d: "[] \<turnstile>\<^sub>CEV ObjFalse"
  have valid: "Finite.valid_in_context [] ObjFalse"
    using d by (rule FiniteCEV.CEV_soundness)
  have env: "Finite.env_typed [] (\<lambda>_. FDInd)"
    unfolding Finite.env_typed_def by (simp add: lookup_def)
  have "finite_holds (Finite.eval (\<lambda>_. FDInd) ObjFalse)"
    using valid env by (rule Finite.valid_holds)
  then show False
    by (simp add: ObjFalse_def ObjTrue_def)
qed

theorem CEV_not_proves_box_ObjFalse:
  "\<not> [] \<turnstile>\<^sub>CEV \<box>\<^sub>o ObjFalse"
proof
  assume d: "[] \<turnstile>\<^sub>CEV \<box>\<^sub>o ObjFalse"
  have valid: "Finite.valid_in_context [] (\<box>\<^sub>o ObjFalse)"
    using d by (rule FiniteCEV.CEV_soundness)
  have env: "Finite.env_typed [] (\<lambda>_. FDInd)"
    unfolding Finite.env_typed_def by (simp add: lookup_def)
  have "finite_holds
      (Finite.eval (\<lambda>_. FDInd) (\<box>\<^sub>o ObjFalse))"
    using valid env by (rule Finite.valid_holds)
  then show False
    by (simp add: ObjBox_def ObjFalse_def ObjTrue_def
      finite_eq_def finite_truth_def)
qed

corollary CEV_supported_modal_successor_nonvacuous:
  obtains K C S D T where
      "finite K"
    and "K \<noteq> {}"
    and "CEV_supported_world K C [] S"
    and "\<box>\<^sub>o ObjFalse \<notin> S"
    and "D \<subseteq> UNIV - C"
    and "infinite D"
    and "CEV_supported_world K (C \<union> D) [] T"
    and
      "CEV_supported_quotient_arrow C (C \<union> D)
        [] S [] T Var"
    and "Neg ObjFalse \<in> T"
    and "ObjFalse \<notin> T"
proof -
  have false_type: "[] \<turnstile> ObjFalse : Prop"
    by (rule typed_ObjFalse)
  show thesis
    using false_type CEV_not_proves_box_ObjFalse that
    by (rule CEV_supported_modal_successor_applicable)
qed

end
