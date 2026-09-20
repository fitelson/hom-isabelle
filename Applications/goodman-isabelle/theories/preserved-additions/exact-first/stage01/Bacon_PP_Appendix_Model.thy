theory Bacon_PP_Appendix_Model
  imports 
    "Goodman_Exact_Legacy_01.Bacon_PP_MSet"
    "HOL-Library.Sublist"
begin

section \<open>Bacon's appendix model at types \<open>t\<close> and \<open>t \<rightarrow> t\<close>\<close>

text \<open>
  This theory packages the semantic objects already constructed in
  \<open>Bacon_PP_Generic_Witness\<close> and \<open>Bacon_PP_MSet\<close> in the notation and
  order of Bacon's Definitions 7.1, 7.2, and 8.1.  The purpose is a
  compliance theorem, not a new variant of the model.

  The substitution monoid is \<open>nat list\<close>.  Its multiplication is literal list
  concatenation, so the division action on propositions is
  \<open>i \<cdot> P = {j. j @ i \<in> P}\<close>.  Bacon describes the induced tree by initial
  segments.  With the displayed multiplication its raw accessibility relation
  is suffix extension; reversing every finite word is an explicit rooted-frame
  isomorphism to the initial-segment presentation.
\<close>

subsection \<open>Definition 7.1: the substitution monoid and proposition action\<close>

definition pp_subst_one :: pp_word where
  "pp_subst_one = []"

definition pp_subst_comp :: "pp_word \<Rightarrow> pp_word \<Rightarrow> pp_word" where
  "pp_subst_comp i j = i @ j"

lemma pp_subst_comp_one_left[simp]:
  "pp_subst_comp pp_subst_one i = i"
  by (simp add: pp_subst_comp_def pp_subst_one_def)

lemma pp_subst_comp_one_right[simp]:
  "pp_subst_comp i pp_subst_one = i"
  by (simp add: pp_subst_comp_def pp_subst_one_def)

lemma pp_subst_comp_assoc:
  "pp_subst_comp i (pp_subst_comp j k) =
    pp_subst_comp (pp_subst_comp i j) k"
  by (simp add: pp_subst_comp_def append_assoc)

definition pp_prop_action ::
    "pp_word \<Rightarrow> pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_prop_action i P = pp_view i P"

theorem pp_prop_action_division:
  "j \<in> pp_prop_action i P \<longleftrightarrow>
    pp_subst_comp j i \<in> P"
  by (simp add: pp_prop_action_def pp_view_def pp_subst_comp_def)

lemma pp_prop_action_one[simp]:
  "pp_prop_action pp_subst_one P = P"
  by (simp add: pp_prop_action_def pp_subst_one_def)

lemma pp_prop_action_comp:
  "pp_prop_action i (pp_prop_action j P) =
    pp_prop_action (pp_subst_comp i j) P"
  by (simp add: pp_prop_action_def pp_subst_comp_def pp_view_compose)

theorem pp_prop_action_surjective:
  "surj (pp_prop_action i)"
  unfolding pp_prop_action_def
  by (rule pp_view_surjective)

subsection \<open>The induced rooted frame\<close>

definition pp_bacon_accessible ::
    "pp_word \<Rightarrow> pp_word \<Rightarrow> bool" where
  "pp_bacon_accessible i j \<longleftrightarrow>
    (\<exists>k. pp_subst_comp k i = j)"

lemma pp_bacon_accessible_iff_suffix:
  "pp_bacon_accessible i j \<longleftrightarrow> (\<exists>k. j = k @ i)"
  by (auto simp: pp_bacon_accessible_def pp_subst_comp_def)

lemma pp_bacon_accessible_eq_existing:
  "pp_bacon_accessible = pp_accessible"
  by (rule ext)+
    (simp add: pp_bacon_accessible_iff_suffix pp_accessible_def)

theorem pp_bacon_accessible_reversal_prefix:
  "pp_bacon_accessible i j \<longleftrightarrow> prefix (rev i) (rev j)"
proof
  assume "pp_bacon_accessible i j"
  then obtain k where j: "j = k @ i"
    by (auto simp: pp_bacon_accessible_iff_suffix)
  show "prefix (rev i) (rev j)"
    unfolding j
    by (simp add: prefix_def)
next
  assume prefix: "prefix (rev i) (rev j)"
  then obtain k where rev_j: "rev j = rev i @ k"
    by (auto simp: prefix_def)
  have "j = rev k @ i"
    using rev_j by (metis rev_append rev_rev_ident)
  then show "pp_bacon_accessible i j"
    by (auto simp: pp_bacon_accessible_iff_suffix)
qed

lemma pp_bacon_root_is_empty_word:
  "pp_subst_one = []"
  by (simp add: pp_subst_one_def)

theorem pp_bacon_truth_clause:
  "pp_root_true P \<longleftrightarrow> pp_subst_one \<in> P"
  by (simp add: pp_root_true_def pp_subst_one_def)

subsection \<open>Definition 7.2: the unary function space\<close>

definition pp_bacon_unary_domain ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) set" where
  "pp_bacon_unary_domain = {F. pp_function_space_member F}"

definition pp_bacon_unary_action ::
    "pp_word \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow>
      (pp_sem_prop \<Rightarrow> pp_sem_prop)" where
  "pp_bacon_unary_action i F = pp_fun_view i F"

theorem pp_bacon_unary_domain_iff:
  "F \<in> pp_bacon_unary_domain \<longleftrightarrow>
    (\<forall>i P Q.
      pp_prop_action i P = pp_prop_action i Q \<longrightarrow>
      pp_prop_action i (F P) = pp_prop_action i (F Q))"
  by (simp add: pp_bacon_unary_domain_def
      pp_function_space_member_def pp_prop_action_def)

theorem pp_bacon_unary_action_preimage_clause:
  assumes F: "F \<in> pp_bacon_unary_domain"
    and preimage: "pp_prop_action i Q = P"
  shows "pp_bacon_unary_action i F P = pp_prop_action i (F Q)"
  using pp_fun_view_preimage_independent[of F i Q P]
    F preimage
  by (simp add: pp_bacon_unary_domain_def
      pp_bacon_unary_action_def pp_prop_action_def)

lemma pp_bacon_unary_action_one[simp]:
  "pp_bacon_unary_action pp_subst_one F = F"
  by (simp add: pp_bacon_unary_action_def pp_subst_one_def)

lemma pp_bacon_unary_action_comp:
  "pp_bacon_unary_action i (pp_bacon_unary_action j F) =
    pp_bacon_unary_action (pp_subst_comp i j) F"
  by (simp add: pp_bacon_unary_action_def pp_subst_comp_def
      pp_fun_view_compose)

theorem pp_bacon_unary_action_closed:
  assumes "F \<in> pp_bacon_unary_domain"
  shows "pp_bacon_unary_action i F \<in> pp_bacon_unary_domain"
  using assms pp_fun_view_member
  by (simp add: pp_bacon_unary_domain_def pp_bacon_unary_action_def)

theorem pp_bacon_unary_action_surjective:
  assumes "F \<in> pp_bacon_unary_domain"
  shows "\<exists>G \<in> pp_bacon_unary_domain.
    pp_bacon_unary_action i G = F"
proof -
  have member: "pp_function_space_member F"
    using assms by (simp add: pp_bacon_unary_domain_def)
  obtain G where G: "pp_function_space_member G"
    and action: "pp_fun_view i G = F"
    using pp_fun_view_surjective_on_function_space[OF member, of i]
    by blast
  show ?thesis
    using G action
    by (intro bexI[of _ G])
      (simp_all add: pp_bacon_unary_domain_def pp_bacon_unary_action_def)
qed

theorem pp_bacon_application_substitution:
  assumes "F \<in> pp_bacon_unary_domain"
  shows "pp_bacon_unary_action i F (pp_prop_action i P) =
    pp_prop_action i (F P)"
  using pp_bacon_unary_action_preimage_clause[OF assms, of i P
      "pp_prop_action i P"]
  by simp

text \<open>
  The preceding theorems are the proposition/unary fragment of Bacon's full
  surjective M-set model: literal division at \<open>t\<close>, precisely the restricted
  function domain of Definition 7.2, its preimage-based action, Proposition 8
  for that action, ordinary application, and the substitution/application law.
  The next compliance layer must iterate this construction at every object
  type rather than replacing it with unrestricted function spaces.
\<close>

end
