theory Classicism_Rigidity_Component
  imports Classicism_Normalization_Core
begin

section \<open>The proposition-input rigidity calculation\<close>

text \<open>This concrete layer contains all root properties of propositions:
  a current truth set, an intermediate truth set, and terminal truth sets.
  The limit truth set is fixed by the ultrafilter. Its full all-type
  action-model embedding is a separate obligation, not a locale premise
  silently counted as discharged here.\<close>

type_synonym root_property =
  "root_prop set \<times> middle_prop set \<times> (nat \<Rightarrow> bool set)"

abbreviation actual_ext :: "root_property \<Rightarrow> root_prop set" where
  "actual_ext P \<equiv> fst P"

abbreviation middle_ext :: "root_property \<Rightarrow> middle_prop set" where
  "middle_ext P \<equiv> fst (snd P)"

abbreviation leaf_ext :: "root_property \<Rightarrow> nat \<Rightarrow> bool set" where
  "leaf_ext P \<equiv> snd (snd P)"

definition limit_ext :: "root_property \<Rightarrow> bool set" where
  "limit_ext P = {b. eventually (\<lambda>n. b \<in> leaf_ext P n) norm_U}"

definition necessary_member :: "root_property \<Rightarrow> root_prop \<Rightarrow> bool" where
  "necessary_member Y p \<longleftrightarrow>
    p \<in> actual_ext Y \<and> to_middle p \<in> middle_ext Y \<and>
    (\<forall>n. (n \<in> snd (snd p)) \<in> leaf_ext Y n) \<and>
    ubit (snd (snd p)) \<in> limit_ext Y"

definition persistent_profile :: "root_property \<Rightarrow> bool" where
  "persistent_profile Z \<longleftrightarrow>
    (\<forall>p \<in> actual_ext Z. necessary_member Z p) \<and>
    (\<forall>q \<in> middle_ext Z. snd q \<in> limit_ext Z)"

definition inextensible_root :: "root_property \<Rightarrow> bool" where
  "inextensible_root Z \<longleftrightarrow>
    (\<forall>Y. (\<forall>p \<in> actual_ext Z. necessary_member Y p) \<longrightarrow> Z \<le> Y)"

definition inextensible_middle :: "root_property \<Rightarrow> bool" where
  "inextensible_middle Z \<longleftrightarrow>
    (\<forall>S T. (\<forall>q \<in> middle_ext Z. q \<in> S \<and> snd q \<in> T) \<longrightarrow>
      middle_ext Z \<subseteq> S \<and> limit_ext Z \<subseteq> T)"

definition rigid_profile :: "root_property \<Rightarrow> bool" where
  "rigid_profile Z \<longleftrightarrow> persistent_profile Z \<and>
    inextensible_root Z \<and> inextensible_middle Z"

definition zero_fiber :: "root_prop set" where
  "zero_fiber = {p. to_middle p = \<bottom>}"

definition comparison_property :: root_property where
  "comparison_property = (zero_fiber,{\<bottom>},\<lambda>n. UNIV)"

lemma ubit_finite: "finite S \<Longrightarrow> \<not> ubit S"
  unfolding ubit_def by (rule norm_U.finite) simp

lemma test_zero_fiber:
  "(False,False,if b then {n} else {}) \<in> zero_fiber"
  by (cases b) (simp_all add: zero_fiber_def ubit_finite bot_prod_def)

lemma bottom_zero_fiber: "(\<bottom>::root_prop) \<in> zero_fiber"
  by (simp add: zero_fiber_def)

lemma comparison_limit [simp]: "limit_ext comparison_property = UNIV"
  by (simp add: limit_ext_def comparison_property_def)

lemma comparison_necessary:
  assumes "p \<in> zero_fiber"
  shows "necessary_member comparison_property p"
  using assms by (simp add: necessary_member_def comparison_property_def zero_fiber_def limit_ext_def)

lemma persistent_fiber_full_leaves:
  assumes ext: "actual_ext Z = zero_fiber"
    and per: "persistent_profile Z"
  shows "leaf_ext Z n = UNIV"
proof -
  have member: "b \<in> leaf_ext Z n" for b
  proof -
    let ?p = "(False,False,if b then {n} else {})"
    have "?p \<in> actual_ext Z" using test_zero_fiber ext by simp
    then have "necessary_member Z ?p"
      using per unfolding persistent_profile_def by blast
    then have all: "\<forall>k. (k \<in> (if b then {n} else {})) \<in> leaf_ext Z k"
      by (simp add: necessary_member_def)
    have "(n \<in> (if b then {n} else {})) \<in> leaf_ext Z n"
      by (rule spec[OF all])
    then show ?thesis by (cases b) auto
  qed
  then show ?thesis by auto
qed

lemma persistent_fiber_full_limit:
  assumes "actual_ext Z = zero_fiber" "persistent_profile Z"
  shows "limit_ext Z = UNIV"
  using persistent_fiber_full_leaves[OF assms]
  by (simp add: limit_ext_def)

lemma persistent_fiber_middle_member:
  assumes ext: "actual_ext Z = zero_fiber"
    and per: "persistent_profile Z"
  shows "(\<bottom>::middle_prop) \<in> middle_ext Z"
proof -
  have "(\<bottom>::root_prop) \<in> actual_ext Z"
    using ext bottom_zero_fiber by simp
  then have "necessary_member Z \<bottom>"
    using per unfolding persistent_profile_def by blast
  then show ?thesis by (simp add: necessary_member_def)
qed

lemma inextensible_fiber_middle_bound:
  assumes ext: "actual_ext Z = zero_fiber"
    and inex: "inextensible_root Z"
  shows "middle_ext Z \<subseteq> {\<bottom>}"
proof -
  have "\<forall>p \<in> actual_ext Z. necessary_member comparison_property p"
    using comparison_necessary ext by blast
  then have "Z \<le> comparison_property"
    using inex unfolding inextensible_root_def by blast
  then show ?thesis
    by (simp add: comparison_property_def less_eq_prod_def)
qed

theorem no_rigid_profile_for_zero_fiber:
  "\<not> (\<exists>Z::root_property. actual_ext Z = zero_fiber \<and> rigid_profile Z)"
proof
  assume "\<exists>Z::root_property. actual_ext Z = zero_fiber \<and> rigid_profile Z"
  then obtain Z where ext: "actual_ext Z = zero_fiber"
    and per: "persistent_profile Z"
    and root: "inextensible_root Z"
    and middle: "inextensible_middle Z"
    unfolding rigid_profile_def by blast
  have mid: "middle_ext Z = {\<bottom>}"
    using persistent_fiber_middle_member[OF ext per]
      inextensible_fiber_middle_bound[OF ext root] by blast
  have lim: "limit_ext Z = UNIV"
    by (rule persistent_fiber_full_limit[OF ext per])
  have premise: "\<forall>q \<in> middle_ext Z.
    q \<in> {\<bottom>} \<and> snd q \<in> {False}"
    by (simp add: mid)
  have "limit_ext Z \<subseteq> {False}"
    using middle premise unfolding inextensible_middle_def by blast
  with lim show False by auto
qed

ML \<open>
  val th = @{thm no_rigid_profile_for_zero_fiber};
  val _ = if null (Thm_Deps.all_oracles [th]) andalso
    null (Thm.hyps_of th) andalso null (Thm.tpairs_of th)
    then writeln "RIGIDITY-COMPONENT: clean endpoint; all-type bridge remains separate"
    else error "Unexpected proof dependency or residual obligation";
\<close>

end
