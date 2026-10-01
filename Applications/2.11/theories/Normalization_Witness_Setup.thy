theory Normalization_Witness_Setup
  imports Classicism_Rigidity_Component
begin

section \<open>Atomicity of the concrete root Boolean algebra\<close>

lemma root_actual_atom: "ba_atom ((True,False,{})::root_prop)"
  unfolding ba_atom_def
  by (auto simp: less_eq_prod_def prod_eq_iff bot_prod_def)

lemma root_leaf_atom: "ba_atom ((False,False,{n})::root_prop)"
  unfolding ba_atom_def
  by (auto simp: less_eq_prod_def prod_eq_iff bot_prod_def subset_singleton_iff)

theorem root_prop_atomic:
  fixes p :: root_prop
  assumes nonzero: "p \<noteq> \<bottom>"
  shows "\<exists>a. ba_atom a \<and> a \<le> p"
proof -
  obtain b c S where p: "p = (b,c,S)" by (cases p) auto
  show ?thesis
  proof (cases b)
    case True
    show ?thesis
    proof (rule exI[where x="(True,False,{})"], rule conjI)
      show "ba_atom ((True,False,{})::root_prop)" by (rule root_actual_atom)
      show "((True,False,{})::root_prop) \<le> p"
        by (simp add: p True less_eq_prod_def)
    qed
  next
    case False
    note b = False
    show ?thesis
    proof (cases c)
      case True
      show ?thesis
      proof (rule exI[where x=norm_w], rule conjI)
        show "ba_atom norm_w" by (rule norm_w_atom)
        show "norm_w \<le> p"
          by (simp add: norm_w_def p b True less_eq_prod_def)
      qed
    next
      case False
      have nonempty: "S \<noteq> {}"
        using nonzero by (simp add: p b False bot_prod_def)
      obtain n where n: "n \<in> S" using nonempty by auto
      show ?thesis
      proof (rule exI[where x="(False,False,{n})"], rule conjI)
        show "ba_atom ((False,False,{n})::root_prop)" by (rule root_leaf_atom)
        show "((False,False,{n})::root_prop) \<le> p"
          by (simp add: p b False n less_eq_prod_def)
      qed
    qed
  qed
qed

section \<open>The intermediate-world witness from footnote 42\<close>

text \<open>These definitions are concrete profile calculations. In particular,
  comparison_property is used as X-star. Its identification with the actual
  least upper bound of the appropriate source-language haecceities, and the
  translation of these profile conditions into source-language sentences,
  require the separate all-type action-model bridge. No such bridge is
  asserted by this theory.\<close>

definition footnote_Y :: root_property where
  "footnote_Y = ({},{\<bottom>},\<lambda>n. {False})"

definition middle_application :: "root_property \<Rightarrow> middle_prop \<Rightarrow> middle_prop" where
  "middle_application P a = (a \<in> middle_ext P, snd a \<in> limit_ext P)"

definition middle_necessary_member :: "root_property \<Rightarrow> middle_prop \<Rightarrow> bool" where
  "middle_necessary_member P a \<longleftrightarrow>
    a \<in> middle_ext P \<and> snd a \<in> limit_ext P"

definition footnote_failure_profile :: middle_prop where
  "footnote_failure_profile =
    middle_application comparison_property (to_middle norm_q) \<sqinter>
    - middle_application footnote_Y (to_middle norm_q)"

lemma footnote_Y_actual [simp]: "actual_ext footnote_Y = {}"
  by (simp add: footnote_Y_def)

lemma footnote_Y_middle [simp]: "middle_ext footnote_Y = {\<bottom>}"
  by (simp add: footnote_Y_def)

lemma footnote_Y_leaf [simp]: "leaf_ext footnote_Y n = {False}"
  by (simp add: footnote_Y_def)

lemma footnote_Y_limit [simp]: "limit_ext footnote_Y = {False}"
  by (auto simp: limit_ext_def footnote_Y_def norm_U.proper)

lemma comparison_middle [simp]: "middle_ext comparison_property = {\<bottom>}"
  by (simp add: comparison_property_def)

lemma footnote_all_middle_instances_necessary:
  "\<forall>a\<in>middle_ext comparison_property. middle_necessary_member footnote_Y a"
  by (simp add: middle_necessary_member_def bot_prod_def)

lemma footnote_comparison_application:
  "middle_application comparison_property (to_middle norm_q) = (False,True)"
  by (simp add: middle_application_def norm_q_def bot_prod_def)

lemma footnote_Y_application:
  "middle_application footnote_Y (to_middle norm_q) = (False,False)"
  by (simp add: middle_application_def norm_q_def bot_prod_def)

lemma footnote_failure_profile_exact:
  "footnote_failure_profile = (False,True)"
  by (simp add: footnote_failure_profile_def footnote_comparison_application
      footnote_Y_application)

lemma footnote_q_is_failure_profile:
  "to_middle norm_q = footnote_failure_profile"
  by (simp add: norm_q_def footnote_failure_profile_exact)

lemma footnote_q_below_failure_profile:
  "to_middle norm_q \<le> footnote_failure_profile"
  by (simp add: footnote_q_is_failure_profile)

lemma root_w_selects_middle_bit:
  fixes p :: root_prop
  shows "norm_w \<le> p \<longleftrightarrow> fst (to_middle p)"
  by (cases p) (simp add: norm_w_def to_middle_def less_eq_prod_def)

text \<open>The following endpoint records the precise concrete intermediate
  premise: all X-star instances necessarily satisfy Y, q is an atom there,
  and q entails the failure profile. Its normalization loses that atom.\<close>

theorem footnote_setup_and_normalization_loss:
  "ba_atom norm_w \<and>
    (\<forall>a\<in>middle_ext comparison_property. middle_necessary_member footnote_Y a) \<and>
    ba_atom (to_middle norm_q) \<and>
    to_middle norm_q \<le> footnote_failure_profile \<and>
    to_middle (Inf norm_fiber) \<noteq> to_middle norm_q \<and>
    \<not> ba_atom (to_middle (Inf norm_fiber))"
  by (simp add: norm_w_atom footnote_all_middle_instances_necessary
      norm_q_middle_atom footnote_q_below_failure_profile
      normalization_does_not_preserve_fiber normalized_middle_not_atom)

section \<open>Audit endpoints\<close>

ML \<open>
  val facts = [@{thm root_actual_atom}, @{thm root_leaf_atom},
    @{thm root_prop_atomic}, @{thm footnote_Y_limit},
    @{thm footnote_all_middle_instances_necessary},
    @{thm footnote_failure_profile_exact}, @{thm footnote_q_is_failure_profile},
    @{thm root_w_selects_middle_bit},
    @{thm footnote_setup_and_normalization_loss}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "NORMALIZATION-WITNESS: 9 clean endpoints; concrete profile layer only";
\<close>

end
