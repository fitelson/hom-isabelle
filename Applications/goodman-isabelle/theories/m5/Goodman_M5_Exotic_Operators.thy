theory Goodman_M5_Exotic_Operators
  imports Goodman_Integration_Exact_M.Goodman_Exact_M2_Transfer
    Goodman_Integration_Exact_L2.Goodman_Exact_L2_Transfer
begin

section \<open>M5: a general two-point truth-index transposition\<close>

text \<open>
  We reconstruct the arguments of Bacon_PP_Goodman_M5 and its
  Orbit_Avoidance repair without importing their M4/M6 comparison-model
  chain. For a root-false proposition s, the pair is s and insert [] s.
  No proper view of either member may reenter the pair. This no-echo
  hypothesis is what prevents outsiders entering the pair and makes the
  classifier involutive; swapping two root truth values alone is insufficient.
\<close>

definition gi_M5_pair :: "pp_sem_prop \<Rightarrow> pp_sem_prop set" where
  "gi_M5_pair s = {s, insert [] s}"

definition gi_M5_swapped_index :: "pp_sem_prop \<Rightarrow> pp_sem_prop set" where
  "gi_M5_swapped_index s = ({P. [] \<in> P} - {insert [] s}) \<union> {s}"

definition gi_M5_exotic :: "pp_sem_prop \<Rightarrow> pp_e_operator" where
  "gi_M5_exotic s = pp_classifier (gi_M5_swapped_index s)"

definition gi_M5_truth_preserving :: "pp_e_operator \<Rightarrow> bool" where
  "gi_M5_truth_preserving F \<longleftrightarrow> (\<forall>P. ([] \<in> F P) = ([] \<in> P))"

definition gi_M5_truth_flipping :: "pp_e_operator \<Rightarrow> bool" where
  "gi_M5_truth_flipping F \<longleftrightarrow> (\<forall>P. ([] \<in> F P) = ([] \<notin> P))"

definition gi_M5_biconditional_operator :: "pp_sem_prop \<Rightarrow> pp_e_operator" where
  "gi_M5_biconditional_operator A = (\<lambda>P. (P \<inter> A) \<union> (- P \<inter> - A))"

lemma gi_M5_exotic_equivariant:
  "pp_equivariant_operator (gi_M5_exotic s)"
  unfolding gi_M5_exotic_def by (rule pp_classifier_equivariant_operator)

lemma gi_M5_exotic_view:
  "pp_view i (gi_M5_exotic s P) = gi_M5_exotic s (pp_view i P)"
  using gi_M5_exotic_equivariant[of s] unfolding pp_equivariant_operator_def by blast

locale gi_M5_no_echo_pair =
  fixes s :: pp_sem_prop
  assumes root_false: "[] \<notin> s"
    and no_echo: "\<And>Q i. Q \<in> gi_M5_pair s \<Longrightarrow> i \<noteq> [] \<Longrightarrow> pp_view i Q \<notin> gi_M5_pair s"
begin

lemma pair_distinct:
  "s \<noteq> insert [] s"
  using root_false by blast

lemma flip_rule:
  "i \<in> gi_M5_exotic s P \<longleftrightarrow>
    (if pp_view i P \<in> gi_M5_pair s then i \<notin> P else i \<in> P)"
proof -
  have root: "[] \<in> pp_view i P \<longleftrightarrow> i \<in> P" by (rule pp_view_membership_at_root)
  show ?thesis unfolding gi_M5_exotic_def pp_classifier_def gi_M5_swapped_index_def gi_M5_pair_def
    using root root_false by auto
qed

lemma swaps_false:
  "gi_M5_exotic s s = insert [] s"
proof (rule set_eqI)
  fix i
  show "i \<in> gi_M5_exotic s s \<longleftrightarrow> i \<in> insert [] s"
  proof (cases "i = []")
    case True
    show ?thesis using True root_false by (simp add: flip_rule gi_M5_pair_def)
  next
    case False
    have outside: "pp_view i s \<notin> gi_M5_pair s"
      by (rule no_echo[OF _ False]; simp add: gi_M5_pair_def)
    show ?thesis using False outside by (simp add: flip_rule)
  qed
qed

lemma swaps_true:
  "gi_M5_exotic s (insert [] s) = s"
proof (rule set_eqI)
  fix i
  show "i \<in> gi_M5_exotic s (insert [] s) \<longleftrightarrow> i \<in> s"
  proof (cases "i = []")
    case True
    show ?thesis using True root_false by (simp add: flip_rule gi_M5_pair_def)
  next
    case False
    have outside: "pp_view i (insert [] s) \<notin> gi_M5_pair s"
      by (rule no_echo[OF _ False]; simp add: gi_M5_pair_def)
    show ?thesis using False outside by (simp add: flip_rule)
  qed
qed

lemma preserves_pair:
  "P \<in> gi_M5_pair s \<Longrightarrow> gi_M5_exotic s P \<in> gi_M5_pair s"
  unfolding gi_M5_pair_def using swaps_false swaps_true by auto

lemma preimage_pair_only_at_root:
  assumes image: "gi_M5_exotic s P \<in> gi_M5_pair s" and view: "pp_view i P \<in> gi_M5_pair s"
  shows "i = []"
proof (rule ccontr)
  assume nonroot: "i \<noteq> []"
  have inside: "pp_view i (gi_M5_exotic s P) \<in> gi_M5_pair s"
    by (simp only: gi_M5_exotic_view; rule preserves_pair[OF view])
  have outside: "pp_view i (gi_M5_exotic s P) \<notin> gi_M5_pair s" by (rule no_echo[OF image nonroot])
  show False using inside outside by contradiction
qed

lemma no_outsider_enters_pair:
  assumes image: "gi_M5_exotic s P \<in> gi_M5_pair s"
  shows "P \<in> gi_M5_pair s"
proof (rule ccontr)
  assume outside: "P \<notin> gi_M5_pair s"
  have no_view: "pp_view i P \<notin> gi_M5_pair s" for i
  proof (cases "i = []")
    case True
    show ?thesis using outside by (simp add: True)
  next
    case False
    show ?thesis using preimage_pair_only_at_root[OF image] False by blast
  qed
  have unchanged: "gi_M5_exotic s P = P"
    by (rule set_eqI; simp add: flip_rule no_view)
  show False using image outside unchanged by simp
qed

lemma pair_iff:
  "gi_M5_exotic s P \<in> gi_M5_pair s \<longleftrightarrow> P \<in> gi_M5_pair s"
  using no_outsider_enters_pair preserves_pair by blast

theorem involution:
  "gi_M5_exotic s (gi_M5_exotic s P) = P"
proof (rule set_eqI)
  fix i
  have stable: "pp_view i (gi_M5_exotic s P) \<in> gi_M5_pair s \<longleftrightarrow> pp_view i P \<in> gi_M5_pair s"
    by (simp only: gi_M5_exotic_view pair_iff)
  show "i \<in> gi_M5_exotic s (gi_M5_exotic s P) \<longleftrightarrow> i \<in> P"
    by (simp only: flip_rule stable; auto)
qed

corollary bijective:
  "bij (gi_M5_exotic s)"
  unfolding bij_def inj_def surj_def using involution by metis

lemma pair_nonextreme:
  "{} \<notin> gi_M5_pair s" "UNIV \<notin> gi_M5_pair s"
proof -
  show "{} \<notin> gi_M5_pair s"
  proof
    assume member: "{} \<in> gi_M5_pair s"
    have "pp_view [0] {} \<notin> gi_M5_pair s" by (rule no_echo[OF member]; simp)
    then show False using member by (simp add: pp_view_def)
  qed
  show "UNIV \<notin> gi_M5_pair s"
  proof
    assume member: "UNIV \<in> gi_M5_pair s"
    have "pp_view [0] UNIV \<notin> gi_M5_pair s" by (rule no_echo[OF member]; simp)
    then show False using member by (simp add: pp_view_def)
  qed
qed

lemma fixes_extremes:
  "gi_M5_exotic s {} = {}" "gi_M5_exotic s UNIV = UNIV"
  by (rule set_eqI; simp add: flip_rule pp_view_def pair_nonextreme)+

lemma not_identity:
  "gi_M5_exotic s \<noteq> id"
proof
  assume equality: "gi_M5_exotic s = id"
  have "gi_M5_exotic s s = s" using equality by simp
  then show False using swaps_false pair_distinct by blast
qed

theorem not_truth_uniform:
  "\<not> gi_M5_truth_preserving (gi_M5_exotic s) \<and> \<not> gi_M5_truth_flipping (gi_M5_exotic s)"
proof
  show "\<not> gi_M5_truth_preserving (gi_M5_exotic s)"
    using swaps_false root_false unfolding gi_M5_truth_preserving_def by blast
next
  show "\<not> gi_M5_truth_flipping (gi_M5_exotic s)"
    using fixes_extremes(2) unfolding gi_M5_truth_flipping_def by blast
qed

theorem not_biconditional:
  "\<not> (\<exists>A. gi_M5_exotic s = gi_M5_biconditional_operator A)"
proof
  assume "\<exists>A. gi_M5_exotic s = gi_M5_biconditional_operator A"
  then obtain A where representation: "gi_M5_exotic s = gi_M5_biconditional_operator A" by blast
  have at_top: "gi_M5_biconditional_operator A UNIV = UNIV" using representation fixes_extremes(2) by simp
  have top: "A = UNIV" using at_top by (simp add: gi_M5_biconditional_operator_def)
  have as_id: "gi_M5_biconditional_operator A = id"
    by (rule ext; simp add: top gi_M5_biconditional_operator_def)
  have exotic_id: "gi_M5_exotic s = id" by (rule trans[OF representation as_id])
  show False by (rule notE[OF not_identity exotic_id])
qed

lemma fixes_avoiding_orbit:
  assumes avoids: "gi_M5_pair s \<inter> pp_orbit R = {}"
  shows "gi_M5_exotic s R = R"
proof (rule set_eqI)
  fix i
  have outside: "pp_view i R \<notin> gi_M5_pair s" using avoids unfolding pp_orbit_def by blast
  show "i \<in> gi_M5_exotic s R \<longleftrightarrow> i \<in> R" by (simp add: flip_rule outside)
qed

end

section \<open>The fixed [5] example and the repaired orbit-avoiding pair\<close>

lemma gi_M5_fixed_pair:
  "gi_M5_no_echo_pair {[5]}"
proof
  show "[] \<notin> ({[5]} :: pp_sem_prop)" by simp
  fix Q :: pp_sem_prop and i :: pp_word
  assume "Q \<in> gi_M5_pair {[5]}" "i \<noteq> []"
  then show "pp_view i Q \<notin> gi_M5_pair {[5]}"
    by (auto simp: pp_view_def gi_M5_pair_def)
qed

corollary gi_M5_fixed_exotic_involution:
  "gi_M5_exotic {[5]} (gi_M5_exotic {[5]} P) = P"
  by (rule gi_M5_no_echo_pair.involution[OF gi_M5_fixed_pair])

definition gi_M5_diagonal_selector :: "pp_sem_prop \<Rightarrow> nat set" where
  "gi_M5_diagonal_selector R = insert 0 {n + 2 | n. [n + 2] \<notin> pp_view (from_nat n) R}"

definition gi_M5_diagonal_s :: "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "gi_M5_diagonal_s R = {w. w \<noteq> [] \<and> last w \<in> gi_M5_diagonal_selector R}"

lemma gi_M5_selector_zero:
  "0 \<in> gi_M5_diagonal_selector R"
  by (simp add: gi_M5_diagonal_selector_def)

lemma gi_M5_selector_one:
  "1 \<notin> gi_M5_diagonal_selector R"
  by (auto simp: gi_M5_diagonal_selector_def)

lemma gi_M5_diagonal_singleton:
  "[n + 2] \<in> gi_M5_diagonal_s R \<longleftrightarrow> [n + 2] \<notin> pp_view (from_nat n) R"
  by (auto simp: gi_M5_diagonal_s_def gi_M5_diagonal_selector_def)

lemma gi_M5_diagonal_false:
  "[] \<notin> gi_M5_diagonal_s R"
  by (simp add: gi_M5_diagonal_s_def)

lemma gi_M5_diagonal_nonextreme:
  "gi_M5_diagonal_s R \<noteq> {}" "gi_M5_diagonal_s R \<noteq> UNIV"
  "insert [] (gi_M5_diagonal_s R) \<noteq> {}" "insert [] (gi_M5_diagonal_s R) \<noteq> UNIV"
proof -
  have zero: "[0] \<in> gi_M5_diagonal_s R" by (simp add: gi_M5_diagonal_s_def gi_M5_selector_zero)
  have one: "[1] \<notin> insert [] (gi_M5_diagonal_s R)"
    by (auto simp: gi_M5_diagonal_s_def gi_M5_diagonal_selector_def)
  show "gi_M5_diagonal_s R \<noteq> {}" using zero by blast
  show "gi_M5_diagonal_s R \<noteq> UNIV" using gi_M5_diagonal_false[of R] by blast
  show "insert [] (gi_M5_diagonal_s R) \<noteq> {}" by simp
  show "insert [] (gi_M5_diagonal_s R) \<noteq> UNIV" using one by blast
qed

lemma gi_M5_diagonal_avoids_view:
  "gi_M5_diagonal_s R \<noteq> pp_view i R" "insert [] (gi_M5_diagonal_s R) \<noteq> pp_view i R"
proof -
  let ?n = "to_nat i"
  have enumeration: "(from_nat ?n :: pp_word) = i" by simp
  have diagonal: "[?n + 2] \<in> gi_M5_diagonal_s R \<longleftrightarrow> [?n + 2] \<notin> pp_view i R"
    using gi_M5_diagonal_singleton[of ?n R] enumeration by simp
  show "gi_M5_diagonal_s R \<noteq> pp_view i R" using diagonal by blast
  have diagonal': "[?n + 2] \<in> insert [] (gi_M5_diagonal_s R) \<longleftrightarrow> [?n + 2] \<notin> pp_view i R"
    using diagonal by simp
  show "insert [] (gi_M5_diagonal_s R) \<noteq> pp_view i R" using diagonal' by blast
qed

theorem gi_M5_diagonal_pair_avoids_orbit:
  "gi_M5_pair (gi_M5_diagonal_s R) \<inter> pp_orbit R = {}"
  unfolding gi_M5_pair_def pp_orbit_def using gi_M5_diagonal_avoids_view[of R] by blast

lemma gi_M5_diagonal_view:
  assumes nonroot: "i \<noteq> []"
  shows "pp_view i (gi_M5_diagonal_s R) = (if last i \<in> gi_M5_diagonal_selector R then UNIV else {})"
  using nonroot by (auto simp: pp_view_def gi_M5_diagonal_s_def last_append)

lemma gi_M5_insert_root_view:
  "i \<noteq> [] \<Longrightarrow> pp_view i (insert [] P) = pp_view i P"
  by (auto simp: pp_view_def)

theorem gi_M5_diagonal_no_echo_pair:
  "gi_M5_no_echo_pair (gi_M5_diagonal_s R)"
proof
  show "[] \<notin> gi_M5_diagonal_s R" by (rule gi_M5_diagonal_false)
  fix Q :: pp_sem_prop and i :: pp_word
  assume member: "Q \<in> gi_M5_pair (gi_M5_diagonal_s R)" and nonroot: "i \<noteq> []"
  have extreme: "pp_view i Q = {} \<or> pp_view i Q = UNIV"
    using member gi_M5_diagonal_view[OF nonroot, of R] gi_M5_insert_root_view[OF nonroot, of "gi_M5_diagonal_s R"]
    unfolding gi_M5_pair_def by (auto split: if_splits)
  show "pp_view i Q \<notin> gi_M5_pair (gi_M5_diagonal_s R)"
    using extreme gi_M5_diagonal_nonextreme[of R] unfolding gi_M5_pair_def by blast
qed

definition gi_M5_repaired_exotic :: "pp_sem_prop \<Rightarrow> pp_e_operator" where
  "gi_M5_repaired_exotic R = gi_M5_exotic (gi_M5_diagonal_s R)"

theorem gi_M5_repaired_exotic_involution:
  "gi_M5_repaired_exotic R (gi_M5_repaired_exotic R P) = P"
  unfolding gi_M5_repaired_exotic_def by (rule gi_M5_no_echo_pair.involution[OF gi_M5_diagonal_no_echo_pair])

theorem gi_M5_repaired_exotic_equivariant:
  "pp_equivariant_operator (gi_M5_repaired_exotic R)"
  unfolding gi_M5_repaired_exotic_def by (rule gi_M5_exotic_equivariant)

theorem gi_M5_repaired_exotic_bijective:
  "bij (gi_M5_repaired_exotic R)"
  unfolding gi_M5_repaired_exotic_def by (rule gi_M5_no_echo_pair.bijective[OF gi_M5_diagonal_no_echo_pair])

lemma gi_M5_repaired_exotic_swaps:
  "gi_M5_repaired_exotic R (gi_M5_diagonal_s R) = insert [] (gi_M5_diagonal_s R)"
  "gi_M5_repaired_exotic R (insert [] (gi_M5_diagonal_s R)) = gi_M5_diagonal_s R"
  unfolding gi_M5_repaired_exotic_def
  by (rule gi_M5_no_echo_pair.swaps_false[OF gi_M5_diagonal_no_echo_pair]
    | rule gi_M5_no_echo_pair.swaps_true[OF gi_M5_diagonal_no_echo_pair])+

theorem gi_M5_repaired_exotic_fixes_R:
  "gi_M5_repaired_exotic R R = R"
  unfolding gi_M5_repaired_exotic_def
  by (rule gi_M5_no_echo_pair.fixes_avoiding_orbit[OF gi_M5_diagonal_no_echo_pair gi_M5_diagonal_pair_avoids_orbit])

theorem gi_M5_repaired_exotic_not_identity:
  "gi_M5_repaired_exotic R \<noteq> id"
  unfolding gi_M5_repaired_exotic_def by (rule gi_M5_no_echo_pair.not_identity[OF gi_M5_diagonal_no_echo_pair])

theorem gi_M5_repaired_exotic_not_truth_uniform:
  "\<not> gi_M5_truth_preserving (gi_M5_repaired_exotic R) \<and> \<not> gi_M5_truth_flipping (gi_M5_repaired_exotic R)"
  unfolding gi_M5_repaired_exotic_def by (rule gi_M5_no_echo_pair.not_truth_uniform[OF gi_M5_diagonal_no_echo_pair])

theorem gi_M5_repaired_exotic_not_biconditional:
  "\<not> (\<exists>A. gi_M5_repaired_exotic R = gi_M5_biconditional_operator A)"
  unfolding gi_M5_repaired_exotic_def by (rule gi_M5_no_echo_pair.not_biconditional[OF gi_M5_diagonal_no_echo_pair])

theorem gi_M5_old_seed_QSS_obstruction:
  assumes exotic: "gi_M5_repaired_exotic R \<in> S" and identity: "id \<in> S"
  shows "\<not> gi_stock_fun_prime S R"
proof
  assume fp: "gi_stock_fun_prime S R"
  have collision: "gi_M5_repaired_exotic R R = id R" by (simp add: gi_M5_repaired_exotic_fixes_R)
  have "gi_M5_repaired_exotic R = id" using fp exotic identity collision unfolding gi_stock_fun_prime_def by blast
  then show False using gi_M5_repaired_exotic_not_identity[of R] by contradiction
qed

section \<open>The exotic value belongs to Bacon's exact carrier\<close>

definition gi_exact_M5_exotic :: "pp_sem_prop \<Rightarrow> ZF" where
  "gi_exact_M5_exotic R = gi_exact_M2_classifier (gi_M5_swapped_index (gi_M5_diagonal_s R))"

theorem gi_exact_M5_exotic_member:
  "Elem (gi_exact_M5_exotic R) (pp_e_domain gb_unary)"
  unfolding gi_exact_M5_exotic_def by (rule gi_exact_M2_classifier_member)

theorem gi_exact_M5_exotic_invariant:
  "pp_b_action gb_unary i (gi_exact_M5_exotic R) = gi_exact_M5_exotic R"
  unfolding gi_exact_M5_exotic_def by (rule gi_exact_M2_classifier_invariant)

theorem gi_exact_M5_exotic_raw:
  "pp_e_raw_operator (gi_exact_M5_exotic R) = gi_M5_repaired_exotic R"
  by (simp only: gi_exact_M5_exotic_def gi_exact_M2_classifier_raw gi_M5_repaired_exotic_def gi_M5_exotic_def)

lemma gi_exact_M5_application_extract:
  assumes pm: "Elem p (pp_e_domain Prop)"
  shows "pp_n_bacon_extract (gi_exact_M5_exotic R \<acute> p) = gi_M5_repaired_exotic R (pp_n_bacon_extract p)"
  using gi_exact_raw_at_extract[OF pm, where X="gi_exact_M5_exotic R"]
  by (simp only: gi_exact_M5_exotic_raw)

theorem gi_exact_M5_exotic_involution:
  assumes pm: "Elem p (pp_e_domain Prop)"
  shows "gi_exact_M5_exotic R \<acute> (gi_exact_M5_exotic R \<acute> p) = p"
proof -
  have kp: "Elem (gi_exact_M5_exotic R \<acute> p) (pp_e_domain Prop)"
    by (rule pp_e_app_closed[OF gi_exact_M5_exotic_member pm])
  have kkp: "Elem (gi_exact_M5_exotic R \<acute> (gi_exact_M5_exotic R \<acute> p)) (pp_e_domain Prop)"
    by (rule pp_e_app_closed[OF gi_exact_M5_exotic_member kp])
  have extracted: "pp_n_bacon_extract (gi_exact_M5_exotic R \<acute> (gi_exact_M5_exotic R \<acute> p)) = pp_n_bacon_extract p"
    by (simp only: gi_exact_M5_application_extract[OF kp] gi_exact_M5_application_extract[OF pm]
      gi_M5_repaired_exotic_involution)
  have power1: "Elem (gi_exact_M5_exotic R \<acute> (gi_exact_M5_exotic R \<acute> p)) (Power Nat)"
    using kkp by simp
  have power2: "Elem p (Power Nat)" using pm by simp
  show ?thesis by (rule pp_n_bacon_extract_injective_on_domain[OF power1 power2 extracted])
qed

lemma gi_exact_M5_application_root:
  "pp_e_holds (gi_exact_M5_exotic R \<acute> pp_n_bacon_embed P) [] \<longleftrightarrow> [] \<in> gi_M5_repaired_exotic R P"
proof -
  have pm: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)" using pp_n_bacon_embed_in_domain[of P] by simp
  have extracted: "pp_n_bacon_extract (gi_exact_M5_exotic R \<acute> pp_n_bacon_embed P) = gi_M5_repaired_exotic R P"
    using gi_exact_M5_application_extract[OF pm, where R=R] by simp
  have at_root: "([] \<in> pp_n_bacon_extract (gi_exact_M5_exotic R \<acute> pp_n_bacon_embed P)) =
    ([] \<in> gi_M5_repaired_exotic R P)"
    by (rule arg_cong[OF extracted, where f="\<lambda>Q. [] \<in> Q"])
  show ?thesis using at_root by (simp add: pp_n_bacon_extract_def)
qed

theorem gi_exact_M5_exotic_not_truth_uniform:
  "\<not> (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
      (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> pp_e_holds p []))
    \<and> \<not> (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
      (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> \<not> pp_e_holds p []))"
proof
  have members: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)" for P
    using pp_n_bacon_embed_in_domain[of P] by simp
  show "\<not> (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
    (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> pp_e_holds p []))"
  proof
    assume preserving: "\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
      (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> pp_e_holds p [])"
    have raw_preserving: "gi_M5_truth_preserving (gi_M5_repaired_exotic R)"
    proof (unfold gi_M5_truth_preserving_def, intro allI)
      fix P
      have preserving_at_input: "pp_e_holds (gi_exact_M5_exotic R \<acute> pp_n_bacon_embed P) [] \<longleftrightarrow>
        pp_e_holds (pp_n_bacon_embed P) []" using preserving members[of P] by blast
      show "([] \<in> gi_M5_repaired_exotic R P) = ([] \<in> P)"
        using preserving_at_input by (simp only: gi_exact_M5_application_root; simp)
    qed
    show False using raw_preserving gi_M5_repaired_exotic_not_truth_uniform[of R] by blast
  qed
next
  have members: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)" for P
    using pp_n_bacon_embed_in_domain[of P] by simp
  show "\<not> (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
    (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> \<not> pp_e_holds p []))"
  proof
    assume flipping: "\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow>
      (pp_e_holds (gi_exact_M5_exotic R \<acute> p) [] \<longleftrightarrow> \<not> pp_e_holds p [])"
    have raw_flipping: "gi_M5_truth_flipping (gi_M5_repaired_exotic R)"
    proof (unfold gi_M5_truth_flipping_def, intro allI)
      fix P
      have flipping_at_input: "pp_e_holds (gi_exact_M5_exotic R \<acute> pp_n_bacon_embed P) [] \<longleftrightarrow>
        \<not> pp_e_holds (pp_n_bacon_embed P) []" using flipping members[of P] by blast
      show "([] \<in> gi_M5_repaired_exotic R P) = ([] \<notin> P)"
        using flipping_at_input by (simp only: gi_exact_M5_application_root; simp)
    qed
    show False using raw_flipping gi_M5_repaired_exotic_not_truth_uniform[of R] by blast
  qed
qed

theorem gi_exact_M5_old_seed_collision:
  "gi_exact_M5_exotic R \<noteq> pp_e_closed_den pp_identity_operator \<and>
    gi_exact_M5_exotic R \<acute> pp_n_bacon_embed R = pp_e_closed_den pp_identity_operator \<acute> pp_n_bacon_embed R"
proof -
  have pm: "Elem (pp_n_bacon_embed R) (pp_e_domain Prop)" using pp_n_bacon_embed_in_domain[of R] by simp
  have im: "Elem (pp_e_closed_den pp_identity_operator) (pp_e_domain gb_unary)"
    by (rule pp_e_closed_den_in_domain[OF typed_pp_identity_operator[unfolded pp_unary_ty_def]])
  have raw_same: "pp_e_raw_operator (gi_exact_M5_exotic R) R = pp_e_raw_operator (pp_e_closed_den pp_identity_operator) R"
    by (simp only: gi_exact_M5_exotic_raw pp_e_raw_operator_identity gi_M5_repaired_exotic_fixes_R id_apply)
  have same: "gi_exact_M5_exotic R \<acute> pp_n_bacon_embed R = pp_e_closed_den pp_identity_operator \<acute> pp_n_bacon_embed R"
    using raw_same
    by (simp only: gi_exact_raw_application_eq_iff[OF gi_exact_M5_exotic_member im pm pm, simplified])
  have distinct: "gi_exact_M5_exotic R \<noteq> pp_e_closed_den pp_identity_operator"
  proof
    assume equal: "gi_exact_M5_exotic R = pp_e_closed_den pp_identity_operator"
    have "gi_M5_repaired_exotic R = id"
      using arg_cong[OF equal, of pp_e_raw_operator] by (simp only: gi_exact_M5_exotic_raw pp_e_raw_operator_identity)
    then show False using gi_M5_repaired_exotic_not_identity[of R] by contradiction
  qed
  show ?thesis by (rule conjI[OF distinct same])
qed

corollary gi_exact_M5_exotic_fixes_seed:
  "gi_exact_M5_exotic R \<acute> pp_n_bacon_embed R = pp_n_bacon_embed R"
proof -
  have same: "gi_exact_M5_exotic R \<acute> pp_n_bacon_embed R =
    pp_e_closed_den pp_identity_operator \<acute> pp_n_bacon_embed R"
    using gi_exact_M5_old_seed_collision[of R] by blast
  have pm: "Elem (pp_n_bacon_embed R) (pp_e_domain Prop)" using pp_n_bacon_embed_in_domain[of R] by simp
  show ?thesis using same pm by (simp add: pp_e_closed_den_def pp_identity_operator_def Lambda_app)
qed

text \<open>
  The fixed pair {[5]}, {[],[5]} certifies an exotic involution, but is not
  claimed to avoid every proposed R-orbit. The repaired pair depends on R;
  a direct diagonal supplies avoidance rather than a countability argument
  over only countably many singleton pairs. Its classifier fixes R and
  differs from identity, so retaining R after declaring this operator pure
  destroys evaluation injectivity.

  The final results concern an actual invariant value in Bacon's exact
  recursively restricted unary carrier. Involution and failure of truth
  uniformity are proved there, not merely in a secondary tree. Membership
  in a Pure stock, a rebuilt-model theorem, and PP remain separate tasks;
  no such membership or consistency is asserted here.
\<close>

end
