theory Goodman_T9_Root_Algebra
  imports Goodman_T9_Native_Purity
    Goodman_Integration_Exact_L2.Goodman_Exact_L2_Root_Semantics
begin

section \<open>Actual exact unary values, not abstract counting parameters\<close>

definition gi_T9_identity :: ZF where
  "gi_T9_identity = pp_e_closed_den pp_identity_operator"

definition gi_T9_compose_builder :: oterm where
  "gi_T9_compose_builder = Lam gb_unary (Lam gb_unary
    (Lam Prop (App (Var 2) (App (Var 1) (Var 0)))))"

definition gi_T9_root_group where
  "gi_T9_root_group C = {Z\<in>gi_T9_root_pure C gb_unary.
    \<exists>W\<in>gi_T9_root_pure C gb_unary.
      gi_exact_value_compose Z W = gi_T9_identity \<and>
      gi_exact_value_compose W Z = gi_T9_identity}"

definition gi_T9_same_kind where
  "gi_T9_same_kind C X Y \<longleftrightarrow>
    (\<exists>Z\<in>gi_T9_root_group C. X = gi_exact_value_compose Y Z)"

definition gi_T9_kind where
  "gi_T9_kind C X = {Y\<in>gi_T9_root_pure C gb_unary. gi_T9_same_kind C X Y}"

definition gi_T9_kinds where
  "gi_T9_kinds C = gi_T9_kind C ` gi_T9_root_pure C gb_unary"

definition gi_T9_kind_rep where
  "gi_T9_kind_rep C k = (SOME X. X \<in> gi_T9_root_pure C gb_unary \<and> gi_T9_kind C X = k)"

definition gi_T9_kind_code where
  "gi_T9_kind_code C k X = (SOME Z. Z \<in> gi_T9_root_group C \<and>
    gi_exact_value_compose (gi_T9_kind_rep C k) Z = X)"

lemma gi_T9_compose_builder_type:
  "[] \<turnstile> gi_T9_compose_builder : Arr gb_unary (Arr gb_unary gb_unary)"
  by (rule infer_type_sound; simp add: gi_T9_compose_builder_def lookup_def)

lemma gi_T9_compose_builder_logical:
  "pp_logical_vocabulary gi_T9_compose_builder"
  by (simp add: gi_T9_compose_builder_def pp_logical_vocabulary_def)

lemma gi_T9_compose_builder_apply:
  assumes xm: "Elem X (pp_e_domain gb_unary)" and ym: "Elem Y (pp_e_domain gb_unary)"
  shows "(pp_e_closed_den gi_T9_compose_builder \<acute> X) \<acute> Y = gi_exact_value_compose X Y"
  by (simp only: pp_e_closed_den_def gi_T9_compose_builder_def pp_e_eval.simps
    extend_env.simps numeral_2_eq_2 One_nat_def Lambda_app[OF xm] Lambda_app[OF ym]
    gi_exact_value_compose_def)

lemma gi_T9_value_identity_member:
  "Elem gi_T9_identity (pp_e_domain gb_unary)"
  unfolding gi_T9_identity_def
  by (rule pp_e_closed_den_in_domain[OF typed_pp_identity_operator[unfolded pp_unary_ty_def]])

lemma gi_T9_value_compose_apply:
  assumes pm: "Elem p (pp_e_domain Prop)"
  shows "gi_exact_value_compose X Y \<acute> p = X \<acute> (Y \<acute> p)"
  unfolding gi_exact_value_compose_def by (rule Lambda_app[OF pm])

lemma gi_T9_value_identity_left:
  assumes xm: "Elem X (pp_e_domain gb_unary)"
  shows "gi_exact_value_compose gi_T9_identity X = X"
proof (rule gi_exact_raw_operator_injective[OF gi_exact_value_compose_member[OF gi_T9_value_identity_member xm] xm])
  show "pp_e_raw_operator (gi_exact_value_compose gi_T9_identity X) = pp_e_raw_operator X"
    by (simp only: gi_exact_raw_value_compose[OF gi_T9_value_identity_member xm];
      simp add: gi_T9_identity_def pp_e_raw_operator_identity)
qed

lemma gi_T9_value_identity_right:
  assumes xm: "Elem X (pp_e_domain gb_unary)"
  shows "gi_exact_value_compose X gi_T9_identity = X"
proof (rule gi_exact_raw_operator_injective[OF gi_exact_value_compose_member[OF xm gi_T9_value_identity_member] xm])
  show "pp_e_raw_operator (gi_exact_value_compose X gi_T9_identity) = pp_e_raw_operator X"
    by (simp only: gi_exact_raw_value_compose[OF xm gi_T9_value_identity_member];
      simp add: gi_T9_identity_def pp_e_raw_operator_identity)
qed

lemma gi_T9_value_compose_associative:
  assumes xm: "Elem X (pp_e_domain gb_unary)" and ym: "Elem Y (pp_e_domain gb_unary)"
    and zm: "Elem Z (pp_e_domain gb_unary)"
  shows "gi_exact_value_compose X (gi_exact_value_compose Y Z) =
    gi_exact_value_compose (gi_exact_value_compose X Y) Z"
proof -
  have xy: "Elem (gi_exact_value_compose X Y) (pp_e_domain gb_unary)" by (rule gi_exact_value_compose_member[OF xm ym])
  have yz: "Elem (gi_exact_value_compose Y Z) (pp_e_domain gb_unary)" by (rule gi_exact_value_compose_member[OF ym zm])
  show ?thesis
  proof (rule gi_exact_raw_operator_injective[OF gi_exact_value_compose_member[OF xm yz]
      gi_exact_value_compose_member[OF xy zm]])
    show "pp_e_raw_operator (gi_exact_value_compose X (gi_exact_value_compose Y Z)) =
      pp_e_raw_operator (gi_exact_value_compose (gi_exact_value_compose X Y) Z)"
      by (simp only: gi_exact_raw_value_compose[OF xm yz] gi_exact_raw_value_compose[OF xy zm]
        gi_exact_raw_value_compose[OF xm ym] gi_exact_raw_value_compose[OF ym zm] comp_assoc)
  qed
qed

context gi_T9_native_purity
begin

lemma gi_T9_root_pure_member:
  "X \<in> gi_T9_root_pure C \<sigma> \<Longrightarrow> Elem X (pp_e_domain \<sigma>)"
  unfolding gi_T9_root_pure_def by blast

theorem gi_T9_compose_pure:
  assumes xp: "X \<in> gi_T9_root_pure C gb_unary" and yp: "Y \<in> gi_T9_root_pure C gb_unary"
  shows "gi_exact_value_compose X Y \<in> gi_T9_root_pure C gb_unary"
proof -
  have builder: "pp_e_closed_den gi_T9_compose_builder \<in>
    gi_T9_root_pure C (Arr gb_unary (Arr gb_unary gb_unary))"
    by (rule gi_T9_closed_logical_value_pure[OF gi_T9_compose_builder_type gi_T9_compose_builder_logical])
  have first: "pp_e_closed_den gi_T9_compose_builder \<acute> X \<in> gi_T9_root_pure C (Arr gb_unary gb_unary)"
    by (rule gi_T9_root_application_closed[OF builder xp])
  have second: "(pp_e_closed_den gi_T9_compose_builder \<acute> X) \<acute> Y \<in> gi_T9_root_pure C gb_unary"
    by (rule gi_T9_root_application_closed[OF first yp])
  show ?thesis using second by (simp only: gi_T9_compose_builder_apply[
    OF gi_T9_root_pure_member[OF xp] gi_T9_root_pure_member[OF yp]])
qed

lemma gi_T9_identity_pure:
  "gi_T9_identity \<in> gi_T9_root_pure C gb_unary"
  unfolding gi_T9_identity_def
  by (rule gi_T9_closed_logical_value_pure[OF typed_pp_identity_operator[unfolded pp_unary_ty_def]];
    simp add: pp_logical_vocabulary_def pp_identity_operator_def)

lemma gi_T9_identity_left:
  "X \<in> gi_T9_root_pure C gb_unary \<Longrightarrow> gi_exact_value_compose gi_T9_identity X = X"
  by (rule gi_T9_value_identity_left, rule gi_T9_root_pure_member; assumption)

lemma gi_T9_identity_right:
  "X \<in> gi_T9_root_pure C gb_unary \<Longrightarrow> gi_exact_value_compose X gi_T9_identity = X"
  by (rule gi_T9_value_identity_right, rule gi_T9_root_pure_member; assumption)

lemma gi_T9_compose_associative:
  "X \<in> gi_T9_root_pure C gb_unary \<Longrightarrow> Y \<in> gi_T9_root_pure C gb_unary \<Longrightarrow>
    Z \<in> gi_T9_root_pure C gb_unary \<Longrightarrow>
    gi_exact_value_compose X (gi_exact_value_compose Y Z) =
      gi_exact_value_compose (gi_exact_value_compose X Y) Z"
  by (rule gi_T9_value_compose_associative; rule gi_T9_root_pure_member; assumption)

lemma gi_T9_group_pure:
  "Z \<in> gi_T9_root_group C \<Longrightarrow> Z \<in> gi_T9_root_pure C gb_unary"
  unfolding gi_T9_root_group_def by blast

lemma gi_T9_identity_in_group:
  "gi_T9_identity \<in> gi_T9_root_group C"
  unfolding gi_T9_root_group_def
  using gi_T9_identity_pure gi_T9_identity_left[OF gi_T9_identity_pure] by blast

theorem gi_T9_group_inverse:
  assumes member: "Z \<in> gi_T9_root_group C"
  obtains W where "W \<in> gi_T9_root_group C"
    "gi_exact_value_compose Z W = gi_T9_identity" "gi_exact_value_compose W Z = gi_T9_identity"
proof -
  obtain W where zp: "Z \<in> gi_T9_root_pure C gb_unary" and wp: "W \<in> gi_T9_root_pure C gb_unary"
    and zw: "gi_exact_value_compose Z W = gi_T9_identity" and wz: "gi_exact_value_compose W Z = gi_T9_identity"
    using member unfolding gi_T9_root_group_def by blast
  have wg: "W \<in> gi_T9_root_group C" unfolding gi_T9_root_group_def using wp zp zw wz by blast
  show thesis by (rule that[OF wg zw wz])
qed

theorem gi_T9_group_compose:
  assumes zg: "Z \<in> gi_T9_root_group C" and wg: "W \<in> gi_T9_root_group C"
  shows "gi_exact_value_compose Z W \<in> gi_T9_root_group C"
proof -
  obtain I where ig: "I \<in> gi_T9_root_group C" and zi: "gi_exact_value_compose Z I = gi_T9_identity"
    and iz: "gi_exact_value_compose I Z = gi_T9_identity" by (rule gi_T9_group_inverse[OF zg])
  obtain J where jg: "J \<in> gi_T9_root_group C" and wj: "gi_exact_value_compose W J = gi_T9_identity"
    and jw: "gi_exact_value_compose J W = gi_T9_identity" by (rule gi_T9_group_inverse[OF wg])
  have zp: "Z \<in> gi_T9_root_pure C gb_unary" and wp: "W \<in> gi_T9_root_pure C gb_unary"
    and ip: "I \<in> gi_T9_root_pure C gb_unary" and jp: "J \<in> gi_T9_root_pure C gb_unary"
    using gi_T9_group_pure[OF zg] gi_T9_group_pure[OF wg] gi_T9_group_pure[OF ig] gi_T9_group_pure[OF jg] by blast+
  have zwp: "gi_exact_value_compose Z W \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_compose_pure[OF zp wp])
  have jip: "gi_exact_value_compose J I \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_compose_pure[OF jp ip])
  have left: "gi_exact_value_compose (gi_exact_value_compose Z W) (gi_exact_value_compose J I) = gi_T9_identity"
  proof -
    have "gi_exact_value_compose (gi_exact_value_compose Z W) (gi_exact_value_compose J I) =
      gi_exact_value_compose Z (gi_exact_value_compose W (gi_exact_value_compose J I))"
      by (rule gi_T9_compose_associative[OF zp wp jip, symmetric])
    also have "... = gi_exact_value_compose Z (gi_exact_value_compose (gi_exact_value_compose W J) I)"
      by (simp only: gi_T9_compose_associative[OF wp jp ip])
    also have "... = gi_T9_identity" by (simp only: wj gi_T9_identity_left[OF ip] zi)
    finally show ?thesis .
  qed
  have right: "gi_exact_value_compose (gi_exact_value_compose J I) (gi_exact_value_compose Z W) = gi_T9_identity"
  proof -
    have "gi_exact_value_compose (gi_exact_value_compose J I) (gi_exact_value_compose Z W) =
      gi_exact_value_compose J (gi_exact_value_compose I (gi_exact_value_compose Z W))"
      by (rule gi_T9_compose_associative[OF jp ip zwp, symmetric])
    also have "... = gi_exact_value_compose J (gi_exact_value_compose (gi_exact_value_compose I Z) W)"
      by (simp only: gi_T9_compose_associative[OF ip zp wp])
    also have "... = gi_T9_identity" by (simp only: iz gi_T9_identity_left[OF wp] jw)
    finally show ?thesis .
  qed
  show ?thesis unfolding gi_T9_root_group_def using zwp jip left right by blast
qed

theorem gi_T9_group_inverse_action:
  assumes zg: "Z \<in> gi_T9_root_group C"
  shows "\<exists>I\<in>gi_T9_root_group C. \<forall>X\<in>gi_T9_root_pure C gb_unary.
    gi_exact_value_compose I (gi_exact_value_compose Z X) = X \<and>
    gi_exact_value_compose Z (gi_exact_value_compose I X) = X"
proof -
  obtain I where ig: "I \<in> gi_T9_root_group C" and zi: "gi_exact_value_compose Z I = gi_T9_identity"
    and iz: "gi_exact_value_compose I Z = gi_T9_identity" by (rule gi_T9_group_inverse[OF zg])
  have zp: "Z \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_group_pure[OF zg])
  have ip: "I \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_group_pure[OF ig])
  have cancel: "gi_exact_value_compose I (gi_exact_value_compose Z X) = X \<and>
    gi_exact_value_compose Z (gi_exact_value_compose I X) = X"
    if xp: "X \<in> gi_T9_root_pure C gb_unary" for X
    by (simp only: gi_T9_compose_associative[OF ip zp xp] gi_T9_compose_associative[OF zp ip xp]
      iz zi gi_T9_identity_left[OF xp])
  show ?thesis using ig cancel by blast
qed

section \<open>The right-composition equivalence relation\<close>

lemma gi_T9_same_kind_refl:
  assumes xp: "X \<in> gi_T9_root_pure C gb_unary"
  shows "gi_T9_same_kind C X X"
  unfolding gi_T9_same_kind_def
  by (rule bexI[where x=gi_T9_identity])
    (rule gi_T9_identity_right[OF xp, symmetric], rule gi_T9_identity_in_group)

lemma gi_T9_same_kind_sym:
  assumes xp: "X \<in> gi_T9_root_pure C gb_unary" and yp: "Y \<in> gi_T9_root_pure C gb_unary"
    and same: "gi_T9_same_kind C X Y"
  shows "gi_T9_same_kind C Y X"
proof -
  obtain Z where zg: "Z \<in> gi_T9_root_group C" and x: "X = gi_exact_value_compose Y Z"
    using same unfolding gi_T9_same_kind_def by blast
  obtain I where ig: "I \<in> gi_T9_root_group C" and zi: "gi_exact_value_compose Z I = gi_T9_identity"
    and iz: "gi_exact_value_compose I Z = gi_T9_identity" by (rule gi_T9_group_inverse[OF zg])
  have zp: "Z \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_group_pure[OF zg])
  have ip: "I \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_group_pure[OF ig])
  have recovers: "gi_exact_value_compose X I = Y"
  proof -
    have "gi_exact_value_compose X I = gi_exact_value_compose Y (gi_exact_value_compose Z I)"
      by (simp only: x gi_T9_compose_associative[OF yp zp ip])
    also have "... = Y" by (simp only: zi gi_T9_identity_right[OF yp])
    finally show ?thesis .
  qed
  show ?thesis unfolding gi_T9_same_kind_def using ig recovers by blast
qed

lemma gi_T9_same_kind_trans:
  assumes xp: "X \<in> gi_T9_root_pure C gb_unary" and yp: "Y \<in> gi_T9_root_pure C gb_unary"
    and zp: "Z \<in> gi_T9_root_pure C gb_unary"
    and xy: "gi_T9_same_kind C X Y" and yz: "gi_T9_same_kind C Y Z"
  shows "gi_T9_same_kind C X Z"
proof -
  obtain A where ag: "A \<in> gi_T9_root_group C" and x: "X = gi_exact_value_compose Y A"
    using xy unfolding gi_T9_same_kind_def by blast
  obtain B where bg: "B \<in> gi_T9_root_group C" and y: "Y = gi_exact_value_compose Z B"
    using yz unfolding gi_T9_same_kind_def by blast
  have ap: "A \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_group_pure[OF ag])
  have bp: "B \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_group_pure[OF bg])
  have product: "gi_exact_value_compose B A \<in> gi_T9_root_group C" by (rule gi_T9_group_compose[OF bg ag])
  have composed: "X = gi_exact_value_compose Z (gi_exact_value_compose B A)"
    by (simp only: x y gi_T9_compose_associative[OF zp bp ap])
  show ?thesis unfolding gi_T9_same_kind_def using product composed by blast
qed

lemma gi_T9_kind_self_member:
  "X \<in> gi_T9_root_pure C gb_unary \<Longrightarrow> X \<in> gi_T9_kind C X"
  using gi_T9_same_kind_refl unfolding gi_T9_kind_def by blast

theorem gi_T9_kind_eq_iff:
  assumes xp: "X \<in> gi_T9_root_pure C gb_unary" and yp: "Y \<in> gi_T9_root_pure C gb_unary"
  shows "gi_T9_kind C X = gi_T9_kind C Y \<longleftrightarrow> gi_T9_same_kind C X Y"
proof
  assume equal: "gi_T9_kind C X = gi_T9_kind C Y"
  have "Y \<in> gi_T9_kind C X" using gi_T9_kind_self_member[OF yp] by (simp only: equal)
  then show "gi_T9_same_kind C X Y" unfolding gi_T9_kind_def by simp
next
  assume xy: "gi_T9_same_kind C X Y"
  have yx: "gi_T9_same_kind C Y X" by (rule gi_T9_same_kind_sym[OF xp yp xy])
  show "gi_T9_kind C X = gi_T9_kind C Y"
  proof (rule set_eqI)
    fix Z
    show "Z \<in> gi_T9_kind C X \<longleftrightarrow> Z \<in> gi_T9_kind C Y"
    proof
      assume member: "Z \<in> gi_T9_kind C X"
      then have zp: "Z \<in> gi_T9_root_pure C gb_unary" and xz: "gi_T9_same_kind C X Z"
        unfolding gi_T9_kind_def by auto
      have yz: "gi_T9_same_kind C Y Z" by (rule gi_T9_same_kind_trans[OF yp xp zp yx xz])
      show "Z \<in> gi_T9_kind C Y" unfolding gi_T9_kind_def using zp yz by simp
    next
      assume member: "Z \<in> gi_T9_kind C Y"
      then have zp: "Z \<in> gi_T9_root_pure C gb_unary" and yz: "gi_T9_same_kind C Y Z"
        unfolding gi_T9_kind_def by auto
      have xz: "gi_T9_same_kind C X Z" by (rule gi_T9_same_kind_trans[OF xp yp zp xy yz])
      show "Z \<in> gi_T9_kind C X" unfolding gi_T9_kind_def using zp xz by simp
    qed
  qed
qed

section \<open>Actual kind representatives and the fibre-to-group coding premise\<close>

lemma gi_T9_kind_closed:
  "gi_T9_kind C ` gi_T9_root_pure C gb_unary \<subseteq> gi_T9_kinds C"
  by (simp only: gi_T9_kinds_def subset_refl)

lemma gi_T9_kind_represented:
  "k \<in> gi_T9_kinds C \<Longrightarrow> \<exists>X\<in>gi_T9_root_pure C gb_unary. gi_T9_kind C X = k"
  unfolding gi_T9_kinds_def by blast

lemma gi_T9_kind_rep_spec:
  assumes kind: "k \<in> gi_T9_kinds C"
  shows "gi_T9_kind_rep C k \<in> gi_T9_root_pure C gb_unary \<and> gi_T9_kind C (gi_T9_kind_rep C k) = k"
proof -
  have witness: "\<exists>X. X \<in> gi_T9_root_pure C gb_unary \<and> gi_T9_kind C X = k"
    using gi_T9_kind_represented[OF kind] by blast
  show ?thesis unfolding gi_T9_kind_rep_def by (rule someI_ex[OF witness])
qed

theorem gi_T9_kind_fibre_orbit:
  assumes kind: "k \<in> gi_T9_kinds C" and xp: "X \<in> gi_T9_root_pure C gb_unary"
    and xk: "gi_T9_kind C X = k"
  shows "\<exists>Z\<in>gi_T9_root_group C. X = gi_exact_value_compose (gi_T9_kind_rep C k) Z"
proof -
  have rp: "gi_T9_kind_rep C k \<in> gi_T9_root_pure C gb_unary"
    and rk: "gi_T9_kind C (gi_T9_kind_rep C k) = k"
    using gi_T9_kind_rep_spec[OF kind] by blast+
  have equal: "gi_T9_kind C X = gi_T9_kind C (gi_T9_kind_rep C k)" using xk rk by simp
  have same: "gi_T9_same_kind C X (gi_T9_kind_rep C k)"
    using equal by (simp only: gi_T9_kind_eq_iff[OF xp rp])
  show ?thesis using same unfolding gi_T9_same_kind_def .
qed

lemma gi_T9_kind_code_spec:
  assumes kind: "k \<in> gi_T9_kinds C" and xp: "X \<in> gi_T9_root_pure C gb_unary"
    and xk: "gi_T9_kind C X = k"
  shows "gi_T9_kind_code C k X \<in> gi_T9_root_group C \<and>
    gi_exact_value_compose (gi_T9_kind_rep C k) (gi_T9_kind_code C k X) = X"
proof -
  have witness: "\<exists>Z. Z \<in> gi_T9_root_group C \<and> gi_exact_value_compose (gi_T9_kind_rep C k) Z = X"
    using gi_T9_kind_fibre_orbit[OF kind xp xk] by blast
  show ?thesis unfolding gi_T9_kind_code_def by (rule someI_ex[OF witness])
qed

theorem gi_T9_kind_fibre_code:
  assumes kind: "k \<in> gi_T9_kinds C"
  shows "inj_on (gi_T9_kind_code C k) {X\<in>gi_T9_root_pure C gb_unary. gi_T9_kind C X = k}"
    and "gi_T9_kind_code C k ` {X\<in>gi_T9_root_pure C gb_unary. gi_T9_kind C X = k} \<subseteq> gi_T9_root_group C"
proof -
  show "inj_on (gi_T9_kind_code C k) {X\<in>gi_T9_root_pure C gb_unary. gi_T9_kind C X = k}"
  proof (rule inj_onI)
    fix X Y
    assume x: "X \<in> {X\<in>gi_T9_root_pure C gb_unary. gi_T9_kind C X = k}"
      and y: "Y \<in> {X\<in>gi_T9_root_pure C gb_unary. gi_T9_kind C X = k}"
      and same: "gi_T9_kind_code C k X = gi_T9_kind_code C k Y"
    have xp: "X \<in> gi_T9_root_pure C gb_unary" and xk: "gi_T9_kind C X = k" using x by auto
    have yp: "Y \<in> gi_T9_root_pure C gb_unary" and yk: "gi_T9_kind C Y = k" using y by auto
    have xr: "gi_exact_value_compose (gi_T9_kind_rep C k) (gi_T9_kind_code C k X) = X"
      using gi_T9_kind_code_spec[OF kind xp xk] by blast
    have yr: "gi_exact_value_compose (gi_T9_kind_rep C k) (gi_T9_kind_code C k Y) = Y"
      using gi_T9_kind_code_spec[OF kind yp yk] by blast
    show "X = Y" using xr yr same by metis
  qed
  show "gi_T9_kind_code C k ` {X\<in>gi_T9_root_pure C gb_unary. gi_T9_kind C X = k} \<subseteq> gi_T9_root_group C"
  proof
    fix z assume "z \<in> gi_T9_kind_code C k ` {X\<in>gi_T9_root_pure C gb_unary. gi_T9_kind C X = k}"
    then obtain X where xp: "X \<in> gi_T9_root_pure C gb_unary" and xk: "gi_T9_kind C X = k"
      and z: "z = gi_T9_kind_code C k X" by blast
    show "z \<in> gi_T9_root_group C" using gi_T9_kind_code_spec[OF kind xp xk] by (simp only: z; blast)
  qed
qed

end

text \<open>
  Composition closure was obtained from a concrete closed logical builder
  and the actual native application-closure axiom, not postulated for the
  cardinal argument. Kinds are sets of actual root-pure exact unary values.
  The representative code is injective on each fibre without requiring
  the group action to be free. Nothing here assumes PC or L2 or supplies
  the subset-selector injection; those are separate T9 obligations.
\<close>

end
