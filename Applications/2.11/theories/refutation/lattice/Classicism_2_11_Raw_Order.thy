theory Classicism_2_11_Raw_Order
  imports Classicism_2_11_Currents
begin

section \<open>The raw order and emptiness as inclusion of current relations\<close>

text \<open>
  Let τ = σ1→…→σk→t, written paper_type_vector σs Prop. The recursive
  raw order c211_rleq τ w x y holds exactly when, at every world v
  accessible from w, the current relation of the transport of x is
  included in that of y; c211_rempty says that all these current
  relations are empty. Naturality of application and transitivity of
  accessibility drive the induction on σs. At the limit world the
  current relation of a transported root object is the ultralimit of
  its leaf relations over the fixed finite tuple carrier. Consequently
  the root order is the product order on the root, intermediate and
  leaf coordinates; the limit coordinate is determined by the leaves
  and never needs to be compared separately.
\<close>

subsection \<open>Counterpart maps out of the root and the intermediate world\<close>

lemma c211_raw_T_root_middle: "raw_T a raw_root raw_middle X = typed_rs a X"
  by (simp add: raw_T_def)

lemma c211_raw_T_root_limit:
  "raw_T a raw_root raw_limit X = typed_j a (typed_rs a X)"
  by (simp add: raw_T_def)

lemma c211_raw_T_root_leaf: "raw_T a raw_root (raw_leaf n) X = typed_rn a X n"
  by (simp add: raw_T_def)

lemma c211_raw_T_middle_limit: "raw_T a raw_middle raw_limit S = typed_j a S"
  by (simp add: raw_T_def)

lemmas c211_raw_T_worlds = c211_raw_T_root_middle c211_raw_T_root_limit
  c211_raw_T_root_leaf c211_raw_T_middle_limit

subsection \<open>Current relations at a curried arrow type\<close>

lemma c211_rcur_Nil_subset:
  "c211_rcur [] w F \<subseteq> c211_rcur [] w G \<longleftrightarrow> (raw_truth w F \<longrightarrow> raw_truth w G)"
  by (simp add: c211_rcur_Nil)

lemma c211_rcur_Nil_empty: "c211_rcur [] w F = {} \<longleftrightarrow> \<not> raw_truth w F"
  by (simp add: c211_rcur_Nil)

lemma c211_rcur_Cons_cases:
  assumes "zs \<in> c211_rcur (\<sigma> # \<sigma>s) w F"
  obtains x ys where "zs = x # ys"
  using c211_rcur_tuples[of "\<sigma> # \<sigma>s" w F] assms c211_tuples_Cons by blast

lemma c211_rcur_Cons_subset:
  "c211_rcur (\<sigma> # \<sigma>s) w F \<subseteq> c211_rcur (\<sigma> # \<sigma>s) w G \<longleftrightarrow>
    (\<forall>x. Elem x (raw_D \<sigma> w) \<longrightarrow>
      c211_rcur \<sigma>s w (raw_app \<sigma> (paper_type_vector \<sigma>s Prop) w F x) \<subseteq>
      c211_rcur \<sigma>s w (raw_app \<sigma> (paper_type_vector \<sigma>s Prop) w G x))"
  (is "?sub \<longleftrightarrow> ?pt")
proof
  assume sub: ?sub
  show ?pt
  proof (intro allI impI subsetI)
    fix x ys
    assume xm: "Elem x (raw_D \<sigma> w)"
      and ys: "ys \<in> c211_rcur \<sigma>s w (raw_app \<sigma> (paper_type_vector \<sigma>s Prop) w F x)"
    have "x # ys \<in> c211_rcur (\<sigma> # \<sigma>s) w F" using xm ys by (simp only: c211_rcur_Cons)
    then have "x # ys \<in> c211_rcur (\<sigma> # \<sigma>s) w G" using sub by blast
    then show "ys \<in> c211_rcur \<sigma>s w (raw_app \<sigma> (paper_type_vector \<sigma>s Prop) w G x)"
      by (simp only: c211_rcur_Cons)
  qed
next
  assume pt: ?pt
  show ?sub
  proof
    fix zs assume zs: "zs \<in> c211_rcur (\<sigma> # \<sigma>s) w F"
    then obtain x ys where z: "zs = x # ys" by (rule c211_rcur_Cons_cases)
    then show "zs \<in> c211_rcur (\<sigma> # \<sigma>s) w G" using zs pt by (auto simp: c211_rcur_Cons)
  qed
qed

lemma c211_rcur_Cons_empty:
  "c211_rcur (\<sigma> # \<sigma>s) w F = {} \<longleftrightarrow>
    (\<forall>x. Elem x (raw_D \<sigma> w) \<longrightarrow>
      c211_rcur \<sigma>s w (raw_app \<sigma> (paper_type_vector \<sigma>s Prop) w F x) = {})"
  (is "?empty \<longleftrightarrow> ?pt")
proof
  assume empty: ?empty
  show ?pt
  proof (intro allI impI equals0I)
    fix x ys
    assume xm: "Elem x (raw_D \<sigma> w)"
      and ys: "ys \<in> c211_rcur \<sigma>s w (raw_app \<sigma> (paper_type_vector \<sigma>s Prop) w F x)"
    have "x # ys \<in> c211_rcur (\<sigma> # \<sigma>s) w F" using xm ys by (simp only: c211_rcur_Cons)
    then show False using empty by blast
  qed
next
  assume pt: ?pt
  show ?empty
  proof (rule equals0I)
    fix zs assume zs: "zs \<in> c211_rcur (\<sigma> # \<sigma>s) w F"
    then obtain x ys where z: "zs = x # ys" by (rule c211_rcur_Cons_cases)
    then show False using zs pt by (auto simp: c211_rcur_Cons)
  qed
qed

subsection \<open>Naturality along two composable accessibility steps\<close>

lemma c211_app_transport:
  assumes wW: "Elem w raw_W" and vW: "Elem v raw_W" and uW: "Elem u raw_W"
    and wv: "raw_rel w v" and vu: "raw_rel v u"
    and Fm: "Elem F (raw_D (Arr \<sigma> \<rho>) w)" and xm: "Elem x (raw_D \<sigma> v)"
  shows "raw_T \<rho> v u (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v F) x) =
    raw_app \<sigma> \<rho> u (raw_T (Arr \<sigma> \<rho>) w u F) (raw_T \<sigma> v u x)"
proof -
  have Fv: "Elem (raw_T (Arr \<sigma> \<rho>) w v F) (raw_D (Arr \<sigma> \<rho>) v)"
    by (rule raw_T_type[OF wW vW wv Fm])
  have "raw_T \<rho> v u (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v F) x) =
      raw_app \<sigma> \<rho> u (raw_T (Arr \<sigma> \<rho>) v u (raw_T (Arr \<sigma> \<rho>) w v F)) (raw_T \<sigma> v u x)"
    by (rule raw_app_natural[OF vW uW vu Fv xm])
  also have "raw_T (Arr \<sigma> \<rho>) v u (raw_T (Arr \<sigma> \<rho>) w v F) = raw_T (Arr \<sigma> \<rho>) w u F"
    by (rule sym[OF raw_T_compose[OF wW vW uW wv vu]])
  finally show ?thesis .
qed

lemma c211_app_transport_type:
  assumes wW: "Elem w raw_W" and vW: "Elem v raw_W" and wv: "raw_rel w v"
    and Fm: "Elem F (raw_D (Arr \<sigma> \<rho>) w)" and xm: "Elem x (raw_D \<sigma> v)"
  shows "Elem (raw_app \<sigma> \<rho> v (raw_T (Arr \<sigma> \<rho>) w v F) x) (raw_D \<rho> v)"
  by (rule raw_app_type[OF raw_T_type[OF wW vW wv Fm] xm])

text \<open>Quantifying over a first step to v, an argument at v and a second step
  to u is the same as quantifying over one step to u and an argument at u:
  the arguments at u are exactly the transports, with v = u covering all.\<close>

lemma c211_two_step_collapse:
  assumes wW: "Elem w raw_W"
    and nat: "\<And>v u a. Elem v raw_W \<Longrightarrow> Elem u raw_W \<Longrightarrow> raw_rel w v \<Longrightarrow>
      raw_rel v u \<Longrightarrow> Elem a (raw_D \<sigma> v) \<Longrightarrow> Q v a u \<longleftrightarrow> P u (raw_T \<sigma> v u a)"
  shows "(\<forall>v a. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem a (raw_D \<sigma> v) \<longrightarrow>
      (\<forall>u. Elem u raw_W \<longrightarrow> raw_rel v u \<longrightarrow> Q v a u)) \<longleftrightarrow>
    (\<forall>u. Elem u raw_W \<longrightarrow> raw_rel w u \<longrightarrow> (\<forall>a. Elem a (raw_D \<sigma> u) \<longrightarrow> P u a))"
  (is "?two \<longleftrightarrow> ?one")
proof
  assume two: ?two
  show ?one
  proof (intro allI impI)
    fix u a assume uW: "Elem u raw_W" and wu: "raw_rel w u" and am: "Elem a (raw_D \<sigma> u)"
    have "Q u a u" using two uW wu am raw_rel_refl by blast
    then show "P u a" using nat[OF uW uW wu raw_rel_refl am] by (simp only: raw_T_id)
  qed
next
  assume one: ?one
  show ?two
  proof (intro allI impI)
    fix v a u assume vW: "Elem v raw_W" and wv: "raw_rel w v" and am: "Elem a (raw_D \<sigma> v)"
      and uW: "Elem u raw_W" and vu: "raw_rel v u"
    have wu: "raw_rel w u" by (rule raw_rel_trans[OF wv vu])
    have "P u (raw_T \<sigma> v u a)" using one uW wu raw_T_type[OF vW uW vu am] by blast
    then show "Q v a u" using nat[OF vW uW wv vu am] by blast
  qed
qed

subsection \<open>O1: the raw order is inclusion of current relations\<close>

theorem c211_rleq_iff_rcur:
  assumes "Elem w raw_W" "Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
    "Elem y (raw_D (paper_type_vector \<sigma>s Prop) w)"
  shows "c211_rleq (paper_type_vector \<sigma>s Prop) w x y \<longleftrightarrow>
    (\<forall>v. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow>
      c211_rcur \<sigma>s v (raw_T (paper_type_vector \<sigma>s Prop) w v x) \<subseteq>
      c211_rcur \<sigma>s v (raw_T (paper_type_vector \<sigma>s Prop) w v y))"
  using assms
proof (induction \<sigma>s arbitrary: w x y)
  case Nil
  show ?case by (simp add: c211_rcur_Nil_subset)
next
  case (Cons \<sigma> \<sigma>s)
  let ?\<rho> = "paper_type_vector \<sigma>s Prop"
  let ?Fx = "\<lambda>v a. raw_app \<sigma> ?\<rho> v (raw_T (Arr \<sigma> ?\<rho>) w v x) a"
  let ?Fy = "\<lambda>v a. raw_app \<sigma> ?\<rho> v (raw_T (Arr \<sigma> ?\<rho>) w v y) a"
  have wW: "Elem w raw_W" by (rule Cons.prems(1))
  have xm: "Elem x (raw_D (Arr \<sigma> ?\<rho>) w)" and ym: "Elem y (raw_D (Arr \<sigma> ?\<rho>) w)"
    using Cons.prems(2,3) by simp_all
  have nat: "c211_rcur \<sigma>s u (raw_T ?\<rho> v u (?Fx v a)) \<subseteq> c211_rcur \<sigma>s u (raw_T ?\<rho> v u (?Fy v a))
      \<longleftrightarrow> c211_rcur \<sigma>s u (?Fx u (raw_T \<sigma> v u a)) \<subseteq> c211_rcur \<sigma>s u (?Fy u (raw_T \<sigma> v u a))"
    if "Elem v raw_W" "Elem u raw_W" "raw_rel w v" "raw_rel v u" "Elem a (raw_D \<sigma> v)"
    for v u a
    by (simp only: c211_app_transport[OF wW that(1,2,3,4) xm that(5)]
        c211_app_transport[OF wW that(1,2,3,4) ym that(5)])
  have "c211_rleq (Arr \<sigma> ?\<rho>) w x y \<longleftrightarrow>
      (\<forall>v a. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem a (raw_D \<sigma> v) \<longrightarrow>
        c211_rleq ?\<rho> v (?Fx v a) (?Fy v a))"
    by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>v a. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem a (raw_D \<sigma> v) \<longrightarrow>
      (\<forall>u. Elem u raw_W \<longrightarrow> raw_rel v u \<longrightarrow>
        c211_rcur \<sigma>s u (raw_T ?\<rho> v u (?Fx v a)) \<subseteq> c211_rcur \<sigma>s u (raw_T ?\<rho> v u (?Fy v a))))"
    using Cons.IH c211_app_transport_type[OF wW _ _ xm] c211_app_transport_type[OF wW _ _ ym]
    by blast
  also have "\<dots> \<longleftrightarrow> (\<forall>u. Elem u raw_W \<longrightarrow> raw_rel w u \<longrightarrow> (\<forall>a. Elem a (raw_D \<sigma> u) \<longrightarrow>
      c211_rcur \<sigma>s u (?Fx u a) \<subseteq> c211_rcur \<sigma>s u (?Fy u a)))"
    by (rule c211_two_step_collapse[where
        Q="\<lambda>v a u. c211_rcur \<sigma>s u (raw_T ?\<rho> v u (?Fx v a)) \<subseteq>
          c211_rcur \<sigma>s u (raw_T ?\<rho> v u (?Fy v a))"
        and P="\<lambda>u a. c211_rcur \<sigma>s u (?Fx u a) \<subseteq> c211_rcur \<sigma>s u (?Fy u a)",
        OF wW nat])
  also have "\<dots> \<longleftrightarrow> (\<forall>u. Elem u raw_W \<longrightarrow> raw_rel w u \<longrightarrow>
      c211_rcur (\<sigma> # \<sigma>s) u (raw_T (Arr \<sigma> ?\<rho>) w u x) \<subseteq>
      c211_rcur (\<sigma> # \<sigma>s) u (raw_T (Arr \<sigma> ?\<rho>) w u y))"
    by (simp only: c211_rcur_Cons_subset)
  finally show ?case by (simp only: paper_type_vector.simps)
qed

subsection \<open>O2: raw emptiness is emptiness of current relations\<close>

theorem c211_rempty_iff_rcur:
  assumes "Elem w raw_W" "Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
  shows "c211_rempty (paper_type_vector \<sigma>s Prop) w x \<longleftrightarrow>
    (\<forall>v. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow>
      c211_rcur \<sigma>s v (raw_T (paper_type_vector \<sigma>s Prop) w v x) = {})"
  using assms
proof (induction \<sigma>s arbitrary: w x)
  case Nil
  show ?case by (simp add: c211_rcur_Nil_empty)
next
  case (Cons \<sigma> \<sigma>s)
  let ?\<rho> = "paper_type_vector \<sigma>s Prop"
  let ?Fx = "\<lambda>v a. raw_app \<sigma> ?\<rho> v (raw_T (Arr \<sigma> ?\<rho>) w v x) a"
  have wW: "Elem w raw_W" by (rule Cons.prems(1))
  have xm: "Elem x (raw_D (Arr \<sigma> ?\<rho>) w)" using Cons.prems(2) by simp
  have nat: "c211_rcur \<sigma>s u (raw_T ?\<rho> v u (?Fx v a)) = {}
      \<longleftrightarrow> c211_rcur \<sigma>s u (?Fx u (raw_T \<sigma> v u a)) = {}"
    if "Elem v raw_W" "Elem u raw_W" "raw_rel w v" "raw_rel v u" "Elem a (raw_D \<sigma> v)"
    for v u a
    by (simp only: c211_app_transport[OF wW that(1,2,3,4) xm that(5)])
  have "c211_rempty (Arr \<sigma> ?\<rho>) w x \<longleftrightarrow>
      (\<forall>v a. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem a (raw_D \<sigma> v) \<longrightarrow>
        c211_rempty ?\<rho> v (?Fx v a))"
    by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>v a. Elem v raw_W \<longrightarrow> raw_rel w v \<longrightarrow> Elem a (raw_D \<sigma> v) \<longrightarrow>
      (\<forall>u. Elem u raw_W \<longrightarrow> raw_rel v u \<longrightarrow> c211_rcur \<sigma>s u (raw_T ?\<rho> v u (?Fx v a)) = {}))"
    using Cons.IH c211_app_transport_type[OF wW _ _ xm] by blast
  also have "\<dots> \<longleftrightarrow> (\<forall>u. Elem u raw_W \<longrightarrow> raw_rel w u \<longrightarrow> (\<forall>a. Elem a (raw_D \<sigma> u) \<longrightarrow>
      c211_rcur \<sigma>s u (?Fx u a) = {}))"
    by (rule c211_two_step_collapse[where
        Q="\<lambda>v a u. c211_rcur \<sigma>s u (raw_T ?\<rho> v u (?Fx v a)) = {}"
        and P="\<lambda>u a. c211_rcur \<sigma>s u (?Fx u a) = {}", OF wW nat])
  also have "\<dots> \<longleftrightarrow> (\<forall>u. Elem u raw_W \<longrightarrow> raw_rel w u \<longrightarrow>
      c211_rcur (\<sigma> # \<sigma>s) u (raw_T (Arr \<sigma> ?\<rho>) w u x) = {})"
    by (simp only: c211_rcur_Cons_empty)
  finally show ?case by (simp only: paper_type_vector.simps)
qed

subsection \<open>Terminal worlds share tuples, application and truth\<close>

lemma c211_tuples_terminal:
  "Nat2nat w \<noteq> 0 \<Longrightarrow> Nat2nat w \<noteq> 1 \<Longrightarrow> c211_tuples \<sigma>s w = c211_tuples \<sigma>s raw_limit"
  by (simp add: c211_tuples_def raw_D_def)

lemma c211_rapp_terminal:
  assumes "Nat2nat w \<noteq> 0" "Nat2nat w \<noteq> 1"
  shows "c211_rapp \<sigma>s w F xs = c211_rapp \<sigma>s raw_limit F xs"
  using assms by (induction \<sigma>s w F xs rule: c211_rapp.induct) (simp_all add: raw_app_def)

lemma c211_truth_terminal:
  "Nat2nat w \<noteq> 0 \<Longrightarrow> Nat2nat w \<noteq> 1 \<Longrightarrow> raw_truth w p = raw_truth raw_limit p"
  by (simp add: raw_truth_def)

lemma c211_rcur_terminal:
  assumes "Nat2nat w \<noteq> 0" "Nat2nat w \<noteq> 1"
  shows "c211_rcur \<sigma>s w F = c211_rcur \<sigma>s raw_limit F"
  by (simp add: c211_rcur_def c211_tuples_terminal[OF assms]
      c211_rapp_terminal[OF assms] c211_truth_terminal[OF assms])

lemma c211_rcur_leaf: "c211_rcur \<sigma>s (raw_leaf n) F = c211_rcur \<sigma>s raw_limit F"
  by (rule c211_rcur_terminal) simp_all

lemma c211_tuples_leaf: "c211_tuples \<sigma>s (raw_leaf n) = c211_tuples \<sigma>s raw_limit"
  by (rule c211_tuples_terminal) simp_all

lemma c211_rapp_type:
  assumes "Elem F (raw_D (paper_type_vector \<sigma>s Prop) w)" "xs \<in> c211_tuples \<sigma>s w"
  shows "Elem (c211_rapp \<sigma>s w F xs) (raw_D Prop w)"
  using assms
proof (induction \<sigma>s arbitrary: F xs)
  case Nil
  then show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  obtain x ys where xs: "xs = x # ys" and xm: "Elem x (raw_D \<sigma> w)"
    and ys: "ys \<in> c211_tuples \<sigma>s w"
    using Cons.prems(2) c211_tuples_Cons by blast
  have Fm: "Elem F (raw_D (Arr \<sigma> (paper_type_vector \<sigma>s Prop)) w)" using Cons.prems(1) by simp
  show ?case
    using Cons.IH[OF raw_app_type[OF Fm xm] ys] by (simp add: xs)
qed

subsection \<open>O3: the limit relation is the ultralimit of the leaf relations\<close>

lemma c211_rapp_ulim:
  assumes "\<And>n. Elem (f n) (typed_M (paper_type_vector \<sigma>s Prop))"
    "xs \<in> c211_tuples \<sigma>s raw_limit"
  shows "c211_rapp \<sigma>s raw_limit (ulim f) xs = ulim (\<lambda>n. c211_rapp \<sigma>s raw_limit (f n) xs)"
  using assms
proof (induction \<sigma>s arbitrary: f xs)
  case Nil
  show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  let ?\<rho> = "paper_type_vector \<sigma>s Prop"
  obtain x ys where xs: "xs = x # ys" and xm: "Elem x (typed_M \<sigma>)"
    and ys: "ys \<in> c211_tuples \<sigma>s raw_limit"
    using Cons.prems(2) c211_tuples_Cons[of xs \<sigma> \<sigma>s raw_limit] by auto
  have fm: "Elem (f n) (typed_M (Arr \<sigma> ?\<rho>))" for n using Cons.prems(1)[of n] by simp
  have gm: "Elem (app (f n) x) (typed_M ?\<rho>)" for n by (rule typed_M_application[OF fm xm])
  have app: "app (ulim f) x = ulim (\<lambda>n. app (f n) x)"
    using typed_ulim_app[of f \<sigma> ?\<rho> "\<lambda>n. x", OF fm xm] by simp
  have "c211_rapp (\<sigma> # \<sigma>s) raw_limit (ulim f) xs = c211_rapp \<sigma>s raw_limit (app (ulim f) x) ys"
    by (simp add: xs raw_app_def)
  also have "\<dots> = ulim (\<lambda>n. c211_rapp \<sigma>s raw_limit (app (f n) x) ys)"
    by (simp only: app Cons.IH[OF gm ys])
  also have "\<dots> = ulim (\<lambda>n. c211_rapp (\<sigma> # \<sigma>s) raw_limit (f n) xs)"
    by (simp add: xs raw_app_def)
  finally show ?case .
qed

lemma c211_truth_ulim:
  assumes "\<And>n. Elem (g n) (typed_M Prop)"
  shows "raw_truth raw_limit (ulim g) \<longleftrightarrow> eventually (\<lambda>n. raw_truth raw_limit (g n)) norm_U"
proof -
  have fin: "finite (explode (typed_M Prop))" by (rule typed_M_finite)
  have "ulim (\<lambda>n. bit_dec (g n)) = bit_dec (ulim g)"
    by (rule ulim_map[OF fin]) (use assms in \<open>simp add: explode_Elem\<close>)
  then show ?thesis by (simp add: raw_truth_def ulim_bool_iff[symmetric])
qed

theorem c211_rcur_ulim:
  assumes fm: "\<And>n. Elem (f n) (typed_M (paper_type_vector \<sigma>s Prop))"
  shows "c211_rcur \<sigma>s raw_limit (ulim f) =
    {xs \<in> c211_tuples \<sigma>s raw_limit. eventually (\<lambda>n. xs \<in> c211_rcur \<sigma>s raw_limit (f n)) norm_U}"
proof (rule set_eqI)
  fix xs
  show "xs \<in> c211_rcur \<sigma>s raw_limit (ulim f) \<longleftrightarrow>
    xs \<in> {xs \<in> c211_tuples \<sigma>s raw_limit. eventually (\<lambda>n. xs \<in> c211_rcur \<sigma>s raw_limit (f n)) norm_U}"
  proof (cases "xs \<in> c211_tuples \<sigma>s raw_limit")
    case True
    have val: "Elem (c211_rapp \<sigma>s raw_limit (f n) xs) (typed_M Prop)" for n
      using c211_rapp_type[of "f n" \<sigma>s raw_limit xs] fm[of n] True by simp
    have "raw_truth raw_limit (c211_rapp \<sigma>s raw_limit (ulim f) xs) \<longleftrightarrow>
        eventually (\<lambda>n. raw_truth raw_limit (c211_rapp \<sigma>s raw_limit (f n) xs)) norm_U"
      by (simp only: c211_rapp_ulim[OF fm True] c211_truth_ulim[OF val])
    then show ?thesis using True by (simp add: c211_rcur_def)
  next
    case False
    then show ?thesis by (simp add: c211_rcur_def)
  qed
qed

theorem c211_rcur_limit_ulim_rn:
  assumes Xm: "Elem X (typed_R (paper_type_vector \<sigma>s Prop))"
  shows "c211_rcur \<sigma>s raw_limit
      (typed_j (paper_type_vector \<sigma>s Prop) (typed_rs (paper_type_vector \<sigma>s Prop) X)) =
    {xs \<in> c211_tuples \<sigma>s raw_limit. eventually (\<lambda>n.
      xs \<in> c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) X n)) norm_U}"
  by (simp only: typed_R_compatible[OF Xm] c211_rcur_leaf
      c211_rcur_ulim[OF typed_rn_type[OF Xm]])

theorem c211_rcur_limit_ulim:
  assumes "Elem X (typed_R (paper_type_vector \<sigma>s Prop))"
  shows "c211_rcur \<sigma>s raw_limit (raw_T (paper_type_vector \<sigma>s Prop) raw_root raw_limit X) =
    {xs \<in> c211_tuples \<sigma>s raw_limit. eventually (\<lambda>n.
      xs \<in> c211_rcur \<sigma>s (raw_leaf n)
        (raw_T (paper_type_vector \<sigma>s Prop) raw_root (raw_leaf n) X)) norm_U}"
  by (simp only: c211_raw_T_root_limit c211_raw_T_root_leaf c211_rcur_limit_ulim_rn[OF assms])

text \<open>The limit coordinate of a root object is determined by its leaves.\<close>

corollary c211_root_limit_mono:
  assumes "Elem X (typed_R (paper_type_vector \<sigma>s Prop))"
    "Elem Y (typed_R (paper_type_vector \<sigma>s Prop))"
    and leaves: "\<And>n. c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) X n) \<subseteq>
      c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) Y n)"
  shows "c211_rcur \<sigma>s raw_limit
      (typed_j (paper_type_vector \<sigma>s Prop) (typed_rs (paper_type_vector \<sigma>s Prop) X)) \<subseteq>
    c211_rcur \<sigma>s raw_limit
      (typed_j (paper_type_vector \<sigma>s Prop) (typed_rs (paper_type_vector \<sigma>s Prop) Y))"
proof
  fix xs
  assume "xs \<in> c211_rcur \<sigma>s raw_limit
      (typed_j (paper_type_vector \<sigma>s Prop) (typed_rs (paper_type_vector \<sigma>s Prop) X))"
  then have xs: "xs \<in> c211_tuples \<sigma>s raw_limit" and ev: "eventually (\<lambda>n.
      xs \<in> c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) X n)) norm_U"
    by (simp_all add: c211_rcur_limit_ulim_rn[OF assms(1)])
  have "eventually (\<lambda>n.
      xs \<in> c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) Y n)) norm_U"
    using ev by (rule eventually_mono) (use leaves in blast)
  then show "xs \<in> c211_rcur \<sigma>s raw_limit
      (typed_j (paper_type_vector \<sigma>s Prop) (typed_rs (paper_type_vector \<sigma>s Prop) Y))"
    using xs by (simp add: c211_rcur_limit_ulim_rn[OF assms(2)])
qed

corollary c211_root_limit_empty:
  assumes "Elem X (typed_R (paper_type_vector \<sigma>s Prop))"
    and leaves: "\<And>n. c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) X n) = {}"
  shows "c211_rcur \<sigma>s raw_limit
      (typed_j (paper_type_vector \<sigma>s Prop) (typed_rs (paper_type_vector \<sigma>s Prop) X)) = {}"
  unfolding c211_rcur_limit_ulim_rn[OF assms(1)] using leaves by (simp add: norm_U.proper)

subsection \<open>O4: coordinatewise order and emptiness\<close>

lemma c211_terminal_rel:
  "w = raw_limit \<or> w = raw_leaf n \<Longrightarrow> raw_rel w v \<longleftrightarrow> v = w"
  by (auto simp: raw_rel_def)

theorem c211_rleq_terminal:
  assumes w: "w = raw_limit \<or> w = raw_leaf n"
    and "Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
    "Elem y (raw_D (paper_type_vector \<sigma>s Prop) w)"
  shows "c211_rleq (paper_type_vector \<sigma>s Prop) w x y \<longleftrightarrow> c211_rcur \<sigma>s w x \<subseteq> c211_rcur \<sigma>s w y"
proof -
  have wW: "Elem w raw_W" using w by auto
  show ?thesis
    by (simp only: c211_rleq_iff_rcur[OF wW assms(2,3)] c211_terminal_rel[OF w])
      (use wW in \<open>auto simp: raw_T_id\<close>)
qed

theorem c211_rempty_terminal:
  assumes w: "w = raw_limit \<or> w = raw_leaf n"
    and "Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
  shows "c211_rempty (paper_type_vector \<sigma>s Prop) w x \<longleftrightarrow> c211_rcur \<sigma>s w x = {}"
proof -
  have wW: "Elem w raw_W" using w by auto
  show ?thesis
    by (simp only: c211_rempty_iff_rcur[OF wW assms(2)] c211_terminal_rel[OF w])
      (use wW in \<open>auto simp: raw_T_id\<close>)
qed

lemma c211_middle_rel: "raw_rel raw_middle v \<longleftrightarrow> v = raw_middle \<or> v = raw_limit"
  by (auto simp: raw_rel_def)

lemma c211_all_two_worlds:
  "Elem a raw_W \<Longrightarrow> Elem b raw_W \<Longrightarrow>
    (\<forall>v. Elem v raw_W \<longrightarrow> v = a \<or> v = b \<longrightarrow> P v) \<longleftrightarrow> P a \<and> P b"
  by blast

theorem c211_rleq_middle:
  assumes "Elem S (typed_S (paper_type_vector \<sigma>s Prop))"
    "Elem S' (typed_S (paper_type_vector \<sigma>s Prop))"
  shows "c211_rleq (paper_type_vector \<sigma>s Prop) raw_middle S S' \<longleftrightarrow>
    c211_rcur \<sigma>s raw_middle S \<subseteq> c211_rcur \<sigma>s raw_middle S' \<and>
    c211_rcur \<sigma>s raw_limit (typed_j (paper_type_vector \<sigma>s Prop) S) \<subseteq>
      c211_rcur \<sigma>s raw_limit (typed_j (paper_type_vector \<sigma>s Prop) S')"
proof -
  have Sm: "Elem S (raw_D (paper_type_vector \<sigma>s Prop) raw_middle)"
    and S'm: "Elem S' (raw_D (paper_type_vector \<sigma>s Prop) raw_middle)"
    using assms by simp_all
  show ?thesis
    by (simp only: c211_rleq_iff_rcur[OF raw_worlds(2) Sm S'm] c211_middle_rel
        c211_all_two_worlds[OF raw_worlds(2,3)] raw_T_id c211_raw_T_middle_limit)
qed

theorem c211_rempty_middle:
  assumes "Elem S (typed_S (paper_type_vector \<sigma>s Prop))"
  shows "c211_rempty (paper_type_vector \<sigma>s Prop) raw_middle S \<longleftrightarrow>
    c211_rcur \<sigma>s raw_middle S = {} \<and>
    c211_rcur \<sigma>s raw_limit (typed_j (paper_type_vector \<sigma>s Prop) S) = {}"
proof -
  have Sm: "Elem S (raw_D (paper_type_vector \<sigma>s Prop) raw_middle)" using assms by simp
  show ?thesis
    by (simp only: c211_rempty_iff_rcur[OF raw_worlds(2) Sm] c211_middle_rel
        c211_all_two_worlds[OF raw_worlds(2,3)] raw_T_id c211_raw_T_middle_limit)
qed

lemma c211_root_rel: "raw_rel raw_root v"
  by (simp add: raw_rel_def)

text \<open>The root order compares the root, intermediate and leaf coordinates
  (all four if one wishes; the limit one is then automatic).\<close>

theorem c211_rleq_root_full:
  assumes "Elem X (typed_R (paper_type_vector \<sigma>s Prop))"
    "Elem Y (typed_R (paper_type_vector \<sigma>s Prop))"
  shows "c211_rleq (paper_type_vector \<sigma>s Prop) raw_root X Y \<longleftrightarrow>
    c211_rcur \<sigma>s raw_root X \<subseteq> c211_rcur \<sigma>s raw_root Y \<and>
    c211_rcur \<sigma>s raw_middle (typed_rs (paper_type_vector \<sigma>s Prop) X) \<subseteq>
      c211_rcur \<sigma>s raw_middle (typed_rs (paper_type_vector \<sigma>s Prop) Y) \<and>
    c211_rcur \<sigma>s raw_limit
        (typed_j (paper_type_vector \<sigma>s Prop) (typed_rs (paper_type_vector \<sigma>s Prop) X)) \<subseteq>
      c211_rcur \<sigma>s raw_limit
        (typed_j (paper_type_vector \<sigma>s Prop) (typed_rs (paper_type_vector \<sigma>s Prop) Y)) \<and>
    (\<forall>n. c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) X n) \<subseteq>
      c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) Y n))"
  (is "_ \<longleftrightarrow> ?coord")
proof -
  let ?\<tau> = "paper_type_vector \<sigma>s Prop"
  have Xm: "Elem X (raw_D ?\<tau> raw_root)" and Ym: "Elem Y (raw_D ?\<tau> raw_root)"
    using assms by simp_all
  have all: "(\<forall>v. Elem v raw_W \<longrightarrow> raw_rel raw_root v \<longrightarrow>
      c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v X) \<subseteq> c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v Y))
    \<longleftrightarrow> ?coord"
  proof
    assume h: "\<forall>v. Elem v raw_W \<longrightarrow> raw_rel raw_root v \<longrightarrow>
      c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v X) \<subseteq> c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v Y)"
    have at: "c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v X) \<subseteq> c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v Y)"
      if "Elem v raw_W" for v
      using h that c211_root_rel by blast
    show ?coord
      using at[OF raw_worlds(1)] at[OF raw_worlds(2)] at[OF raw_worlds(3)]
        at[OF raw_worlds(4)]
      by (simp add: raw_T_id c211_raw_T_worlds)
  next
    assume c: ?coord
    show "\<forall>v. Elem v raw_W \<longrightarrow> raw_rel raw_root v \<longrightarrow>
      c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v X) \<subseteq> c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v Y)"
    proof (intro allI impI)
      fix v assume vW: "Elem v raw_W"
      from vW show "c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v X) \<subseteq>
          c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v Y)"
        by (cases rule: c211_world_exhaust) (use c in \<open>simp_all add: raw_T_id c211_raw_T_worlds\<close>)
    qed
  qed
  show ?thesis by (simp only: c211_rleq_iff_rcur[OF raw_worlds(1) Xm Ym] all)
qed

theorem c211_rleq_root:
  assumes "Elem X (typed_R (paper_type_vector \<sigma>s Prop))"
    "Elem Y (typed_R (paper_type_vector \<sigma>s Prop))"
  shows "c211_rleq (paper_type_vector \<sigma>s Prop) raw_root X Y \<longleftrightarrow>
    c211_rcur \<sigma>s raw_root X \<subseteq> c211_rcur \<sigma>s raw_root Y \<and>
    c211_rcur \<sigma>s raw_middle (typed_rs (paper_type_vector \<sigma>s Prop) X) \<subseteq>
      c211_rcur \<sigma>s raw_middle (typed_rs (paper_type_vector \<sigma>s Prop) Y) \<and>
    (\<forall>n. c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) X n) \<subseteq>
      c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) Y n))"
  using c211_rleq_root_full[OF assms] c211_root_limit_mono[OF assms] by blast

theorem c211_rleq_root_middle:
  assumes "Elem X (typed_R (paper_type_vector \<sigma>s Prop))"
    "Elem Y (typed_R (paper_type_vector \<sigma>s Prop))"
  shows "c211_rleq (paper_type_vector \<sigma>s Prop) raw_root X Y \<longleftrightarrow>
    c211_rcur \<sigma>s raw_root X \<subseteq> c211_rcur \<sigma>s raw_root Y \<and>
    c211_rleq (paper_type_vector \<sigma>s Prop) raw_middle
      (typed_rs (paper_type_vector \<sigma>s Prop) X) (typed_rs (paper_type_vector \<sigma>s Prop) Y) \<and>
    (\<forall>n. c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) X n) \<subseteq>
      c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) Y n))"
  using c211_rleq_root_full[OF assms]
    c211_rleq_middle[OF typed_rs_type[OF assms(1)] typed_rs_type[OF assms(2)]]
  by blast

theorem c211_rempty_root:
  assumes "Elem X (typed_R (paper_type_vector \<sigma>s Prop))"
  shows "c211_rempty (paper_type_vector \<sigma>s Prop) raw_root X \<longleftrightarrow>
    c211_rcur \<sigma>s raw_root X = {} \<and>
    c211_rcur \<sigma>s raw_middle (typed_rs (paper_type_vector \<sigma>s Prop) X) = {} \<and>
    (\<forall>n. c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) X n) = {})"
  (is "_ \<longleftrightarrow> ?coord")
proof -
  let ?\<tau> = "paper_type_vector \<sigma>s Prop"
  have Xm: "Elem X (raw_D ?\<tau> raw_root)" using assms by simp
  have all: "(\<forall>v. Elem v raw_W \<longrightarrow> raw_rel raw_root v \<longrightarrow>
      c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v X) = {}) \<longleftrightarrow> ?coord"
  proof
    assume h: "\<forall>v. Elem v raw_W \<longrightarrow> raw_rel raw_root v \<longrightarrow>
      c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v X) = {}"
    have at: "c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v X) = {}" if "Elem v raw_W" for v
      using h that c211_root_rel by blast
    show ?coord
      using at[OF raw_worlds(1)] at[OF raw_worlds(2)] at[OF raw_worlds(4)]
      by (simp add: raw_T_id c211_raw_T_worlds)
  next
    assume c: ?coord
    have lim: "c211_rcur \<sigma>s raw_limit (typed_j ?\<tau> (typed_rs ?\<tau> X)) = {}"
      by (rule c211_root_limit_empty[OF assms]) (use c in blast)
    show "\<forall>v. Elem v raw_W \<longrightarrow> raw_rel raw_root v \<longrightarrow>
      c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v X) = {}"
    proof (intro allI impI)
      fix v assume vW: "Elem v raw_W"
      from vW show "c211_rcur \<sigma>s v (raw_T ?\<tau> raw_root v X) = {}"
        by (cases rule: c211_world_exhaust)
          (use c lim in \<open>simp_all add: raw_T_id c211_raw_T_worlds\<close>)
    qed
  qed
  show ?thesis by (simp only: c211_rempty_iff_rcur[OF raw_worlds(1) Xm] all)
qed

section \<open>Audit endpoints\<close>

ML \<open>
  val facts = [@{thm c211_raw_T_root_middle}, @{thm c211_raw_T_root_limit},
    @{thm c211_raw_T_root_leaf}, @{thm c211_raw_T_middle_limit},
    @{thm c211_rcur_Cons_subset}, @{thm c211_rcur_Cons_empty},
    @{thm c211_rleq_iff_rcur}, @{thm c211_rempty_iff_rcur},
    @{thm c211_rcur_leaf}, @{thm c211_tuples_leaf}, @{thm c211_rapp_ulim},
    @{thm c211_rcur_ulim}, @{thm c211_rcur_limit_ulim_rn}, @{thm c211_rcur_limit_ulim},
    @{thm c211_root_limit_mono}, @{thm c211_root_limit_empty},
    @{thm c211_rleq_terminal}, @{thm c211_rempty_terminal},
    @{thm c211_rleq_middle}, @{thm c211_rempty_middle},
    @{thm c211_rleq_root_full}, @{thm c211_rleq_root}, @{thm c211_rleq_root_middle},
    @{thm c211_rempty_root}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "C211-RAW-ORDER: order and emptiness are coordinatewise inclusion of current relations";
\<close>

end
