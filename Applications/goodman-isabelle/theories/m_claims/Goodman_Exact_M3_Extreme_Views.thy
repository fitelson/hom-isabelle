theory Goodman_Exact_M3_Extreme_Views
  imports Goodman_Exact_M3_Algebra
begin

section \<open>Necessity and necessity of negation are in the exact logical stock\<close>

definition gi_M3_box_term where
  "gi_M3_box_term b = Lam Prop (ObjBox (if b then Var 0 else Neg (Var 0)))"

lemma gi_M3_box_term_type:
  "[] \<turnstile> gi_M3_box_term b : gb_unary"
  unfolding gi_M3_box_term_def
  by (cases b; simp; intro has_type.Lam typed_ObjBox has_type.Neg typed_var0)

lemma gi_M3_box_term_logical:
  "pp_logical_vocabulary (gi_M3_box_term b)"
  by (cases b; simp add: gi_M3_box_term_def pp_logical_vocabulary_def ObjBox_def ObjTrue_def)

lemma gi_M3_future_truth_iff_view:
  "(\<forall>v. prefix (rev i) v \<longrightarrow> pp_e_holds (pp_n_bacon_embed P) v)
    \<longleftrightarrow> pp_view i P = UNIV"
proof
  assume all: "\<forall>v. prefix (rev i) v \<longrightarrow> pp_e_holds (pp_n_bacon_embed P) v"
  show "pp_view i P = UNIV"
  proof (rule set_eqI)
    fix j
    have future: "prefix (rev i) (rev i @ rev j)" by (simp add: prefix_def)
    have "pp_e_holds (pp_n_bacon_embed P) (rev i @ rev j)"
      using all future by blast
    then show "j \<in> pp_view i P \<longleftrightarrow> j \<in> UNIV"
      by (simp add: pp_view_def)
  qed
next
  assume view: "pp_view i P = UNIV"
  show "\<forall>v. prefix (rev i) v \<longrightarrow> pp_e_holds (pp_n_bacon_embed P) v"
  proof (intro allI impI)
    fix v assume "prefix (rev i) v"
    then obtain u where shape: "v = rev i @ u" by (auto simp: prefix_def)
    have "rev u \<in> pp_view i P" using view by simp
    then show "pp_e_holds (pp_n_bacon_embed P) v" by (simp add: shape pp_view_def)
  qed
qed

lemma gi_M3_box_raw:
  "pp_e_raw_operator (pp_e_closed_den (gi_M3_box_term b)) P =
    pp_sem_box (if b then P else - P)"
proof (rule set_eqI)
  fix i
  have pm: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)"
    using pp_n_bacon_embed_in_domain[of P] by simp
  have positive: "(\<forall>v. prefix (rev i) v \<longrightarrow> pp_e_holds (pp_n_bacon_embed P) v)
    = (pp_view i P = UNIV)" by (rule gi_M3_future_truth_iff_view)
  have negative: "(\<forall>v. prefix (rev i) v \<longrightarrow> \<not> pp_e_holds (pp_n_bacon_embed P) v)
    = (pp_view i (- P) = UNIV)"
    using gi_M3_future_truth_iff_view[of i "- P"] by simp
  show "i \<in> pp_e_raw_operator (pp_e_closed_den (gi_M3_box_term b)) P \<longleftrightarrow>
      i \<in> pp_sem_box (if b then P else - P)"
    using pm positive negative
    by (cases b; simp add: pp_e_raw_operator_def pp_e_closed_den_def gi_M3_box_term_def
      Lambda_app pp_n_bacon_extract_def pp_e_eval_ObjBox_holds pp_e_eval_ObjTrue
      pp_e_prop_eqv_truth_iff pp_sem_box_def)
qed

theorem gi_exact_M3_box_in_stock:
  "(\<lambda>P. pp_sem_box (if b then P else - P)) \<in> pp_e_exact_operator_stock"
proof -
  have member: "pp_e_raw_operator (pp_e_closed_den (gi_M3_box_term b)) \<in> pp_e_exact_operator_stock"
    by (rule pp_e_exact_operator_stockI[OF gi_M3_box_term_type gi_M3_box_term_logical])
  have same: "pp_e_raw_operator (pp_e_closed_den (gi_M3_box_term b)) =
      (\<lambda>P. pp_sem_box (if b then P else - P))"
    by (rule ext; rule gi_M3_box_raw)
  show ?thesis using member by (simp only: same)
qed

lemma gi_exact_M3_box_nonzero:
  "(\<lambda>P. pp_sem_box (if b then P else - P)) \<noteq> (\<lambda>P. {})"
proof
  assume equal: "(\<lambda>P. pp_sem_box (if b then P else - P)) = (\<lambda>P. {})"
  have "pp_sem_box (if b then (if b then UNIV else {}) else - (if b then UNIV else {})) = {}"
    by (rule fun_cong[OF equal])
  then show False by (cases b; simp add: pp_sem_box_def pp_view_def)
qed

theorem gi_exact_M3_fun_prime_has_extreme_views:
  assumes fp: "pp_e_exact_fun_prime p"
  shows "UNIV \<in> pp_orbit p \<and> {} \<in> pp_orbit p"
proof -
  have free: "gi_M3_free_for_stock pp_e_exact_operator_stock p"
    using fp by (simp only: gi_exact_M3_fun_prime_iff_free)
  have nonempty: "pp_sem_box (if b then p else - p) \<noteq> {}" for b
    using free gi_exact_M3_box_in_stock[of b] gi_exact_M3_box_nonzero[of b]
    unfolding gi_M3_free_for_stock_def by blast
  obtain i where top: "pp_view i p = UNIV"
    using nonempty[of True] unfolding pp_sem_box_def by auto
  obtain j where not_top: "pp_view j (- p) = UNIV"
    using nonempty[of False] unfolding pp_sem_box_def by auto
  have bottom: "pp_view j p = {}" using not_top by (auto simp: pp_view_def)
  show ?thesis unfolding pp_orbit_def
    using top bottom by (auto intro: image_eqI[where x=i] image_eqI[where x=j])
qed

corollary gi_native_M3_fun_prime_has_extreme_views:
  "sg_rich G \<Longrightarrow> gi_stock_fun_prime (gi_exact_native_operator_stock G) p \<Longrightarrow>
    UNIV \<in> pp_orbit p \<and> {} \<in> pp_orbit p"
  by (simp only: gi_exact_native_fun_prime_iff; rule gi_exact_M3_fun_prime_has_extreme_views; assumption)

text \<open>
  Exact closed logical witnesses discharge the modal-stock premise of M3.
  Necessity and necessity of negation suffice directly: a free generator
  cannot make either nonzero operator identically false. Hence it has both
  a wholly true and a wholly false view. This is a statement about the
  complete exact stock, not merely an abstract Boolean closure.
\<close>

end
