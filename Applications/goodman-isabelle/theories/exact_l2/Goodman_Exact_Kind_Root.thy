theory Goodman_Exact_Kind_Root
  imports Goodman_Exact_L2_Root_Semantics
begin

section \<open>Pure unary values and their faithful raw representation at the root\<close>

lemma gi_exact_raw_stock_iff:
  assumes xm: "Elem X (pp_e_domain gb_unary)"
  shows "pp_e_closed_logical_stock gb_unary [] X \<longleftrightarrow>
    pp_e_raw_operator X \<in> pp_e_exact_operator_stock"
proof
  assume pure: "pp_e_closed_logical_stock gb_unary [] X"
  have "X \<in> pp_e_closed_unary_denotations" using pure by (simp only: gi_exact_root_unary_stock)
  then show "pp_e_raw_operator X \<in> pp_e_exact_operator_stock"
    unfolding pp_e_exact_operator_stock_def by blast
next
  assume raw: "pp_e_raw_operator X \<in> pp_e_exact_operator_stock"
  then obtain Y where ym: "Y \<in> pp_e_closed_unary_denotations"
    and same: "pp_e_raw_operator X = pp_e_raw_operator Y"
    unfolding pp_e_exact_operator_stock_def by blast
  have yd: "Elem Y (pp_e_domain gb_unary)"
    by (rule pp_e_closed_unary_denotation_in_domain[OF ym])
  have xy: "X = Y" by (rule gi_exact_raw_operator_injective[OF xm yd same])
  show "pp_e_closed_logical_stock gb_unary [] X"
    using ym by (simp only: xy gi_exact_root_unary_stock)
qed

lemma gi_exact_identity_denotation:
  "pp_e_eval C \<rho> pp_identity_operator = pp_e_closed_den pp_identity_operator"
  by (simp add: pp_identity_operator_def pp_e_closed_den_def)

lemma gi_exact_identity_denotation_member:
  "Elem (pp_e_closed_den pp_identity_operator) (pp_e_domain gb_unary)"
  by (rule pp_e_closed_den_in_domain[OF typed_pp_identity_operator[unfolded pp_unary_ty_def]])

lemma gi_exact_root_compose_eq_iff:
  assumes xm: "Elem X (pp_e_domain gb_unary)" and ym: "Elem Y (pp_e_domain gb_unary)"
    and zm: "Elem Z (pp_e_domain gb_unary)"
  shows "pp_e_eqv gb_unary [] X (gi_exact_value_compose Y Z) \<longleftrightarrow>
    pp_e_raw_operator X = pp_e_raw_operator Y \<circ> pp_e_raw_operator Z"
proof -
  have cm: "Elem (gi_exact_value_compose Y Z) (pp_e_domain gb_unary)"
    by (rule gi_exact_value_compose_member[OF ym zm])
  have faithful: "(X = gi_exact_value_compose Y Z) \<longleftrightarrow>
    pp_e_raw_operator X = pp_e_raw_operator (gi_exact_value_compose Y Z)"
    using gi_exact_raw_operator_eq_iff[OF xm cm] by blast
  show ?thesis by (simp only: gi_exact_root_eqv[OF xm cm] faithful gi_exact_raw_value_compose[OF ym zm])
qed

lemma gi_exact_root_inverse_eq_iff:
  assumes xm: "Elem X (pp_e_domain gb_unary)" and ym: "Elem Y (pp_e_domain gb_unary)"
  shows "pp_e_eqv gb_unary [] (gi_exact_value_compose X Y) (pp_e_closed_den pp_identity_operator)
    \<longleftrightarrow> pp_e_raw_operator X \<circ> pp_e_raw_operator Y = id"
proof -
  have cm: "Elem (gi_exact_value_compose X Y) (pp_e_domain gb_unary)"
    by (rule gi_exact_value_compose_member[OF xm ym])
  have im: "Elem (pp_e_closed_den pp_identity_operator) (pp_e_domain gb_unary)"
    by (rule gi_exact_identity_denotation_member)
  have faithful: "(gi_exact_value_compose X Y = pp_e_closed_den pp_identity_operator) \<longleftrightarrow>
    pp_e_raw_operator (gi_exact_value_compose X Y) = pp_e_raw_operator (pp_e_closed_den pp_identity_operator)"
    using gi_exact_raw_operator_eq_iff[OF cm im] by blast
  show ?thesis by (simp only: gi_exact_root_eqv[OF cm im] faithful
    gi_exact_raw_value_compose[OF xm ym] pp_e_raw_operator_identity)
qed

section \<open>Existential inverse: the argument need not itself be pure\<close>

text \<open>
  The old pp_reversible formula asserts a pure inverse, but does not
  include Pure(Z). Only pp_group_member adds that conjunct. Accordingly
  the next root theorem concludes existence of a stock inverse, not
  pp_e_exact_reversible, whose definition also requires Z in the stock.
\<close>

lemma gi_exact_reversible_body_root:
  assumes wm: "Elem W (pp_e_domain gb_unary)"
  shows "pp_e_holds (pp_e_eval pp_e_generic_internal_constants (extend_env W \<rho>)
    (Conj (pp_pure pp_unary_ty (Var 0))
      (Conj (Eq pp_unary_ty (pp_compose (shift Z) (Var 0)) pp_identity_operator)
        (Eq pp_unary_ty (pp_compose (Var 0) (shift Z)) pp_identity_operator)))) []
    \<longleftrightarrow>
    pp_e_closed_logical_stock gb_unary [] W \<and>
    pp_e_eqv gb_unary [] (gi_exact_value_compose (pp_e_eval pp_e_generic_internal_constants \<rho> Z) W)
      (pp_e_closed_den pp_identity_operator) \<and>
    pp_e_eqv gb_unary [] (gi_exact_value_compose W (pp_e_eval pp_e_generic_internal_constants \<rho> Z))
      (pp_e_closed_den pp_identity_operator)"
  by (simp only: pp_e_eval_Conj_holds pp_e_eval_Eq_holds pp_pure_def
    gi_exact_eval_compose pp_e_eval_shift gi_exact_identity_denotation
    pp_e_eval.simps(1,3) pp_e_generic_eval_Pure extend_env.simps
    pp_unary_ty_def pp_e_classifier_holds[OF wm])

lemma gi_exact_reversible_value_witness:
  assumes xm: "Elem X (pp_e_domain gb_unary)"
  shows "(\<exists>W. Elem W (pp_e_domain gb_unary) \<and>
      pp_e_closed_logical_stock gb_unary [] W \<and>
      pp_e_eqv gb_unary [] (gi_exact_value_compose X W) (pp_e_closed_den pp_identity_operator) \<and>
      pp_e_eqv gb_unary [] (gi_exact_value_compose W X) (pp_e_closed_den pp_identity_operator))
    \<longleftrightarrow> (\<exists>V\<in>pp_e_exact_operator_stock.
      pp_e_raw_operator X \<circ> V = id \<and> V \<circ> pp_e_raw_operator X = id)"
proof
  assume left: "\<exists>W. Elem W (pp_e_domain gb_unary) \<and>
    pp_e_closed_logical_stock gb_unary [] W \<and>
    pp_e_eqv gb_unary [] (gi_exact_value_compose X W) (pp_e_closed_den pp_identity_operator) \<and>
    pp_e_eqv gb_unary [] (gi_exact_value_compose W X) (pp_e_closed_den pp_identity_operator)"
  then obtain W where wm: "Elem W (pp_e_domain gb_unary)"
    and pure: "pp_e_closed_logical_stock gb_unary [] W"
    and xw: "pp_e_eqv gb_unary [] (gi_exact_value_compose X W) (pp_e_closed_den pp_identity_operator)"
    and wx: "pp_e_eqv gb_unary [] (gi_exact_value_compose W X) (pp_e_closed_den pp_identity_operator)" by blast
  have stock: "pp_e_raw_operator W \<in> pp_e_exact_operator_stock"
    using pure by (simp only: gi_exact_raw_stock_iff[OF wm])
  have a: "pp_e_raw_operator X \<circ> pp_e_raw_operator W = id"
    using xw by (simp only: gi_exact_root_inverse_eq_iff[OF xm wm])
  have b: "pp_e_raw_operator W \<circ> pp_e_raw_operator X = id"
    using wx by (simp only: gi_exact_root_inverse_eq_iff[OF wm xm])
  show "\<exists>V\<in>pp_e_exact_operator_stock. pp_e_raw_operator X \<circ> V = id \<and> V \<circ> pp_e_raw_operator X = id"
    using stock a b by blast
next
  assume right: "\<exists>V\<in>pp_e_exact_operator_stock.
    pp_e_raw_operator X \<circ> V = id \<and> V \<circ> pp_e_raw_operator X = id"
  then obtain V where vs: "V \<in> pp_e_exact_operator_stock"
    and xv: "pp_e_raw_operator X \<circ> V = id" and vx: "V \<circ> pp_e_raw_operator X = id" by blast
  obtain W where wd: "W \<in> pp_e_closed_unary_denotations" and raw: "V = pp_e_raw_operator W"
    using vs unfolding pp_e_exact_operator_stock_def by blast
  have wm: "Elem W (pp_e_domain gb_unary)" by (rule pp_e_closed_unary_denotation_in_domain[OF wd])
  have pure: "pp_e_closed_logical_stock gb_unary [] W" using wd by (simp only: gi_exact_root_unary_stock)
  have xw: "pp_e_eqv gb_unary [] (gi_exact_value_compose X W) (pp_e_closed_den pp_identity_operator)"
    using xv by (simp only: raw gi_exact_root_inverse_eq_iff[OF xm wm])
  have wx: "pp_e_eqv gb_unary [] (gi_exact_value_compose W X) (pp_e_closed_den pp_identity_operator)"
    using vx by (simp only: raw gi_exact_root_inverse_eq_iff[OF wm xm])
  show "\<exists>W. Elem W (pp_e_domain gb_unary) \<and>
    pp_e_closed_logical_stock gb_unary [] W \<and>
    pp_e_eqv gb_unary [] (gi_exact_value_compose X W) (pp_e_closed_den pp_identity_operator) \<and>
    pp_e_eqv gb_unary [] (gi_exact_value_compose W X) (pp_e_closed_den pp_identity_operator)"
    using wm pure xw wx by blast
qed

theorem gi_exact_reversible_root_iff:
  assumes typed: "\<Gamma> \<turnstile> Z : pp_unary_ty" and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_reversible Z)) []
    \<longleftrightarrow> (\<exists>W\<in>pp_e_exact_operator_stock.
      pp_e_raw_operator (pp_e_eval pp_e_generic_internal_constants \<rho> Z) \<circ> W = id \<and>
      W \<circ> pp_e_raw_operator (pp_e_eval pp_e_generic_internal_constants \<rho> Z) = id)"
proof -
  let ?X = "pp_e_eval pp_e_generic_internal_constants \<rho> Z"
  have xm: "Elem ?X (pp_e_domain gb_unary)"
    using GenericExactBaconConstants.pp_e_eval_type[OF typed env]
    by (simp only: pp_e_dom_def pp_unary_ty_def)
  let ?B = "\<lambda>W. pp_e_holds (pp_e_eval pp_e_generic_internal_constants (extend_env W \<rho>)
    (Conj (pp_pure pp_unary_ty (Var 0))
      (Conj (Eq pp_unary_ty (pp_compose (shift Z) (Var 0)) pp_identity_operator)
        (Eq pp_unary_ty (pp_compose (Var 0) (shift Z)) pp_identity_operator)))) []"
  let ?Q = "\<lambda>W. pp_e_closed_logical_stock gb_unary [] W \<and>
    pp_e_eqv gb_unary [] (gi_exact_value_compose ?X W) (pp_e_closed_den pp_identity_operator) \<and>
    pp_e_eqv gb_unary [] (gi_exact_value_compose W ?X) (pp_e_closed_den pp_identity_operator)"
  have evaluation: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_reversible Z)) []
    \<longleftrightarrow> (\<exists>W. Elem W (pp_e_domain gb_unary) \<and> ?Q W)"
  proof
    assume holds: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_reversible Z)) []"
    have original: "\<exists>W. Elem W (pp_e_domain pp_unary_ty) \<and> ?B W"
      using holds by (simp only: pp_reversible_def pp_e_eval_Exists_holds)
    then obtain W where old_member: "Elem W (pp_e_domain pp_unary_ty)" and body: "?B W" by blast
    have wm: "Elem W (pp_e_domain gb_unary)" using old_member by (simp only: pp_unary_ty_def)
    have transformed: "?Q W" using body gi_exact_reversible_body_root[OF wm, where \<rho>=\<rho> and Z=Z] by blast
    show "\<exists>W. Elem W (pp_e_domain gb_unary) \<and> ?Q W" using wm transformed by blast
  next
    assume transformed: "\<exists>W. Elem W (pp_e_domain gb_unary) \<and> ?Q W"
    then obtain W where wm: "Elem W (pp_e_domain gb_unary)" and body: "?Q W" by blast
    have original_body: "?B W" using body gi_exact_reversible_body_root[OF wm, where \<rho>=\<rho> and Z=Z] by blast
    have old_member: "Elem W (pp_e_domain pp_unary_ty)" using wm by (simp only: pp_unary_ty_def)
    have original: "\<exists>W. Elem W (pp_e_domain pp_unary_ty) \<and> ?B W" using old_member original_body by blast
    show "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_reversible Z)) []"
      using original by (simp only: pp_reversible_def pp_e_eval_Exists_holds)
  qed
  show ?thesis by (simp only: evaluation gi_exact_reversible_value_witness[OF xm])
qed

theorem gi_exact_group_member_root_iff:
  assumes typed: "\<Gamma> \<turnstile> Z : pp_unary_ty" and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_group_member Z)) []
    \<longleftrightarrow> pp_e_exact_reversible (pp_e_raw_operator (pp_e_eval pp_e_generic_internal_constants \<rho> Z))"
proof -
  have xm: "Elem (pp_e_eval pp_e_generic_internal_constants \<rho> Z) (pp_e_domain gb_unary)"
    using GenericExactBaconConstants.pp_e_eval_type[OF typed env]
    by (simp only: pp_e_dom_def pp_unary_ty_def)
  have pure: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_pure pp_unary_ty Z)) []
    \<longleftrightarrow> pp_e_raw_operator (pp_e_eval pp_e_generic_internal_constants \<rho> Z) \<in> pp_e_exact_operator_stock"
    using pp_e_generic_eval_pure_holds[OF typed env, where w="[]"]
    by (simp only: pp_unary_ty_def gi_exact_raw_stock_iff[OF xm])
  show ?thesis by (simp only: pp_group_member_def pp_e_eval_Conj_holds pure
    gi_exact_reversible_root_iff[OF typed env] pp_e_exact_reversible_def)
qed

section \<open>Input-side composition gives exactly Goodman's same-kind relation\<close>

theorem gi_exact_same_kind_root_iff:
  assumes xt: "\<Gamma> \<turnstile> X : pp_unary_ty" and yt: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_same_kind X Y)) []
    \<longleftrightarrow> pp_e_exact_same_kind
      (pp_e_raw_operator (pp_e_eval pp_e_generic_internal_constants \<rho> X))
      (pp_e_raw_operator (pp_e_eval pp_e_generic_internal_constants \<rho> Y))"
proof -
  let ?x = "pp_e_eval pp_e_generic_internal_constants \<rho> X"
  let ?y = "pp_e_eval pp_e_generic_internal_constants \<rho> Y"
  have xm: "Elem ?x (pp_e_domain gb_unary)" and ym: "Elem ?y (pp_e_domain gb_unary)"
    using GenericExactBaconConstants.pp_e_eval_type[OF xt env]
      GenericExactBaconConstants.pp_e_eval_type[OF yt env]
    by (simp_all only: pp_e_dom_def pp_unary_ty_def)
  have group_clause: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants (extend_env W \<rho>)
      (pp_group_member (Var 0))) [] \<longleftrightarrow> pp_e_exact_reversible (pp_e_raw_operator W)"
    if wm: "Elem W (pp_e_domain gb_unary)" for W
  proof -
    have extended: "pp_e_env_typed (pp_unary_ty # \<Gamma>) (extend_env W \<rho>)"
      by (rule pp_e_env_typed_extend[OF env]; simp only: pp_unary_ty_def; rule wm)
    show ?thesis using gi_exact_group_member_root_iff[OF typed_var0 extended]
      by simp
  qed
  have equality_clause: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants (extend_env W \<rho>)
      (Eq pp_unary_ty (shift X) (pp_compose (shift Y) (Var 0)))) []
      \<longleftrightarrow> pp_e_raw_operator ?x = pp_e_raw_operator ?y \<circ> pp_e_raw_operator W"
    if wm: "Elem W (pp_e_domain gb_unary)" for W
    by (simp only: pp_e_eval_Eq_holds gi_exact_eval_compose pp_e_eval_shift
      pp_e_eval.simps(1) extend_env.simps pp_unary_ty_def
      gi_exact_root_compose_eq_iff[OF xm ym wm])
  let ?B = "\<lambda>W. pp_e_holds (pp_e_eval pp_e_generic_internal_constants (extend_env W \<rho>)
      (pp_group_member (Var 0))) [] \<and>
    pp_e_holds (pp_e_eval pp_e_generic_internal_constants (extend_env W \<rho>)
      (Eq pp_unary_ty (shift X) (pp_compose (shift Y) (Var 0)))) []"
  let ?Q = "\<lambda>W. pp_e_exact_reversible (pp_e_raw_operator W) \<and>
    pp_e_raw_operator ?x = pp_e_raw_operator ?y \<circ> pp_e_raw_operator W"
  have evaluation: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_same_kind X Y)) []
    \<longleftrightarrow> (\<exists>W. Elem W (pp_e_domain gb_unary) \<and> ?Q W)"
  proof
    assume holds: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_same_kind X Y)) []"
    have original: "\<exists>W. Elem W (pp_e_domain pp_unary_ty) \<and> ?B W"
      using holds by (simp only: pp_same_kind_def pp_e_eval_Exists_holds pp_e_eval_Conj_holds)
    then obtain W where old_member: "Elem W (pp_e_domain pp_unary_ty)" and body: "?B W" by blast
    have wm: "Elem W (pp_e_domain gb_unary)" using old_member by (simp only: pp_unary_ty_def)
    have transformed: "?Q W" using body group_clause[OF wm] equality_clause[OF wm] by blast
    show "\<exists>W. Elem W (pp_e_domain gb_unary) \<and> ?Q W" using wm transformed by blast
  next
    assume transformed: "\<exists>W. Elem W (pp_e_domain gb_unary) \<and> ?Q W"
    then obtain W where wm: "Elem W (pp_e_domain gb_unary)" and body: "?Q W" by blast
    have original_body: "?B W" using body group_clause[OF wm] equality_clause[OF wm] by blast
    have old_member: "Elem W (pp_e_domain pp_unary_ty)" using wm by (simp only: pp_unary_ty_def)
    have original: "\<exists>W. Elem W (pp_e_domain pp_unary_ty) \<and> ?B W" using old_member original_body by blast
    show "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_same_kind X Y)) []"
      using original by (simp only: pp_same_kind_def pp_e_eval_Exists_holds pp_e_eval_Conj_holds)
  qed
  have witnesses: "(\<exists>W. Elem W (pp_e_domain gb_unary) \<and>
      pp_e_exact_reversible (pp_e_raw_operator W) \<and>
      pp_e_raw_operator ?x = pp_e_raw_operator ?y \<circ> pp_e_raw_operator W)
    \<longleftrightarrow> pp_e_exact_same_kind (pp_e_raw_operator ?x) (pp_e_raw_operator ?y)"
  proof
    assume left: "\<exists>W. Elem W (pp_e_domain gb_unary) \<and>
      pp_e_exact_reversible (pp_e_raw_operator W) \<and>
      pp_e_raw_operator ?x = pp_e_raw_operator ?y \<circ> pp_e_raw_operator W"
    then show "pp_e_exact_same_kind (pp_e_raw_operator ?x) (pp_e_raw_operator ?y)"
      unfolding pp_e_exact_same_kind_def pp_e_exact_G_def by blast
  next
    assume right: "pp_e_exact_same_kind (pp_e_raw_operator ?x) (pp_e_raw_operator ?y)"
    then obtain V where reversible: "pp_e_exact_reversible V"
      and compose: "pp_e_raw_operator ?x = pp_e_raw_operator ?y \<circ> V"
      unfolding pp_e_exact_same_kind_def pp_e_exact_G_def by blast
    have vs: "V \<in> pp_e_exact_operator_stock" using reversible unfolding pp_e_exact_reversible_def by blast
    obtain W where wd: "W \<in> pp_e_closed_unary_denotations" and raw: "V = pp_e_raw_operator W"
      using vs unfolding pp_e_exact_operator_stock_def by blast
    have wm: "Elem W (pp_e_domain gb_unary)" by (rule pp_e_closed_unary_denotation_in_domain[OF wd])
    show "\<exists>W. Elem W (pp_e_domain gb_unary) \<and>
      pp_e_exact_reversible (pp_e_raw_operator W) \<and>
      pp_e_raw_operator ?x = pp_e_raw_operator ?y \<circ> pp_e_raw_operator W"
      using wm reversible compose raw by blast
  qed
  show ?thesis by (simp only: evaluation witnesses)
qed

text \<open>
  These are actual root truth clauses under the fixed generic internal
  interpretation, with arbitrary well-typed unary terms and typed old
  environments. The witness relation is X = Y ∘ Z, not Z ∘ Y. Neither
  X nor Y is silently assumed pure in the same-kind clause: their purity
  belongs to the surrounding L2 antecedent. The conclusion does not assert
  a corresponding clause at non-root worlds or under an enlarged stock.
\<close>

end
