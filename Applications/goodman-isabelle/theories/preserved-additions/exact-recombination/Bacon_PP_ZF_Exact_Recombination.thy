theory Bacon_PP_ZF_Exact_Recombination
  imports 
    "Goodman_Exact_Generic_Seed.Bacon_PP_ZF_Exact_Generic_Seed"
begin

section \<open>The exact Bacon model and the generic raw witness\<close>

lemma pp_e_raw_operator_mem_iff:
  assumes X: "Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and P: "Elem P (pp_e_domain Prop)"
  shows "i \<in> pp_e_raw_operator X (pp_n_bacon_extract P)
    \<longleftrightarrow> pp_e_holds (X \<acute> P) (rev i)"
proof -
  have recover: "pp_n_bacon_embed (pp_n_bacon_extract P) = P"
    by (rule pp_n_bacon_embed_extract) (use P in simp)
  show ?thesis
    unfolding pp_e_raw_operator_def
    using recover
    by (simp add: pp_n_bacon_extract_def)
qed

lemma pp_e_raw_operator_at_world_iff:
  assumes X: "Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and P: "Elem P (pp_e_domain Prop)"
  shows "rev w \<in> pp_e_raw_operator X (pp_n_bacon_extract P)
    \<longleftrightarrow> pp_e_holds (X \<acute> P) w"
  using pp_e_raw_operator_mem_iff[OF X P, of "rev w"] by simp

lemma pp_e_raw_box_at_world_iff:
  assumes X: "Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and P: "Elem P (pp_e_domain Prop)"
  shows "rev w \<in> pp_sem_box
      (pp_e_raw_operator X (pp_n_bacon_extract P))
    \<longleftrightarrow>
      (\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> P) v)"
proof
  assume box: "rev w \<in> pp_sem_box
      (pp_e_raw_operator X (pp_n_bacon_extract P))"
  show "\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> P) v"
  proof (intro allI impI)
    fix v
    assume "prefix w v"
    then obtain u where v: "v = w @ u"
      by (auto simp: prefix_def)
    have member:
        "rev u \<in> pp_view (rev w)
          (pp_e_raw_operator X (pp_n_bacon_extract P))"
      using box unfolding pp_sem_box_def by simp
    have raw:
        "rev v \<in> pp_e_raw_operator X (pp_n_bacon_extract P)"
      using member v by (simp add: pp_view_def rev_append)
    show "pp_e_holds (X \<acute> P) v"
      using pp_e_raw_operator_mem_iff[OF X P, of "rev v"] raw by simp
  qed
next
  assume necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> P) v"
  have all:
      "pp_view (rev w)
        (pp_e_raw_operator X (pp_n_bacon_extract P)) = UNIV"
  proof (rule set_eqI)
    fix i
    have future: "prefix w (w @ rev i)"
      by (simp add: prefix_def)
    have truth: "pp_e_holds (X \<acute> P) (w @ rev i)"
      using necessary future by blast
    have raw:
        "rev (w @ rev i) \<in>
          pp_e_raw_operator X (pp_n_bacon_extract P)"
      using pp_e_raw_operator_mem_iff[OF X P,
        of "rev (w @ rev i)"] truth by simp
    show "i \<in> pp_view (rev w)
        (pp_e_raw_operator X (pp_n_bacon_extract P)) \<longleftrightarrow>
      i \<in> UNIV"
      using raw by (simp add: pp_view_def rev_append)
  qed
  show "rev w \<in> pp_sem_box
      (pp_e_raw_operator X (pp_n_bacon_extract P))"
    using all unfolding pp_sem_box_def by simp
qed

lemma pp_e_fundamental_implies_raw_fundamental:
  assumes P: "Elem P (pp_e_domain Prop)"
    and fundamental:
      "pp_e_eqv Prop w P (pp_e_generic_seed_at w)"
  shows "pp_fundamental_at (rev w) pp_e_generic_raw_seed
    (pp_n_bacon_extract P)"
proof -
  have action:
      "pp_b_action Prop (rev w) P =
       pp_b_action Prop (rev w) (pp_e_generic_seed_at w)"
    using pp_e_eqv_iff_action_eq[
      OF P pp_e_generic_seed_at_in_domain, of w] fundamental by simp
  have P_extract:
      "pp_n_bacon_extract (pp_b_action Prop (rev w) P) =
       pp_view (rev w) (pp_n_bacon_extract P)"
    by (simp add: pp_n_bacon_extract_action pp_prop_action_def)
  have seed_extract:
      "pp_n_bacon_extract
          (pp_b_action Prop (rev w) (pp_e_generic_seed_at w)) =
       pp_view (rev w)
          (pp_n_bacon_extract (pp_e_generic_seed_at w))"
    by (simp add: pp_n_bacon_extract_action pp_prop_action_def)
  have extracts:
      "pp_view (rev w) (pp_n_bacon_extract P) =
       pp_n_bacon_extract pp_e_generic_root_seed"
    using arg_cong[OF action, where f=pp_n_bacon_extract]
      P_extract seed_extract pp_e_generic_seed_at_action
    by metis
  have root:
      "pp_n_bacon_extract pp_e_generic_root_seed =
       pp_e_generic_raw_seed"
    by (simp add: pp_e_generic_root_seed_def)
  show ?thesis
    unfolding pp_fundamental_at_def
    using extracts root by simp
qed

lemma pp_e_closed_den_universal_from_raw:
  assumes D: "Elem D (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and universal:
      "\<forall>Q. rev w \<in> pp_e_raw_operator D Q"
  shows "\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
    pp_e_holds (D \<acute> q) w"
proof (intro allI impI)
  fix q
  assume q: "Elem q (pp_e_domain Prop)"
  have raw:
      "rev w \<in> pp_e_raw_operator D (pp_n_bacon_extract q)"
    by (rule universal[rule_format])
  show "pp_e_holds (D \<acute> q) w"
    using pp_e_raw_operator_at_world_iff[OF D q, of w] raw by blast
qed

definition pp_e_unary_recombines_at ::
    "nat list \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_e_unary_recombines_at w X r \<longleftrightarrow>
    ((\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> r) v)
      \<longrightarrow>
      (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
        pp_e_holds (X \<acute> q) w))"

theorem pp_e_generic_seed_recombines_closed_logical_stock:
  assumes X: "Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and X_stock:
      "pp_e_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop) w X"
  shows "pp_e_unary_recombines_at w X (pp_e_generic_seed_at w)"
proof (unfold pp_e_unary_recombines_at_def, intro impI)
  assume necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_e_holds (X \<acute> pp_e_generic_seed_at w) v"
  obtain M where typed: "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    and logical: "pp_logical_vocabulary M"
    and XD:
      "pp_e_eqv (Prop \<rightarrow>\<^sub>o Prop) w X (pp_e_closed_den M)"
    using X_stock unfolding pp_e_closed_logical_stock_def by blast
  let ?D = "pp_e_closed_den M"
  let ?S = "pp_operator_index (pp_e_raw_operator ?D)"
  have D: "Elem ?D (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
    by (rule pp_e_closed_den_in_domain[OF typed])
  have D_stock: "?D \<in> pp_e_closed_unary_denotations"
    unfolding pp_e_closed_unary_denotations_def
    using typed logical by blast
  have S_stock: "?S \<in> pp_e_closed_classifier_indices"
    unfolding pp_e_closed_classifier_indices_def
    using D_stock by blast
  have classifier:
      "pp_e_raw_operator ?D = pp_classifier ?S"
    by (rule pp_e_closed_raw_operator_is_classifier[OF D_stock])
  have seed: "Elem (pp_e_generic_seed_at w) (pp_e_domain Prop)"
    by (rule pp_e_generic_seed_at_in_domain)
  have D_seed_necessary:
      "\<forall>v. prefix w v \<longrightarrow>
        pp_e_holds (?D \<acute> pp_e_generic_seed_at w) v"
  proof (intro allI impI)
    fix v
    assume future: "prefix w v"
    have XD_v:
        "pp_e_eqv (Prop \<rightarrow>\<^sub>o Prop) v X ?D"
      by (rule pp_e_eqv_persistent[OF XD future])
    have seed_refl:
        "pp_e_eqv Prop v
          (pp_e_generic_seed_at w) (pp_e_generic_seed_at w)"
      by (rule pp_e_eqv_reflexive[OF seed])
    have applications:
        "pp_e_eqv Prop v
          (X \<acute> pp_e_generic_seed_at w)
          (?D \<acute> pp_e_generic_seed_at w)"
      using XD_v seed seed seed_refl by simp
    have X_true:
        "pp_e_holds (X \<acute> pp_e_generic_seed_at w) v"
      using necessary future by blast
    show "pp_e_holds (?D \<acute> pp_e_generic_seed_at w) v"
      using pp_e_prop_eqv_at[OF applications, of v] X_true by simp
  qed
  have raw_fundamental:
      "pp_fundamental_at (rev w) pp_e_generic_raw_seed
        (pp_n_bacon_extract (pp_e_generic_seed_at w))"
    by (rule pp_e_fundamental_implies_raw_fundamental[
      OF seed pp_e_generic_seed_at_local])
  have raw_box:
      "rev w \<in> pp_sem_box
        (pp_e_raw_operator ?D
          (pp_n_bacon_extract (pp_e_generic_seed_at w)))"
    using pp_e_raw_box_at_world_iff[OF D seed, of w]
      D_seed_necessary by blast
  have guarded:
      "pp_guarded_unary_QLN_at_world
        (rev w) pp_e_generic_raw_seed ?S"
    using pp_e_generic_raw_seed_spec S_stock by blast
  have raw_box_classifier:
      "rev w \<in> pp_sem_box
        (pp_classifier ?S
          (pp_n_bacon_extract (pp_e_generic_seed_at w)))"
    using raw_box classifier by simp
  have universal_classifier:
      "\<forall>Q. rev w \<in> pp_classifier ?S Q"
    using guarded raw_fundamental raw_box_classifier
    unfolding pp_guarded_unary_QLN_at_world_def by blast
  have universal_raw:
      "\<forall>Q. rev w \<in> pp_e_raw_operator ?D Q"
    using universal_classifier classifier by simp
  have D_universal:
      "\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
        pp_e_holds (?D \<acute> q) w"
    by (rule pp_e_closed_den_universal_from_raw[OF D universal_raw])
  show "\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
      pp_e_holds (X \<acute> q) w"
  proof (intro allI impI)
    fix q
    assume q: "Elem q (pp_e_domain Prop)"
    have q_refl: "pp_e_eqv Prop w q q"
      by (rule pp_e_eqv_reflexive[OF q])
    have applications: "pp_e_eqv Prop w (X \<acute> q) (?D \<acute> q)"
      using XD q q q_refl by simp
    have D_true: "pp_e_holds (?D \<acute> q) w"
      using D_universal q by blast
    show "pp_e_holds (X \<acute> q) w"
      using pp_e_prop_eqv_at[OF applications, of w] D_true by simp
  qed
qed

theorem pp_e_generic_fundamental_recombines:
  assumes X: "Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and X_stock:
      "pp_e_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop) w X"
    and r: "Elem r (pp_e_domain Prop)"
    and r_fundamental:
      "pp_e_generic_fundamental_at Prop w r"
  shows "pp_e_unary_recombines_at w X r"
proof (unfold pp_e_unary_recombines_at_def, intro impI)
  assume necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> r) v"
  let ?seed = "pp_e_generic_seed_at w"
  have seed: "Elem ?seed (pp_e_domain Prop)"
    by (rule pp_e_generic_seed_at_in_domain)
  have r_seed: "pp_e_eqv Prop w r ?seed"
    using r_fundamental by simp
  have seed_necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> ?seed) v"
  proof (intro allI impI)
    fix v
    assume future: "prefix w v"
    have r_seed_v: "pp_e_eqv Prop v r ?seed"
      by (rule pp_e_eqv_persistent[OF r_seed future])
    have X_refl:
        "pp_e_eqv (Prop \<rightarrow>\<^sub>o Prop) v X X"
      by (rule pp_e_eqv_reflexive[OF X])
    have applications:
        "pp_e_eqv Prop v (X \<acute> r) (X \<acute> ?seed)"
      by (rule pp_e_app_respects[OF X_refl r seed r_seed_v])
    have r_true: "pp_e_holds (X \<acute> r) v"
      using necessary future by blast
    show "pp_e_holds (X \<acute> ?seed) v"
      using pp_e_prop_eqv_at[OF applications, of v] r_true by simp
  qed
  show "\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
      pp_e_holds (X \<acute> q) w"
    using pp_e_generic_seed_recombines_closed_logical_stock[
      OF X X_stock]
      seed_necessary
    unfolding pp_e_unary_recombines_at_def by blast
qed

section \<open>Object-language Recombination\<close>

lemma pp_e_generic_unary_recombination_holds_iff:
  "pp_e_holds
      (pp_e_eval pp_e_generic_internal_constants \<rho>
        pp_unary_recombination) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
      (\<forall>r. Elem r (pp_e_domain Prop) \<longrightarrow>
        (pp_e_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop) w X
          \<and> pp_e_generic_fundamental_at Prop w r)
        \<longrightarrow> pp_e_unary_recombines_at w X r))"
  by (simp add: pp_unary_recombination_def
      pp_pure_def pp_fun_def pp_e_classifier_holds
      pp_e_prop_eqv_truth_iff pp_e_eval_ObjBox_holds
      pp_e_unary_recombines_at_def extend_env.simps
      pp_e_three_extensions_index_two)

theorem pp_e_generic_unary_recombination_holds:
  "pp_e_holds
    (pp_e_eval pp_e_generic_internal_constants \<rho>
      pp_unary_recombination) w"
  unfolding pp_e_generic_unary_recombination_holds_iff
  using pp_e_generic_fundamental_recombines by blast

theorem pp_e_generic_unary_recombination_gvalid:
  "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
    pp_unary_recombination"
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_def
    GenericExactBaconConstants.pp_e_den_def
  using pp_e_generic_unary_recombination_holds by blast

lemma pp_e_generic_zeroary_recombination_holds:
  "pp_e_holds
    (pp_e_eval pp_e_generic_internal_constants \<rho>
      pp_zeroary_recombination) w"
proof -
  have base: "pp_e_env_typed [] \<rho>"
    by (simp add: pp_e_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_zeroary_recombination_def
    apply (simp only: pp_e_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix P
    assume P: "Elem P (pp_e_domain Prop)"
    have extended:
        "pp_e_env_typed [Prop] (extend_env P \<rho>)"
      using pp_e_env_typed_extend[OF base P] .
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have pure_iff:
        "pp_e_holds
          (pp_e_eval pp_e_generic_internal_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow> pp_e_closed_logical_stock Prop w P"
      using pp_e_generic_eval_pure_holds[
        OF var_type extended, of w] by simp
    have modal_T:
        "pp_e_eqv Prop w P (pp_zf_truth True)
          \<Longrightarrow> pp_e_holds P w"
    proof -
      assume box: "pp_e_eqv Prop w P (pp_zf_truth True)"
      have at_w:
          "pp_e_holds P w \<longleftrightarrow>
            pp_e_holds (pp_zf_truth True) w"
        using pp_e_prop_eqv_at[OF box, of w] by simp
      show "pp_e_holds P w"
        using at_w by simp
    qed
    show "pp_e_holds
        (pp_e_eval pp_e_generic_internal_constants
          (extend_env P \<rho>)
          (Imp
            (pp_pure Prop (Var 0))
            (Imp (\<box>\<^sub>o (Var 0)) (Var 0)))) w"
      unfolding pp_e_eval_Imp_holds
      using pure_iff modal_T
      by (simp add: pp_e_eval_ObjBox_holds)
  qed
qed

theorem pp_e_generic_zeroary_recombination_gvalid:
  "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
    pp_zeroary_recombination"
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_def
    GenericExactBaconConstants.pp_e_den_def
  using pp_e_generic_zeroary_recombination_holds by blast

section \<open>Exhaustion in Bacon's exact model\<close>

lemma pp_e_closed_prop_den_world_constant:
  assumes typed: "[] \<turnstile> M : Prop"
  shows "pp_e_holds (pp_e_closed_den M) v =
    pp_e_holds (pp_e_closed_den M) []"
proof -
  have invariant:
      "pp_b_action Prop (rev v) (pp_e_closed_den M) =
       pp_e_closed_den M"
    by (rule pp_e_closed_den_action_invariant[OF typed])
  have shifted:
      "pp_e_holds
        (pp_b_action Prop (rev v) (pp_e_closed_den M)) [] =
       pp_e_holds (pp_e_closed_den M) v"
    by simp
  show ?thesis
    using invariant shifted by simp
qed

lemma pp_e_closed_logical_prop_true_imp_box:
  assumes stock: "pp_e_closed_logical_stock Prop w P"
    and true: "pp_e_holds P w"
  shows "pp_e_eqv Prop w P (pp_zf_truth True)"
proof -
  obtain M where typed: "[] \<turnstile> M : Prop"
    and logical: "pp_logical_vocabulary M"
    and PM: "pp_e_eqv Prop w P (pp_e_closed_den M)"
    using stock unfolding pp_e_closed_logical_stock_def by blast
  have D_true_w: "pp_e_holds (pp_e_closed_den M) w"
    using pp_e_prop_eqv_at[OF PM, of w] true by simp
  have D_true_root: "pp_e_holds (pp_e_closed_den M) []"
    using D_true_w pp_e_closed_prop_den_world_constant[OF typed, of w]
    by simp
  show ?thesis
  proof (simp only: pp_e_eqv.simps, intro allI impI)
    fix v
    assume future: "prefix w v"
    have PM_v: "pp_e_eqv Prop v P (pp_e_closed_den M)"
      by (rule pp_e_eqv_persistent[OF PM future])
    have D_true_v: "pp_e_holds (pp_e_closed_den M) v"
      using D_true_root pp_e_closed_prop_den_world_constant[OF typed, of v]
      by simp
    show "pp_e_holds P v \<longleftrightarrow>
        pp_e_holds (pp_zf_truth True) v"
      using pp_e_prop_eqv_at[OF PM_v, of v] D_true_v by simp
  qed
qed

lemma pp_e_generic_zeroary_exhaustion_holds:
  "pp_e_holds
    (pp_e_eval pp_e_generic_internal_constants \<rho>
      pp_zeroary_exhaustion) w"
proof -
  have base: "pp_e_env_typed [] \<rho>"
    by (simp add: pp_e_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_zeroary_exhaustion_def
    apply (simp only: pp_e_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix P
    assume P: "Elem P (pp_e_domain Prop)"
    have extended: "pp_e_env_typed [Prop] (extend_env P \<rho>)"
      using pp_e_env_typed_extend[OF base P] .
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have pure_iff:
        "pp_e_holds
          (pp_e_eval pp_e_generic_internal_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow> pp_e_closed_logical_stock Prop w P"
      using pp_e_generic_eval_pure_holds[
        OF var_type extended, of w] by simp
    show "pp_e_holds
        (pp_e_eval pp_e_generic_internal_constants
          (extend_env P \<rho>)
          (Imp (pp_pure Prop (Var 0))
            (Imp (Var 0) (\<box>\<^sub>o (Var 0))))) w"
      unfolding pp_e_eval_Imp_holds
      using pure_iff pp_e_closed_logical_prop_true_imp_box
      by (simp add: pp_e_eval_ObjBox_holds)
  qed
qed

theorem pp_e_generic_zeroary_exhaustion_gvalid:
  "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
    pp_zeroary_exhaustion"
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_def
    GenericExactBaconConstants.pp_e_den_def
  using pp_e_generic_zeroary_exhaustion_holds by blast

definition pp_e_unary_exhausts_at ::
    "nat list \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_e_unary_exhausts_at w X r \<longleftrightarrow>
    ((\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
        pp_e_holds (X \<acute> q) w)
      \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> r) v))"

theorem pp_e_generic_fundamental_exhausts:
  assumes X: "Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and X_stock:
      "pp_e_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop) w X"
    and r: "Elem r (pp_e_domain Prop)"
    and r_fundamental:
      "pp_e_generic_fundamental_at Prop w r"
  shows "pp_e_unary_exhausts_at w X r"
proof (unfold pp_e_unary_exhausts_at_def, intro impI)
  assume universal_X:
      "\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
        pp_e_holds (X \<acute> q) w"
  obtain M where typed: "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    and logical: "pp_logical_vocabulary M"
    and XD:
      "pp_e_eqv (Prop \<rightarrow>\<^sub>o Prop) w X (pp_e_closed_den M)"
    using X_stock unfolding pp_e_closed_logical_stock_def by blast
  let ?D = "pp_e_closed_den M"
  let ?S = "pp_operator_index (pp_e_raw_operator ?D)"
  have D: "Elem ?D (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
    by (rule pp_e_closed_den_in_domain[OF typed])
  have D_stock: "?D \<in> pp_e_closed_unary_denotations"
    unfolding pp_e_closed_unary_denotations_def
    using typed logical by blast
  have S_stock: "?S \<in> pp_e_closed_classifier_indices"
    unfolding pp_e_closed_classifier_indices_def
    using D_stock by blast
  have classifier:
      "pp_e_raw_operator ?D = pp_classifier ?S"
    by (rule pp_e_closed_raw_operator_is_classifier[OF D_stock])
  have universal_D:
      "\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
        pp_e_holds (?D \<acute> q) w"
  proof (intro allI impI)
    fix q
    assume q: "Elem q (pp_e_domain Prop)"
    have q_refl: "pp_e_eqv Prop w q q"
      by (rule pp_e_eqv_reflexive[OF q])
    have applications: "pp_e_eqv Prop w (X \<acute> q) (?D \<acute> q)"
      by (rule pp_e_app_respects[OF XD q q q_refl])
    have X_true: "pp_e_holds (X \<acute> q) w"
      using universal_X q by blast
    show "pp_e_holds (?D \<acute> q) w"
      using pp_e_prop_eqv_at[OF applications, of w] X_true by simp
  qed
  have universal_raw:
      "\<forall>Q. rev w \<in> pp_e_raw_operator ?D Q"
  proof
    fix Q
    have embed: "Elem (pp_n_bacon_embed Q) (pp_e_domain Prop)"
      using pp_n_bacon_embed_in_domain by simp
    have truth: "pp_e_holds (?D \<acute> pp_n_bacon_embed Q) w"
      using universal_D embed by blast
    have bridge:
        "rev w \<in> pp_e_raw_operator ?D
            (pp_n_bacon_extract (pp_n_bacon_embed Q))
        \<longleftrightarrow>
          pp_e_holds (?D \<acute> pp_n_bacon_embed Q) w"
      by (rule pp_e_raw_operator_at_world_iff[OF D embed])
    show "rev w \<in> pp_e_raw_operator ?D Q"
      using bridge truth by simp
  qed
  have raw_fundamental:
      "pp_fundamental_at (rev w) pp_e_generic_raw_seed
        (pp_n_bacon_extract r)"
  proof (rule pp_e_fundamental_implies_raw_fundamental[OF r])
    show "pp_e_eqv Prop w r (pp_e_generic_seed_at w)"
      using r_fundamental by simp
  qed
  have guarded:
      "pp_guarded_unary_QLN_at_world
        (rev w) pp_e_generic_raw_seed ?S"
    using pp_e_generic_raw_seed_spec S_stock by blast
  have universal_classifier:
      "\<forall>Q. rev w \<in> pp_classifier ?S Q"
    using universal_raw classifier by simp
  have raw_box_classifier:
      "rev w \<in> pp_sem_box
        (pp_classifier ?S (pp_n_bacon_extract r))"
    using guarded raw_fundamental universal_classifier
    unfolding pp_guarded_unary_QLN_at_world_def by blast
  have raw_box:
      "rev w \<in> pp_sem_box
        (pp_e_raw_operator ?D (pp_n_bacon_extract r))"
    using raw_box_classifier classifier by simp
  have D_necessary:
      "\<forall>v. prefix w v \<longrightarrow> pp_e_holds (?D \<acute> r) v"
    using pp_e_raw_box_at_world_iff[OF D r, of w] raw_box by blast
  show "\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> r) v"
  proof (intro allI impI)
    fix v
    assume future: "prefix w v"
    have XD_v:
        "pp_e_eqv (Prop \<rightarrow>\<^sub>o Prop) v X ?D"
      by (rule pp_e_eqv_persistent[OF XD future])
    have r_refl: "pp_e_eqv Prop v r r"
      by (rule pp_e_eqv_reflexive[OF r])
    have applications: "pp_e_eqv Prop v (X \<acute> r) (?D \<acute> r)"
      by (rule pp_e_app_respects[OF XD_v r r r_refl])
    have D_true: "pp_e_holds (?D \<acute> r) v"
      using D_necessary future by blast
    show "pp_e_holds (X \<acute> r) v"
      using pp_e_prop_eqv_at[OF applications, of v] D_true by simp
  qed
qed

lemma pp_e_generic_unary_exhaustion_holds_iff:
  "pp_e_holds
      (pp_e_eval pp_e_generic_internal_constants \<rho>
        pp_unary_exhaustion) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
      (\<forall>r. Elem r (pp_e_domain Prop) \<longrightarrow>
        (pp_e_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop) w X
          \<and> pp_e_generic_fundamental_at Prop w r)
        \<longrightarrow> pp_e_unary_exhausts_at w X r))"
  by (simp add: pp_unary_exhaustion_def
      pp_pure_def pp_fun_def pp_e_classifier_holds
      pp_e_prop_eqv_truth_iff pp_e_eval_ObjBox_holds
      pp_e_unary_exhausts_at_def extend_env.simps
      pp_e_three_extensions_index_two)

theorem pp_e_generic_unary_exhaustion_holds:
  "pp_e_holds
    (pp_e_eval pp_e_generic_internal_constants \<rho>
      pp_unary_exhaustion) w"
  unfolding pp_e_generic_unary_exhaustion_holds_iff
  using pp_e_generic_fundamental_exhausts by blast

theorem pp_e_generic_unary_exhaustion_gvalid:
  "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
    pp_unary_exhaustion"
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_def
    GenericExactBaconConstants.pp_e_den_def
  using pp_e_generic_unary_exhaustion_holds by blast

section \<open>QLN\<close>

lemma pp_e_generic_zeroary_QLN_holds:
  "pp_e_holds
    (pp_e_eval pp_e_generic_internal_constants \<rho>
      pp_zeroary_QLN) w"
proof -
  have base: "pp_e_env_typed [] \<rho>"
    by (simp add: pp_e_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_zeroary_QLN_def
    apply (simp only: pp_e_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix P
    assume P: "Elem P (pp_e_domain Prop)"
    have extended: "pp_e_env_typed [Prop] (extend_env P \<rho>)"
      using pp_e_env_typed_extend[OF base P] .
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have pure_iff:
        "pp_e_holds
          (pp_e_eval pp_e_generic_internal_constants
            (extend_env P \<rho>) (pp_pure Prop (Var 0))) w
        \<longleftrightarrow> pp_e_closed_logical_stock Prop w P"
      using pp_e_generic_eval_pure_holds[
        OF var_type extended, of w] by simp
    have modal_T:
        "pp_e_eqv Prop w P (pp_zf_truth True)
          \<Longrightarrow> pp_e_holds P w"
      using pp_e_prop_eqv_truth_iff by blast
    show "pp_e_holds
        (pp_e_eval pp_e_generic_internal_constants
          (extend_env P \<rho>)
          (Imp (pp_pure Prop (Var 0))
            ((\<box>\<^sub>o (Var 0)) \<longleftrightarrow>\<^sub>o Var 0))) w"
      unfolding pp_e_eval_Imp_holds
      using pure_iff modal_T pp_e_closed_logical_prop_true_imp_box
      by (simp add: pp_e_eval_ObjBox_holds)
  qed
qed

theorem pp_e_generic_zeroary_QLN_gvalid:
  "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
    pp_zeroary_QLN"
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_def
    GenericExactBaconConstants.pp_e_den_def
  using pp_e_generic_zeroary_QLN_holds by blast

lemma pp_e_generic_unary_QLN_holds_iff:
  "pp_e_holds
      (pp_e_eval pp_e_generic_internal_constants \<rho>
        pp_unary_QLN) w
    \<longleftrightarrow>
    (\<forall>X.
      Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
      (\<forall>r. Elem r (pp_e_domain Prop) \<longrightarrow>
        (pp_e_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop) w X
          \<and> pp_e_generic_fundamental_at Prop w r)
        \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> r) v)
          \<longleftrightarrow>
          (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
            pp_e_holds (X \<acute> q) w))))"
  by (simp add: pp_unary_QLN_def
      pp_pure_def pp_fun_def pp_e_classifier_holds
      pp_e_prop_eqv_truth_iff pp_e_eval_ObjBox_holds
      extend_env.simps pp_e_three_extensions_index_two;
      blast)

theorem pp_e_generic_unary_QLN_holds:
  "pp_e_holds
    (pp_e_eval pp_e_generic_internal_constants \<rho>
      pp_unary_QLN) w"
  unfolding pp_e_generic_unary_QLN_holds_iff
proof (intro allI impI)
  fix X r
  assume X: "Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and r: "Elem r (pp_e_domain Prop)"
    and both:
      "pp_e_closed_logical_stock (Prop \<rightarrow>\<^sub>o Prop) w X \<and>
       pp_e_generic_fundamental_at Prop w r"
  have recombination: "pp_e_unary_recombines_at w X r"
    by (rule pp_e_generic_fundamental_recombines[
      OF X both[THEN conjunct1] r both[THEN conjunct2]])
  have exhaustion: "pp_e_unary_exhausts_at w X r"
    by (rule pp_e_generic_fundamental_exhausts[
      OF X both[THEN conjunct1] r both[THEN conjunct2]])
  show "((\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> r) v) =
      (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
        pp_e_holds (X \<acute> q) w))"
    using recombination exhaustion
    unfolding pp_e_unary_recombines_at_def pp_e_unary_exhausts_at_def
    by blast
qed

theorem pp_e_generic_unary_QLN_gvalid:
  "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
    pp_unary_QLN"
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_def
    GenericExactBaconConstants.pp_e_den_def
  using pp_e_generic_unary_QLN_holds by blast

section \<open>The exact background package\<close>

theorem pp_e_generic_recombination_background_gvalid:
  "GenericExactBaconConstants.ExactBaconHenkin.gvalid_set
    pp_recombination_background_axioms"
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_recombination_background_axioms"
  from A consider
      (purity) "A \<in> pp_purity_schema"
    | (application) "A \<in> pp_application_closure_schema"
    | (unique) "A = pp_unique_fundamental Prop"
    | (no_other) "A \<in> pp_no_other_fundamentals_schema"
    | (zeroary) "A = pp_zeroary_recombination"
    | (unary) "A = pp_unary_recombination"
    unfolding pp_recombination_background_axioms_def
      pp_background_axioms_def by blast
  then show "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma> A"
  proof cases
    case purity
    then obtain \<sigma> M where typed: "[] \<turnstile> M : \<sigma>"
      and logical: "pp_logical_vocabulary M"
      and A_def: "A = pp_pure \<sigma> M"
      unfolding pp_purity_schema_def by blast
    show ?thesis
      unfolding A_def
      by (rule pp_e_generic_closed_logical_purity_gvalid[
        OF typed logical])
  next
    case application
    then obtain \<sigma> \<tau> where
        A_def: "A = pp_application_closure \<sigma> \<tau>"
      unfolding pp_application_closure_schema_def by blast
    show ?thesis
      unfolding A_def
      by (rule pp_e_generic_closed_logical_application_closure_gvalid)
  next
    case unique
    show ?thesis
      unfolding unique
      by (rule pp_e_generic_unique_fundamental_gvalid)
  next
    case no_other
    then obtain \<sigma> where nonprop: "\<sigma> \<noteq> Prop"
      and A_def: "A = pp_no_fundamentals \<sigma>"
      unfolding pp_no_other_fundamentals_schema_def by blast
    show ?thesis
      unfolding A_def
      by (rule pp_e_generic_no_fundamentals_gvalid[OF nonprop])
  next
    case zeroary
    show ?thesis
      unfolding zeroary
      by (rule pp_e_generic_zeroary_recombination_gvalid)
  next
    case unary
    show ?thesis
      unfolding unary
      by (rule pp_e_generic_unary_recombination_gvalid)
  qed
qed

theorem pp_e_generic_full_QLN_background_gvalid:
  "GenericExactBaconConstants.ExactBaconHenkin.gvalid_set
    pp_full_QLN_background_axioms"
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def
proof (intro allI impI)
  fix \<Gamma> A
  assume A: "A \<in> pp_full_QLN_background_axioms"
  then consider
      (recombination) "A \<in> pp_recombination_background_axioms"
    | (zeroary) "A = pp_zeroary_exhaustion"
    | (unary) "A = pp_unary_exhaustion"
    unfolding pp_full_QLN_background_axioms_def
      pp_exhaustion_axioms_def by blast
  then show "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma> A"
  proof cases
    case recombination
    show ?thesis
      using pp_e_generic_recombination_background_gvalid recombination
      unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def
      by blast
  next
    case zeroary
    show ?thesis
      unfolding zeroary
      by (rule pp_e_generic_zeroary_exhaustion_gvalid)
  next
    case unary
    show ?thesis
      unfolding unary
      by (rule pp_e_generic_unary_exhaustion_gvalid)
  qed
qed

lemma pp_e_generic_target_PP_holds_iff:
  "pp_e_holds
      (pp_e_eval pp_e_generic_internal_constants \<rho>
        pp_target_PP) w
    \<longleftrightarrow>
    pp_e_closed_logical_stock
      ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
      (pp_e_classifier (Prop \<rightarrow>\<^sub>o Prop)
        (pp_e_closed_logical_stock
          (Prop \<rightarrow>\<^sub>o Prop)))"
proof -
  let ?U = "Prop \<rightarrow>\<^sub>o Prop"
  let ?C =
    "pp_e_classifier ?U (pp_e_closed_logical_stock ?U)"
  have C: "Elem ?C (pp_e_domain (?U \<rightarrow>\<^sub>o Prop))"
    using pp_e_classifier_in_domain[
      OF pp_e_closed_logical_stock_admissible] .
  show ?thesis
    unfolding pp_target_PP_def pp_purity_of_pure_def pp_pure_def
    using pp_e_classifier_holds[
      OF C, of "pp_e_closed_logical_stock (?U \<rightarrow>\<^sub>o Prop)" w]
    by simp
qed

theorem pp_e_generic_full_QLN_PP_gvalid_iff:
  "GenericExactBaconConstants.ExactBaconHenkin.gvalid_set
      pp_full_QLN_PP_axioms
    \<longleftrightarrow>
    (\<forall>w.
      pp_e_closed_logical_stock
        ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_e_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (pp_e_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop))))"
proof
  assume valid:
      "GenericExactBaconConstants.ExactBaconHenkin.gvalid_set
        pp_full_QLN_PP_axioms"
  have target:
      "GenericExactBaconConstants.ExactBaconHenkin.gvalid [] pp_target_PP"
    using valid
    unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def
      pp_full_QLN_PP_axioms_def by blast
  show "\<forall>w.
      pp_e_closed_logical_stock
        ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_e_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (pp_e_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop)))"
  proof
    fix w
    have target_holds:
        "pp_e_holds
          (pp_e_eval pp_e_generic_internal_constants
            (pp_e_list_env []) pp_target_PP) w"
      using target
      unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_def
        GenericExactBaconConstants.pp_e_den_def by simp
    show "pp_e_closed_logical_stock
        ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_e_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (pp_e_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop)))"
      using target_holds
      unfolding pp_e_generic_target_PP_holds_iff .
  qed
next
  assume target:
      "\<forall>w.
        pp_e_closed_logical_stock
          ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
          (pp_e_classifier (Prop \<rightarrow>\<^sub>o Prop)
            (pp_e_closed_logical_stock
              (Prop \<rightarrow>\<^sub>o Prop)))"
  show "GenericExactBaconConstants.ExactBaconHenkin.gvalid_set
      pp_full_QLN_PP_axioms"
    unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def
  proof (intro allI impI)
    fix \<Gamma> A
    assume A: "A \<in> pp_full_QLN_PP_axioms"
    then consider
        (target_case) "A = pp_target_PP"
      | (background) "A \<in> pp_full_QLN_background_axioms"
      unfolding pp_full_QLN_PP_axioms_def by blast
    then show "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma> A"
    proof cases
      case target_case
      show ?thesis
        unfolding target_case
          GenericExactBaconConstants.ExactBaconHenkin.gvalid_def
          GenericExactBaconConstants.pp_e_den_def
        using target pp_e_generic_target_PP_holds_iff by blast
    next
      case background
      show ?thesis
        using pp_e_generic_full_QLN_background_gvalid background
        unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def
        by blast
    qed
  qed
qed

end
