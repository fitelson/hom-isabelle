theory Bacon_PP_ZF_Exact_Generic_Seed
  imports 
    "Goodman_Exact_Stock_Action.Bacon_PP_ZF_Exact_Logical_Stock_Action"
begin

section \<open>A generic fundamental proposition in Bacon's exact model\<close>

definition pp_e_raw_operator ::
    "ZF \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop)"
where
  "pp_e_raw_operator X P =
    pp_n_bacon_extract (X \<acute> pp_n_bacon_embed P)"

definition pp_e_closed_unary_denotations :: "ZF set" where
  "pp_e_closed_unary_denotations =
    {X. \<exists>M.
      [] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop) \<and>
      pp_logical_vocabulary M \<and>
      X = pp_e_closed_den M}"

lemma pp_e_closed_unary_denotations_countable:
  "countable pp_e_closed_unary_denotations"
proof -
  let ?T = "{M. [] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop) \<and>
    pp_logical_vocabulary M}"
  have terms: "countable ?T" by simp
  have representation: "pp_e_closed_unary_denotations =
      image pp_e_closed_den ?T"
    unfolding pp_e_closed_unary_denotations_def by auto
  show ?thesis
    unfolding representation
    by (rule countable_image[OF terms])
qed

lemma pp_e_closed_unary_denotation_in_domain:
  assumes "X \<in> pp_e_closed_unary_denotations"
  shows "Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
  using assms pp_e_closed_den_in_domain
  unfolding pp_e_closed_unary_denotations_def by blast

lemma pp_e_raw_operator_equivariant:
  assumes X: "Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
    and invariant:
      "\<And>i. pp_b_action (Prop \<rightarrow>\<^sub>o Prop) i X = X"
  shows "pp_equivariant_operator (pp_e_raw_operator X)"
proof (unfold pp_equivariant_operator_def, intro allI)
  fix i P
  have embed: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)"
    using pp_n_bacon_embed_in_domain by simp
  have application:
      "pp_b_action Prop i (X \<acute> pp_n_bacon_embed P) =
       pp_b_action (Prop \<rightarrow>\<^sub>o Prop) i X \<acute>
         pp_b_action Prop i (pp_n_bacon_embed P)"
    using pp_b_application_substitution_exact[OF X embed, of i]
    by (simp add: pp_prop_action_def)
  have embed_view:
      "pp_b_action Prop i (pp_n_bacon_embed P) =
       pp_n_bacon_embed (pp_view i P)"
    using pp_n_prop_action_is_bacon_division[of i P]
    by (simp add: pp_prop_action_def)
  show "pp_view i (pp_e_raw_operator X P) =
      pp_e_raw_operator X (pp_view i P)"
    unfolding pp_e_raw_operator_def
    using pp_n_bacon_extract_action[
        of i "X \<acute> pp_n_bacon_embed P"]
      application invariant[of i] embed_view
    by (simp add: pp_prop_action_def)
qed

theorem pp_e_closed_raw_operator_equivariant:
  assumes X: "X \<in> pp_e_closed_unary_denotations"
  shows "pp_equivariant_operator (pp_e_raw_operator X)"
proof -
  obtain M where typed:
      "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    and X_def: "X = pp_e_closed_den M"
    using X unfolding pp_e_closed_unary_denotations_def by blast
  have domain: "Elem X (pp_e_domain (Prop \<rightarrow>\<^sub>o Prop))"
    by (rule pp_e_closed_unary_denotation_in_domain[OF X])
  have invariant:
      "\<And>i. pp_b_action (Prop \<rightarrow>\<^sub>o Prop) i X = X"
    unfolding X_def
    by (rule pp_e_closed_den_action_invariant[OF typed])
  show ?thesis
    by (rule pp_e_raw_operator_equivariant[OF domain invariant])
qed

definition pp_e_closed_classifier_indices :: "pp_sem_prop set set" where
  "pp_e_closed_classifier_indices =
    image pp_operator_index
      (image pp_e_raw_operator pp_e_closed_unary_denotations)"

lemma pp_e_closed_classifier_indices_countable:
  "countable pp_e_closed_classifier_indices"
  unfolding pp_e_closed_classifier_indices_def
  using pp_e_closed_unary_denotations_countable
  by simp

lemma pp_e_closed_raw_operator_is_classifier:
  assumes X: "X \<in> pp_e_closed_unary_denotations"
  shows "pp_e_raw_operator X =
    pp_classifier (pp_operator_index (pp_e_raw_operator X))"
  using pp_equivariant_operator_is_classifier[
    OF pp_e_closed_raw_operator_equivariant[OF X]] .

lemma pp_e_generic_raw_seed_exists:
  "\<exists>r. \<forall>S \<in> pp_e_closed_classifier_indices. \<forall>i.
    pp_guarded_unary_QLN_at_world i r S"
  by (rule pp_countable_stock_has_all_worlds_guarded_QLN_witness[
      OF pp_e_closed_classifier_indices_countable])

definition pp_e_generic_raw_seed :: pp_sem_prop where
  "pp_e_generic_raw_seed =
    (SOME r. \<forall>S \<in> pp_e_closed_classifier_indices. \<forall>i.
      pp_guarded_unary_QLN_at_world i r S)"

lemma pp_e_generic_raw_seed_spec:
  "\<forall>S \<in> pp_e_closed_classifier_indices. \<forall>i.
    pp_guarded_unary_QLN_at_world i pp_e_generic_raw_seed S"
  unfolding pp_e_generic_raw_seed_def
  by (rule someI_ex[OF pp_e_generic_raw_seed_exists])

definition pp_e_generic_root_seed :: ZF where
  "pp_e_generic_root_seed =
    pp_n_bacon_embed pp_e_generic_raw_seed"

lemma pp_e_generic_root_seed_in_domain:
  "Elem pp_e_generic_root_seed (pp_e_domain Prop)"
  unfolding pp_e_generic_root_seed_def
  using pp_n_bacon_embed_in_domain by simp

definition pp_e_generic_seed_at :: "nat list \<Rightarrow> ZF" where
  "pp_e_generic_seed_at w =
    pp_b_lift Prop (rev w) pp_e_generic_root_seed"

lemma pp_e_generic_seed_at_in_domain:
  "Elem (pp_e_generic_seed_at w) (pp_e_domain Prop)"
  unfolding pp_e_generic_seed_at_def
  by (rule pp_b_structure_lift_closed[
      OF pp_b_mset_structure_all pp_e_generic_root_seed_in_domain])

lemma pp_e_generic_seed_at_action:
  "pp_b_action Prop (rev w) (pp_e_generic_seed_at w) =
    pp_e_generic_root_seed"
  unfolding pp_e_generic_seed_at_def
  by (rule pp_b_structure_action_lift[
      OF pp_b_mset_structure_all pp_e_generic_root_seed_in_domain])

lemma pp_e_generic_seed_at_local:
  "pp_e_eqv Prop w (pp_e_generic_seed_at w)
    (pp_e_generic_seed_at w)"
  by (rule pp_e_eqv_reflexive[OF pp_e_generic_seed_at_in_domain])

section \<open>The generic-seed internal interpretation\<close>

fun pp_e_generic_fundamental_at ::
    "otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_e_generic_fundamental_at Ind w x = False"
| "pp_e_generic_fundamental_at Prop w x =
    pp_e_eqv Prop w x (pp_e_generic_seed_at w)"
| "pp_e_generic_fundamental_at (\<sigma> \<rightarrow>\<^sub>o \<tau>) w x =
    False"

lemma pp_e_generic_fundamental_admissible:
  "pp_e_predicate_admissible \<sigma>
    (pp_e_generic_fundamental_at \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    by (simp add: pp_e_predicate_admissible_def)
next
  case Prop
  show ?thesis
    unfolding Prop pp_e_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_e_domain Prop)"
      and y: "Elem y (pp_e_domain Prop)"
      and xy: "pp_e_eqv Prop w x y"
      and wv: "prefix w v"
    have xy_v: "pp_e_eqv Prop v x y"
      using pp_e_eqv_persistent[OF xy wv] .
    have seed_refl:
        "pp_e_eqv Prop v
          (pp_e_generic_seed_at v) (pp_e_generic_seed_at v)"
      using pp_e_eqv_reflexive[
        OF pp_e_generic_seed_at_in_domain] .
    show "pp_e_generic_fundamental_at Prop v x =
        pp_e_generic_fundamental_at Prop v y"
      using pp_e_eqv_congruence[
        OF x y pp_e_generic_seed_at_in_domain
          pp_e_generic_seed_at_in_domain xy_v seed_refl]
      by simp
  qed
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis
    by (simp add: pp_e_predicate_admissible_def)
qed

fun pp_e_generic_internal_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_e_generic_internal_constants c Ind = pp_e_default Ind"
| "pp_e_generic_internal_constants c Prop = pp_e_default Prop"
| "pp_e_generic_internal_constants c (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    (if c = pp_pure_name \<and> \<tau> = Prop
     then pp_e_classifier \<sigma> (pp_e_closed_logical_stock \<sigma>)
     else if c = pp_fun_name \<and> \<tau> = Prop
     then pp_e_classifier \<sigma> (pp_e_generic_fundamental_at \<sigma>)
     else pp_e_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))"

lemma pp_e_generic_internal_constants_typed:
  "Elem (pp_e_generic_internal_constants c \<sigma>)
    (pp_e_domain \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    using pp_e_default_in_domain[of Ind] by simp
next
  case Prop
  then show ?thesis
    using pp_e_default_in_domain[of Prop] by simp
next
  case (Arr \<sigma> \<tau>)
  have pure_classifier:
      "Elem
        (pp_e_classifier \<sigma> (pp_e_closed_logical_stock \<sigma>))
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_e_classifier_in_domain[
      OF pp_e_closed_logical_stock_admissible] .
  have fun_classifier:
      "Elem
        (pp_e_classifier \<sigma> (pp_e_generic_fundamental_at \<sigma>))
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_e_classifier_in_domain[
      OF pp_e_generic_fundamental_admissible] .
  have default:
      "Elem (pp_e_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using pp_e_default_in_domain .
  show ?thesis
    using Arr pure_classifier fun_classifier default by auto
qed

interpretation GenericExactBaconConstants:
  pp_e_constants pp_e_generic_internal_constants
  by standard (rule pp_e_generic_internal_constants_typed)

lemma pp_e_generic_eval_Pure[simp]:
  "pp_e_eval pp_e_generic_internal_constants \<rho> (pp_Pure \<sigma>) =
    pp_e_classifier \<sigma> (pp_e_closed_logical_stock \<sigma>)"
  by (simp add: pp_Pure_def pp_pure_name_def)

lemma pp_e_generic_eval_Fun[simp]:
  "pp_e_eval pp_e_generic_internal_constants \<rho> (pp_Fun \<sigma>) =
    pp_e_classifier \<sigma> (pp_e_generic_fundamental_at \<sigma>)"
  by (simp add: pp_Fun_def pp_fun_name_def
      pp_pure_name_def)

lemma pp_e_generic_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds
      (pp_e_eval pp_e_generic_internal_constants \<rho>
        (pp_pure \<sigma> M)) w
    \<longleftrightarrow>
      pp_e_closed_logical_stock \<sigma> w
        (pp_e_eval pp_e_generic_internal_constants \<rho> M)"
proof -
  have argument:
      "Elem (pp_e_eval pp_e_generic_internal_constants \<rho> M)
        (pp_e_domain \<sigma>)"
    using GenericExactBaconConstants.pp_e_eval_type[OF typed env]
    by (simp add: pp_e_dom_def)
  show ?thesis
    unfolding pp_pure_def
    using pp_e_classifier_holds[
      OF argument, of "pp_e_closed_logical_stock \<sigma>" w]
    by simp
qed

lemma pp_e_generic_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds
      (pp_e_eval pp_e_generic_internal_constants \<rho>
        (pp_fun \<sigma> M)) w
    \<longleftrightarrow>
      pp_e_generic_fundamental_at \<sigma> w
        (pp_e_eval pp_e_generic_internal_constants \<rho> M)"
proof -
  have argument:
      "Elem (pp_e_eval pp_e_generic_internal_constants \<rho> M)
        (pp_e_domain \<sigma>)"
    using GenericExactBaconConstants.pp_e_eval_type[OF typed env]
    by (simp add: pp_e_dom_def)
  show ?thesis
    unfolding pp_fun_def
    using pp_e_classifier_holds[
      OF argument, of "pp_e_generic_fundamental_at \<sigma>" w]
    by simp
qed

lemma pp_e_generic_unique_fundamental_holds:
  "pp_e_holds
    (pp_e_eval pp_e_generic_internal_constants \<rho>
      (pp_unique_fundamental Prop)) w"
proof -
  let ?r = "pp_e_generic_seed_at w"
  have base: "pp_e_env_typed [] \<rho>"
    by (simp add: pp_e_env_typed_def lookup_def)
  have r_env:
      "pp_e_env_typed [Prop] (extend_env ?r \<rho>)"
    using pp_e_env_typed_extend[
      OF base pp_e_generic_seed_at_in_domain] .
  have r_is_fundamental:
      "pp_e_holds
        (pp_e_eval pp_e_generic_internal_constants
          (extend_env ?r \<rho>) (pp_fun Prop (Var 0))) w"
  proof -
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have rr: "pp_e_eqv Prop w ?r ?r"
      using pp_e_eqv_reflexive[
        OF pp_e_generic_seed_at_in_domain] .
    show ?thesis
      using pp_e_generic_eval_fun_holds[
        OF var_type r_env, of w] rr
      by simp
  qed
  have uniqueness:
      "\<forall>y. Elem y (pp_e_domain Prop) \<longrightarrow>
        pp_e_holds
          (pp_e_eval pp_e_generic_internal_constants
            (extend_env y (extend_env ?r \<rho>))
            (Imp
              (pp_fun Prop (Var 0))
              (Eq Prop (Var 0) (Var 1)))) w"
  proof (intro allI impI)
    fix y
    assume y: "Elem y (pp_e_domain Prop)"
    have yr_env:
        "pp_e_env_typed [Prop, Prop]
          (extend_env y (extend_env ?r \<rho>))"
      using pp_e_env_typed_extend[OF r_env y] .
    have y_type: "[Prop, Prop] \<turnstile> Var 0 : Prop"
      by simp
    have fun_iff:
        "pp_e_holds
          (pp_e_eval pp_e_generic_internal_constants
            (extend_env y (extend_env ?r \<rho>))
            (pp_fun Prop (Var 0))) w
        \<longleftrightarrow> pp_e_eqv Prop w y ?r"
      using pp_e_generic_eval_fun_holds[
        OF y_type yr_env, of w] by simp
    have eq_iff:
        "pp_e_holds
          (pp_e_eval pp_e_generic_internal_constants
            (extend_env y (extend_env ?r \<rho>))
            (Eq Prop (Var 0) (Var 1))) w
        \<longleftrightarrow> pp_e_eqv Prop w y ?r"
      by simp
    show "pp_e_holds
        (pp_e_eval pp_e_generic_internal_constants
          (extend_env y (extend_env ?r \<rho>))
          (Imp
            (pp_fun Prop (Var 0))
            (Eq Prop (Var 0) (Var 1)))) w"
      unfolding pp_e_eval_Imp_holds
      using fun_iff eq_iff by blast
  qed
  show ?thesis
    unfolding pp_unique_fundamental_def
    apply (simp only: pp_e_eval_Exists_holds)
    apply (rule exI[of _ ?r])
    using pp_e_generic_seed_at_in_domain
      r_is_fundamental uniqueness
    by (simp only: pp_e_eval_Conj_holds
        pp_e_eval_Forall_holds)
qed

lemma pp_e_generic_no_fundamentals_holds:
  assumes nonprop: "\<sigma> \<noteq> Prop"
  shows "pp_e_holds
    (pp_e_eval pp_e_generic_internal_constants \<rho>
      (pp_no_fundamentals \<sigma>)) w"
proof -
  have base: "pp_e_env_typed [] \<rho>"
    by (simp add: pp_e_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_no_fundamentals_def
    apply (simp only: pp_e_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix x
    assume x: "Elem x (pp_e_domain \<sigma>)"
    have extended:
        "pp_e_env_typed [\<sigma>] (extend_env x \<rho>)"
      using pp_e_env_typed_extend[OF base x] .
    have var_type: "[\<sigma>] \<turnstile> Var 0 : \<sigma>"
      by simp
    have fun_false:
        "\<not> pp_e_generic_fundamental_at \<sigma> w x"
      using nonprop by (cases \<sigma>) auto
    have fun_iff:
        "pp_e_holds
          (pp_e_eval pp_e_generic_internal_constants
            (extend_env x \<rho>) (pp_fun \<sigma> (Var 0))) w
        \<longleftrightarrow> pp_e_generic_fundamental_at \<sigma> w x"
      using pp_e_generic_eval_fun_holds[
        OF var_type extended, of w] by simp
    have not_fun:
        "\<not> pp_e_holds
          (pp_e_eval pp_e_generic_internal_constants
            (extend_env x \<rho>) (pp_fun \<sigma> (Var 0))) w"
      using fun_iff fun_false by blast
    show "pp_e_holds
        (pp_e_eval pp_e_generic_internal_constants
          (extend_env x \<rho>)
          (Neg (pp_fun \<sigma> (Var 0)))) w"
      using pp_e_eval_Neg_holds[
        of pp_e_generic_internal_constants
          "extend_env x \<rho>" "pp_fun \<sigma> (Var 0)" w]
        not_fun
      by blast
  qed
qed

theorem pp_e_generic_unique_fundamental_gvalid:
  "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
    (pp_unique_fundamental Prop)"
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_def
    GenericExactBaconConstants.pp_e_den_def
  using pp_e_generic_unique_fundamental_holds by blast

theorem pp_e_generic_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
    (pp_no_fundamentals \<sigma>)"
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_def
    GenericExactBaconConstants.pp_e_den_def
  using pp_e_generic_no_fundamentals_holds[OF assms]
  by blast

theorem pp_e_generic_closed_logical_purity_gvalid:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
    (pp_pure \<sigma> M)"
proof (rule GenericExactBaconConstants.ExactBaconHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_e_dom \<Gamma>) env"
  have eval_pure:
      "pp_e_holds
        (pp_e_eval pp_e_generic_internal_constants
          (pp_e_list_env env) (pp_pure \<sigma> M)) w
      \<longleftrightarrow>
        pp_e_closed_logical_stock \<sigma> w
          (pp_e_eval pp_e_generic_internal_constants
            (pp_e_list_env env) M)"
    using pp_e_generic_eval_pure_holds[
      OF typed pp_e_empty_env_typed, where w=w] .
  have stock:
      "pp_e_closed_logical_stock \<sigma> w
        (pp_e_eval pp_e_generic_internal_constants
          (pp_e_list_env env) M)"
    using pp_e_closed_logical_stock_contains_eval[
      OF typed logical] .
  show "pp_e_holds
      (GenericExactBaconConstants.pp_e_den
        (pp_pure \<sigma> M) env) w"
    unfolding GenericExactBaconConstants.pp_e_den_def
    using eval_pure stock by blast
qed

lemma pp_e_generic_closed_logical_application_closure_holds_iff:
  "pp_e_holds
      (pp_e_eval pp_e_generic_internal_constants \<rho>
        (pp_application_closure \<sigma> \<tau>)) w
    \<longleftrightarrow>
    (\<forall>f.
      Elem f (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      (\<forall>x. Elem x (pp_e_domain \<sigma>) \<longrightarrow>
        pp_e_closed_logical_stock
          (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f
        \<and> pp_e_closed_logical_stock \<sigma> w x
        \<longrightarrow>
        pp_e_closed_logical_stock \<tau> w (f \<acute> x)))"
  by (simp add: pp_application_closure_def pp_pure_def
      pp_e_classifier_holds pp_e_app_closed
      extend_env.simps)

theorem pp_e_generic_closed_logical_application_closure_gvalid:
  "GenericExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule GenericExactBaconConstants.ExactBaconHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_e_dom \<Gamma>) env"
  show "pp_e_holds
      (GenericExactBaconConstants.pp_e_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding GenericExactBaconConstants.pp_e_den_def
      pp_e_generic_closed_logical_application_closure_holds_iff
    using pp_e_closed_logical_stock_application_closed
    by blast
qed

end
