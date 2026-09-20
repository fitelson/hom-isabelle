theory Goodman_Exact_Basis_Seed
  imports Goodman_Exact_Invariant_Basis
begin

section \<open>Raw unary operators and the countable requirements for one generic seed\<close>

definition gi_basis_raw_stock :: "(otype \<Rightarrow> ZF set) \<Rightarrow> pp_e_operator set" where
  "gi_basis_raw_stock B = pp_e_raw_operator ` B gb_unary"

definition gi_basis_classifier_indices :: "(otype \<Rightarrow> ZF set) \<Rightarrow> pp_sem_prop set set" where
  "gi_basis_classifier_indices B = pp_operator_index ` gi_basis_raw_stock B"

definition gi_basis_equalizer_indices :: "(otype \<Rightarrow> ZF set) \<Rightarrow> pp_sem_prop set set" where
  "gi_basis_equalizer_indices B =
    (\<lambda>(F,H). pp_e_operator_equalizer F H) ` (gi_basis_raw_stock B \<times> gi_basis_raw_stock B)"

definition gi_basis_generic_indices :: "(otype \<Rightarrow> ZF set) \<Rightarrow> pp_sem_prop set set" where
  "gi_basis_generic_indices B = gi_basis_classifier_indices B \<union> gi_basis_equalizer_indices B"

definition gi_basis_raw_seed :: "(otype \<Rightarrow> ZF set) \<Rightarrow> pp_sem_prop" where
  "gi_basis_raw_seed B = (SOME r. \<forall>S\<in>gi_basis_generic_indices B. \<forall>i.
    pp_guarded_unary_QLN_at_world i r S)"

definition gi_basis_root_seed :: "(otype \<Rightarrow> ZF set) \<Rightarrow> ZF" where
  "gi_basis_root_seed B = pp_n_bacon_embed (gi_basis_raw_seed B)"

definition gi_basis_seed_at :: "(otype \<Rightarrow> ZF set) \<Rightarrow> nat list \<Rightarrow> ZF" where
  "gi_basis_seed_at B w = pp_b_lift Prop (rev w) (gi_basis_root_seed B)"

fun gi_basis_fundamental_at ::
  "(otype \<Rightarrow> ZF set) \<Rightarrow> otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool" where
  "gi_basis_fundamental_at B Ind w x = False"
| "gi_basis_fundamental_at B Prop w x = pp_e_eqv Prop w x (gi_basis_seed_at B w)"
| "gi_basis_fundamental_at B (Arr \<sigma> \<tau>) w x = False"

fun gi_basis_internal_constants :: "(otype \<Rightarrow> ZF set) \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF" where
  "gi_basis_internal_constants B c Ind = pp_e_default Ind"
| "gi_basis_internal_constants B c Prop = pp_e_default Prop"
| "gi_basis_internal_constants B c (Arr \<sigma> \<tau>) =
    (if c = pp_pure_name \<and> \<tau> = Prop then pp_e_classifier \<sigma> (gi_basis_pure B \<sigma>)
     else if c = pp_fun_name \<and> \<tau> = Prop then pp_e_classifier \<sigma> (gi_basis_fundamental_at B \<sigma>)
     else pp_e_default (Arr \<sigma> \<tau>))"

context gi_exact_invariant_basis
begin

lemma gi_basis_raw_stock_countable:
  "countable (gi_basis_raw_stock B)"
  unfolding gi_basis_raw_stock_def by (rule countable_image[OF basis_countable])

lemma gi_basis_raw_stock_equivariant:
  assumes member: "F \<in> gi_basis_raw_stock B"
  shows "pp_equivariant_operator F"
proof -
  obtain a where ab: "a \<in> B gb_unary" and raw: "F = pp_e_raw_operator a"
    using member unfolding gi_basis_raw_stock_def by blast
  show ?thesis unfolding raw
    by (rule pp_e_raw_operator_equivariant[OF basis_member[OF ab]]; rule basis_invariant[OF ab])
qed

lemma gi_basis_raw_stock_classifier:
  "F \<in> gi_basis_raw_stock B \<Longrightarrow> F = pp_classifier (pp_operator_index F)"
  by (rule pp_equivariant_operator_is_classifier, rule gi_basis_raw_stock_equivariant; assumption)

lemma gi_basis_classifier_indices_countable:
  "countable (gi_basis_classifier_indices B)"
  unfolding gi_basis_classifier_indices_def by (rule countable_image[OF gi_basis_raw_stock_countable])

lemma gi_basis_equalizer_indices_countable:
  "countable (gi_basis_equalizer_indices B)"
  unfolding gi_basis_equalizer_indices_def
  by (rule countable_image; simp add: gi_basis_raw_stock_countable)

lemma gi_basis_generic_indices_countable:
  "countable (gi_basis_generic_indices B)"
  by (simp add: gi_basis_generic_indices_def gi_basis_classifier_indices_countable gi_basis_equalizer_indices_countable)

theorem gi_basis_raw_seed_exists:
  "\<exists>r. \<forall>S\<in>gi_basis_generic_indices B. \<forall>i. pp_guarded_unary_QLN_at_world i r S"
  by (rule pp_countable_stock_has_all_worlds_guarded_QLN_witness[OF gi_basis_generic_indices_countable])

theorem gi_basis_raw_seed_spec:
  "\<forall>S\<in>gi_basis_generic_indices B. \<forall>i. pp_guarded_unary_QLN_at_world i (gi_basis_raw_seed B) S"
  unfolding gi_basis_raw_seed_def by (rule someI_ex[OF gi_basis_raw_seed_exists])

lemma gi_basis_raw_seed_index_condition:
  assumes member: "S \<in> gi_basis_generic_indices B"
  shows "pp_orbit (gi_basis_raw_seed B) \<subseteq> S \<longleftrightarrow> S = UNIV"
proof -
  have at_root: "pp_guarded_unary_QLN_at_world [] (gi_basis_raw_seed B) S"
    using gi_basis_raw_seed_spec member by blast
  show ?thesis using at_root
    by (simp only: pp_guarded_unary_QLN_at_world_iff pp_root_unary_QLN_iff)
qed

lemma gi_basis_raw_seed_classifier_QLN:
  assumes member: "F \<in> gi_basis_raw_stock B"
  shows "pp_root_unary_QLN (pp_operator_index F) (gi_basis_raw_seed B)"
proof -
  have index: "pp_operator_index F \<in> gi_basis_generic_indices B"
    using member unfolding gi_basis_generic_indices_def gi_basis_classifier_indices_def by blast
  show ?thesis using gi_basis_raw_seed_index_condition[OF index]
    by (simp only: pp_root_unary_QLN_iff)
qed

theorem gi_basis_raw_seed_separates:
  assumes fs: "F \<in> gi_basis_raw_stock B" and hs: "H \<in> gi_basis_raw_stock B"
    and agreement: "F (gi_basis_raw_seed B) = H (gi_basis_raw_seed B)"
  shows "F = H"
proof (rule ccontr)
  assume distinct: "F \<noteq> H"
  let ?S = "pp_e_operator_equalizer F H"
  have fe: "pp_equivariant_operator F" by (rule gi_basis_raw_stock_equivariant[OF fs])
  have he: "pp_equivariant_operator H" by (rule gi_basis_raw_stock_equivariant[OF hs])
  have proper: "?S \<noteq> UNIV" by (rule pp_e_distinct_equivariant_equalizer_proper[OF fe he distinct])
  have index: "?S \<in> gi_basis_generic_indices B"
    using fs hs unfolding gi_basis_generic_indices_def gi_basis_equalizer_indices_def
    by (auto intro: image_eqI[where x="(F,H)"])
  have contained: "pp_orbit (gi_basis_raw_seed B) \<subseteq> ?S"
  proof
    fix p assume "p \<in> pp_orbit (gi_basis_raw_seed B)"
    then obtain i where p: "p = pp_view i (gi_basis_raw_seed B)" unfolding pp_orbit_def by blast
    have fv: "pp_view i (F (gi_basis_raw_seed B)) = F (pp_view i (gi_basis_raw_seed B))"
      using fe unfolding pp_equivariant_operator_def by blast
    have hv: "pp_view i (H (gi_basis_raw_seed B)) = H (pp_view i (gi_basis_raw_seed B))"
      using he unfolding pp_equivariant_operator_def by blast
    have outputs: "F p = H p" using fv hv agreement p by metis
    show "p \<in> ?S" using outputs by (simp add: pp_e_operator_equalizer_def)
  qed
  have "?S = UNIV" using contained gi_basis_raw_seed_index_condition[OF index] by blast
  then show False using proper by contradiction
qed

theorem gi_basis_raw_seed_fun_prime:
  "pp_stock_fun_prime (gi_basis_raw_stock B) (gi_basis_raw_seed B)"
  unfolding pp_stock_fun_prime_def
  by (intro ballI impI; rule gi_basis_raw_seed_separates; assumption)

corollary gi_basis_raw_seed_fun_prime_native_predicate:
  "gi_stock_fun_prime (gi_basis_raw_stock B) (gi_basis_raw_seed B)"
  using gi_basis_raw_seed_fun_prime unfolding gi_stock_fun_prime_def pp_stock_fun_prime_def .

section \<open>The typed moving seed and exact internal constants\<close>

lemma gi_basis_root_seed_member:
  "Elem (gi_basis_root_seed B) (pp_e_domain Prop)"
  unfolding gi_basis_root_seed_def using pp_n_bacon_embed_in_domain by simp

lemma gi_basis_root_seed_extract:
  "pp_n_bacon_extract (gi_basis_root_seed B) = gi_basis_raw_seed B"
  by (simp add: gi_basis_root_seed_def)

lemma gi_basis_seed_at_member:
  "Elem (gi_basis_seed_at B w) (pp_e_domain Prop)"
  unfolding gi_basis_seed_at_def
  by (rule pp_b_structure_lift_closed[OF pp_b_mset_structure_all gi_basis_root_seed_member])

lemma gi_basis_seed_at_action:
  "pp_b_action Prop (rev w) (gi_basis_seed_at B w) = gi_basis_root_seed B"
  unfolding gi_basis_seed_at_def
  by (rule pp_b_structure_action_lift[OF pp_b_mset_structure_all gi_basis_root_seed_member])

theorem gi_basis_fundamental_admissible:
  "pp_e_predicate_admissible \<sigma> (gi_basis_fundamental_at B \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis by (simp add: pp_e_predicate_admissible_def)
next
  case Prop
  show ?thesis unfolding Prop pp_e_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume xm: "Elem x (pp_e_domain Prop)" and ym: "Elem y (pp_e_domain Prop)"
      and xy: "pp_e_eqv Prop w x y" and future: "prefix w v"
    have later: "pp_e_eqv Prop v x y" by (rule pp_e_eqv_persistent[OF xy future])
    have seed: "pp_e_eqv Prop v (gi_basis_seed_at B v) (gi_basis_seed_at B v)"
      by (rule pp_e_eqv_reflexive[OF gi_basis_seed_at_member])
    show "gi_basis_fundamental_at B Prop v x = gi_basis_fundamental_at B Prop v y"
      using pp_e_eqv_congruence[OF xm ym gi_basis_seed_at_member gi_basis_seed_at_member later seed] by simp
  qed
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis by (simp add: pp_e_predicate_admissible_def)
qed

theorem gi_basis_internal_constants_typed:
  "Elem (gi_basis_internal_constants B c \<sigma>) (pp_e_domain \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis using pp_e_default_in_domain[of Ind] by simp
next
  case Prop
  then show ?thesis using pp_e_default_in_domain[of Prop] by simp
next
  case (Arr \<sigma> \<tau>)
  have pure: "Elem (pp_e_classifier \<sigma> (gi_basis_pure B \<sigma>)) (pp_e_domain (Arr \<sigma> Prop))"
    by (rule gi_basis_pure_classifier_member)
  have fundamental: "Elem (pp_e_classifier \<sigma> (gi_basis_fundamental_at B \<sigma>)) (pp_e_domain (Arr \<sigma> Prop))"
    by (rule pp_e_classifier_in_domain[OF gi_basis_fundamental_admissible])
  have default: "Elem (pp_e_default (Arr \<sigma> \<tau>)) (pp_e_domain (Arr \<sigma> \<tau>))"
    by (rule pp_e_default_in_domain)
  show ?thesis using Arr pure fundamental default by auto
qed

theorem gi_basis_internal_constants_locale:
  "pp_e_constants (gi_basis_internal_constants B)"
  by standard (rule gi_basis_internal_constants_typed)

interpretation BasisExactBaconConstants: pp_e_constants "gi_basis_internal_constants B"
  by (rule gi_basis_internal_constants_locale)

lemma gi_basis_eval_Pure:
  "pp_e_eval (gi_basis_internal_constants B) \<rho> (pp_Pure \<sigma>) = pp_e_classifier \<sigma> (gi_basis_pure B \<sigma>)"
  by (simp add: pp_Pure_def pp_pure_name_def)

lemma gi_basis_eval_Fun:
  "pp_e_eval (gi_basis_internal_constants B) \<rho> (pp_Fun \<sigma>) = pp_e_classifier \<sigma> (gi_basis_fundamental_at B \<sigma>)"
  by (simp add: pp_Fun_def pp_fun_name_def pp_pure_name_def)

theorem gi_basis_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>" and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> (pp_pure \<sigma> M)) w
    \<longleftrightarrow> gi_basis_pure B \<sigma> w (pp_e_eval (gi_basis_internal_constants B) \<rho> M)"
proof -
  have member: "Elem (pp_e_eval (gi_basis_internal_constants B) \<rho> M) (pp_e_domain \<sigma>)"
    using BasisExactBaconConstants.pp_e_eval_type[OF typed env] by (simp only: pp_e_dom_def)
  show ?thesis by (simp only: pp_pure_def pp_e_eval.simps(3) gi_basis_eval_Pure pp_e_classifier_holds[OF member])
qed

theorem gi_basis_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>" and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> (pp_fun \<sigma> M)) w
    \<longleftrightarrow> gi_basis_fundamental_at B \<sigma> w (pp_e_eval (gi_basis_internal_constants B) \<rho> M)"
proof -
  have member: "Elem (pp_e_eval (gi_basis_internal_constants B) \<rho> M) (pp_e_domain \<sigma>)"
    using BasisExactBaconConstants.pp_e_eval_type[OF typed env] by (simp only: pp_e_dom_def)
  show ?thesis by (simp only: pp_fun_def pp_e_eval.simps(3) gi_basis_eval_Fun pp_e_classifier_holds[OF member])
qed

end

text \<open>
  Equalizer requirements were included explicitly alongside the classifier
  indices. Thus the chosen root seed separates the full raw basis stock;
  no assumed diagonal or unspecified witness is used. These theorems
  supply the typed interpretation and its Pure/Fun evaluation clauses.
  Global QLN/background validity remains an additional proof obligation,
  and PP still requires a separate self-classification condition.
\<close>

end
