theory Goodman_Exact_Basis_QLN
  imports Goodman_Exact_Basis_Seed
    Goodman_Integration_Exact_QLN.Goodman_Exact_QLN_Transfer
begin

section \<open>QLN for a countable invariant basis in the unchanged exact carriers\<close>

text \<open>
  The basis assumptions supply typed invariant values, application closure,
  and every closed logical denotation. Its chosen generic seed already has
  the proved countable classifier-index property. We derive, rather than
  assume, zeroary and unary Recombination and Exhaustion for the resulting
  Pure/Fun interpretation. The raw guarded-QLN equivalence used below is
  the checked branch-gluing theorem; its Exhaustion direction includes
  surjectivity of taking a view on arbitrary input propositions.
\<close>

context gi_exact_invariant_basis
begin

lemma gi_basis_fundamental_raw:
  assumes pm: "Elem p (pp_e_domain Prop)" and fundamental: "gi_basis_fundamental_at B Prop w p"
  shows "pp_fundamental_at (rev w) (gi_basis_raw_seed B) (pp_n_bacon_extract p)"
proof -
  have related: "pp_e_eqv Prop w p (gi_basis_seed_at B w)" using fundamental by simp
  have action: "pp_b_action Prop (rev w) p = gi_basis_root_seed B"
    using related by (simp only: pp_e_eqv_iff_action_eq[OF pm gi_basis_seed_at_member] gi_basis_seed_at_action)
  have raw: "pp_view (rev w) (pp_n_bacon_extract p) = gi_basis_raw_seed B"
    using arg_cong[OF action, where f=pp_n_bacon_extract]
    by (simp add: pp_n_bacon_extract_action pp_prop_action_def gi_basis_root_seed_extract)
  show ?thesis by (simp only: pp_fundamental_at_def raw)
qed

lemma gi_basis_raw_universal_iff:
  assumes dm: "Elem D (pp_e_domain gb_unary)"
  shows "(\<forall>P. rev w \<in> pp_e_raw_operator D P) \<longleftrightarrow>
    (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow> pp_e_holds (D \<acute> p) w)"
proof
  assume raw: "\<forall>P. rev w \<in> pp_e_raw_operator D P"
  show "\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow> pp_e_holds (D \<acute> p) w"
    by (rule pp_e_closed_den_universal_from_raw[OF dm raw])
next
  assume exact: "\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow> pp_e_holds (D \<acute> p) w"
  show "\<forall>P. rev w \<in> pp_e_raw_operator D P"
  proof
    fix P
    have pm: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)" using pp_n_bacon_embed_in_domain[of P] by simp
    have truth: "pp_e_holds (D \<acute> pp_n_bacon_embed P) w" using exact pm by blast
    show "rev w \<in> pp_e_raw_operator D P"
      using pp_e_raw_operator_at_world_iff[OF dm pm, where w=w] truth by simp
  qed
qed

theorem gi_basis_value_unary_QLN:
  assumes db: "D \<in> B gb_unary" and rm: "Elem r (pp_e_domain Prop)"
    and fundamental: "gi_basis_fundamental_at B Prop w r"
  shows "(\<forall>v. prefix w v \<longrightarrow> pp_e_holds (D \<acute> r) v) \<longleftrightarrow>
    (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow> pp_e_holds (D \<acute> q) w)"
proof -
  let ?F = "pp_e_raw_operator D"
  let ?S = "pp_operator_index ?F"
  have dm: "Elem D (pp_e_domain gb_unary)" by (rule basis_member[OF db])
  have raw_member: "?F \<in> gi_basis_raw_stock B" using db unfolding gi_basis_raw_stock_def by blast
  have index: "?S \<in> gi_basis_generic_indices B"
    using raw_member unfolding gi_basis_generic_indices_def gi_basis_classifier_indices_def by blast
  have classifier: "?F = pp_classifier ?S" by (rule gi_basis_raw_stock_classifier[OF raw_member])
  have guarded: "pp_guarded_unary_QLN_at_world (rev w) (gi_basis_raw_seed B) ?S"
    using gi_basis_raw_seed_spec index by blast
  have raw_fundamental: "pp_fundamental_at (rev w) (gi_basis_raw_seed B) (pp_n_bacon_extract r)"
    by (rule gi_basis_fundamental_raw[OF rm fundamental])
  have raw_QLN: "(rev w \<in> pp_sem_box (pp_classifier ?S (pp_n_bacon_extract r))) \<longleftrightarrow>
    (\<forall>Q. rev w \<in> pp_classifier ?S Q)"
    using guarded raw_fundamental unfolding pp_guarded_unary_QLN_at_world_def by blast
  have raw_QLN': "(rev w \<in> pp_sem_box (?F (pp_n_bacon_extract r))) \<longleftrightarrow>
    (\<forall>Q. rev w \<in> ?F Q)"
    using raw_QLN classifier by metis
  show ?thesis using raw_QLN'
    by (simp only: pp_e_raw_box_at_world_iff[OF dm rm] gi_basis_raw_universal_iff[OF dm])
qed

lemma gi_basis_pure_unary_representative:
  assumes pure: "gi_basis_pure B gb_unary w X"
  obtains D where "D \<in> B gb_unary" "pp_e_eqv gb_unary w X D"
  using pure unfolding gi_basis_pure_def by blast

lemma gi_basis_related_applications:
  assumes related: "pp_e_eqv gb_unary w X D" and qm: "Elem q (pp_e_domain Prop)"
    and future: "prefix w v"
  shows "pp_e_holds (X \<acute> q) v \<longleftrightarrow> pp_e_holds (D \<acute> q) v"
proof -
  have later: "pp_e_eqv gb_unary v X D" by (rule pp_e_eqv_persistent[OF related future])
  have refl: "pp_e_eqv Prop v q q" by (rule pp_e_eqv_reflexive[OF qm])
  have apps: "pp_e_eqv Prop v (X \<acute> q) (D \<acute> q)" by (rule pp_e_app_respects[OF later qm qm refl])
  show ?thesis using pp_e_prop_eqv_at[OF apps, of v] by simp
qed

theorem gi_basis_pure_unary_QLN:
  assumes pure: "gi_basis_pure B gb_unary w X" and rm: "Elem r (pp_e_domain Prop)"
    and fundamental: "gi_basis_fundamental_at B Prop w r"
  shows "(\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> r) v) \<longleftrightarrow>
    (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow> pp_e_holds (X \<acute> q) w)"
proof -
  obtain D where db: "D \<in> B gb_unary" and related: "pp_e_eqv gb_unary w X D"
    by (rule gi_basis_pure_unary_representative[OF pure])
  have necessity: "(\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> r) v) \<longleftrightarrow>
    (\<forall>v. prefix w v \<longrightarrow> pp_e_holds (D \<acute> r) v)"
    using gi_basis_related_applications[OF related rm] by blast
  have universal: "(\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow> pp_e_holds (X \<acute> q) w) \<longleftrightarrow>
    (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow> pp_e_holds (D \<acute> q) w)"
  proof -
    have current: "pp_e_holds (X \<acute> q) w \<longleftrightarrow> pp_e_holds (D \<acute> q) w"
      if qm: "Elem q (pp_e_domain Prop)" for q
      by (rule gi_basis_related_applications[OF related qm]; simp)
    show ?thesis using current by blast
  qed
  show ?thesis using necessity universal gi_basis_value_unary_QLN[OF db rm fundamental] by blast
qed

section \<open>Invariant proposition values supply zeroary Exhaustion\<close>

lemma gi_basis_proposition_world_constant:
  assumes member: "a \<in> B Prop"
  shows "pp_e_holds a v = pp_e_holds a []"
proof -
  have invariant: "pp_b_action Prop (rev v) a = a" by (rule basis_invariant[OF member])
  have truth: "pp_e_holds (pp_b_action Prop (rev v) a) [] = pp_e_holds a v" by simp
  show ?thesis using invariant truth by simp
qed

theorem gi_basis_pure_prop_true_imp_box:
  assumes pure: "gi_basis_pure B Prop w p" and truth: "pp_e_holds p w"
  shows "pp_e_eqv Prop w p (pp_zf_truth True)"
proof -
  obtain a where member: "a \<in> B Prop" and related: "pp_e_eqv Prop w p a"
    using pure unfolding gi_basis_pure_def by blast
  have a_true_w: "pp_e_holds a w" using pp_e_prop_eqv_at[OF related, of w] truth by simp
  have a_true_root: "pp_e_holds a []" using a_true_w gi_basis_proposition_world_constant[OF member, of w] by simp
  show ?thesis
  proof (simp only: pp_e_eqv.simps, intro allI impI)
    fix v assume future: "prefix w v"
    have later: "pp_e_eqv Prop v p a" by (rule pp_e_eqv_persistent[OF related future])
    have a_true: "pp_e_holds a v" using a_true_root gi_basis_proposition_world_constant[OF member, of v] by simp
    show "pp_e_holds p v \<longleftrightarrow> pp_e_holds (pp_zf_truth True) v"
      using pp_e_prop_eqv_at[OF later, of v] a_true by simp
  qed
qed

section \<open>The four actual source formulas at every world\<close>

lemma gi_basis_unary_recombination_holds_iff:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> pp_unary_recombination) w \<longleftrightarrow>
    (\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      (\<forall>r. Elem r (pp_e_domain Prop) \<longrightarrow>
        (gi_basis_pure B gb_unary w X \<and> gi_basis_fundamental_at B Prop w r) \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> r) v) \<longrightarrow>
          (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow> pp_e_holds (X \<acute> q) w))))"
  by (simp add: pp_unary_recombination_def pp_pure_def pp_fun_def gi_basis_eval_Pure gi_basis_eval_Fun
    pp_e_classifier_holds pp_e_prop_eqv_truth_iff pp_e_eval_ObjBox_holds
    extend_env.simps pp_e_three_extensions_index_two)

theorem gi_basis_unary_recombination_holds:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> pp_unary_recombination) w"
  unfolding gi_basis_unary_recombination_holds_iff using gi_basis_pure_unary_QLN by blast

lemma gi_basis_unary_exhaustion_holds_iff:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> pp_unary_exhaustion) w \<longleftrightarrow>
    (\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      (\<forall>r. Elem r (pp_e_domain Prop) \<longrightarrow>
        (gi_basis_pure B gb_unary w X \<and> gi_basis_fundamental_at B Prop w r) \<longrightarrow>
        ((\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow> pp_e_holds (X \<acute> q) w) \<longrightarrow>
          (\<forall>v. prefix w v \<longrightarrow> pp_e_holds (X \<acute> r) v))))"
  by (simp add: pp_unary_exhaustion_def pp_pure_def pp_fun_def gi_basis_eval_Pure gi_basis_eval_Fun
    pp_e_classifier_holds pp_e_prop_eqv_truth_iff pp_e_eval_ObjBox_holds
    extend_env.simps pp_e_three_extensions_index_two)

theorem gi_basis_unary_exhaustion_holds:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> pp_unary_exhaustion) w"
  unfolding gi_basis_unary_exhaustion_holds_iff using gi_basis_pure_unary_QLN by blast

theorem gi_basis_zeroary_recombination_holds:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> pp_zeroary_recombination) w"
  by (simp add: pp_zeroary_recombination_def pp_e_eval_ObjBox_holds pp_e_prop_eqv_truth_iff)

lemma gi_basis_zeroary_exhaustion_holds_iff:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> pp_zeroary_exhaustion) w \<longleftrightarrow>
    (\<forall>p. Elem p (pp_e_domain Prop) \<longrightarrow> gi_basis_pure B Prop w p \<longrightarrow>
      pp_e_holds p w \<longrightarrow> pp_e_eqv Prop w p (pp_zf_truth True))"
  by (simp add: pp_zeroary_exhaustion_def pp_pure_def gi_basis_eval_Pure
    pp_e_classifier_holds pp_e_eval_ObjBox_holds)

theorem gi_basis_zeroary_exhaustion_holds:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> pp_zeroary_exhaustion) w"
  unfolding gi_basis_zeroary_exhaustion_holds_iff using gi_basis_pure_prop_true_imp_box by blast

section \<open>The independently written native QLN formulas are globally valid\<close>

theorem gi_basis_native_zeroary_recombination_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G (gb_zeroary_recombination G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis
    by (rule pp_e_constants.gi_exact_goodman_closed_equivalence_transfer[
      OF gi_basis_internal_constants_locale rich typed_pp_zeroary_recombination names
        gi_exact_zeroary_recombination_vocabulary gi_exact_zeroary_recombination_admitted[OF names]
        gb_zeroary_recombination_language[OF rich] gi_zeroary_recombination_equivalence[OF rich names]
        gi_basis_zeroary_recombination_holds])
qed

theorem gi_basis_native_unary_recombination_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G (gb_unary_recombination G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis
    by (rule pp_e_constants.gi_exact_goodman_closed_equivalence_transfer[
      OF gi_basis_internal_constants_locale rich typed_pp_unary_recombination names
        gi_exact_unary_recombination_vocabulary gi_exact_unary_recombination_admitted[OF names]
        gb_unary_recombination_language[OF rich] gi_unary_recombination_equivalence[OF rich names]
        gi_basis_unary_recombination_holds])
qed

theorem gi_basis_native_zeroary_exhaustion_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G (gb_zeroary_exhaustion G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis
    by (rule pp_e_constants.gi_exact_goodman_closed_equivalence_transfer[
      OF gi_basis_internal_constants_locale rich typed_pp_zeroary_exhaustion names
        gi_exact_zeroary_exhaustion_vocabulary gi_exact_zeroary_exhaustion_admitted[OF names]
        gb_zeroary_exhaustion_language[OF rich] gi_zeroary_exhaustion_equivalence[OF rich names]
        gi_basis_zeroary_exhaustion_holds])
qed

theorem gi_basis_native_unary_exhaustion_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G (gb_unary_exhaustion G)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  show ?thesis
    by (rule pp_e_constants.gi_exact_goodman_closed_equivalence_transfer[
      OF gi_basis_internal_constants_locale rich typed_pp_unary_exhaustion names
        gi_exact_unary_exhaustion_vocabulary gi_exact_unary_exhaustion_admitted[OF names]
        gb_unary_exhaustion_language[OF rich] gi_unary_exhaustion_equivalence[OF rich names]
        gi_basis_unary_exhaustion_holds])
qed

text \<open>
  All four native conclusions quantify over every world and every typed
  named assignment. The Pure predicate is the local-identity saturation of
  the actual basis, which already contains every native closed logical
  denotation by the checked decoder theorem. The carrier is unchanged.
  This file proves only the zeroary/unary QLN directions; assembling all
  background schemas and proving the separately required PP membership
  condition are not consequences of these four formulas alone.
\<close>

end

end
