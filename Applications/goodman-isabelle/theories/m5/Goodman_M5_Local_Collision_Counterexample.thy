theory Goodman_M5_Local_Collision_Counterexample
  imports Goodman_Integration_Exact_M.Goodman_Exact_M6_Repair
    Goodman_Integration_M5_Object.Goodman_M5_Object_Transfer
    Goodman_Integration_Exact_QLN.Goodman_Exact_QLN_Model
    Goodman_Integration_Exact_L2.Goodman_Exact_Fun_Prime_Root
begin

section \<open>A local counterexample is different from a global fun′ axiom\<close>

text \<open>
  The historical collision proof adds fun′(r) as an AXIOM and applies
  theorem-level Equivalence above that axiom. We test the stronger claim
  obtained by silently discharging it to a local implication. The actual
  historical pp_M5_collision_operator and gi_M5_collision_result are used.

  Put A = {w : length(w) is even} and P = lift_[0](r) ∪ lift_[1](A),
  where r is fun′ for the complete exact logical stock. Its [0]-view is r,
  so P is fun′. Its [1]-view is everywhere contingent. Consequently NC(P)
  is permanently false on that cone; there F(NC(P)) is false while F(⊤)
  is true. This refutes the local collision implication in the no-PP model,
  not the preserved theorem with a stronger global axiom premise.
\<close>

definition gi_M5_raw_NC :: "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "gi_M5_raw_NC P = pp_sem_box P \<union> pp_sem_box (- P)"

definition gi_M5_raw_collision :: pp_e_operator where
  "gi_M5_raw_collision P = {i. (i \<in> P) = (i \<in> gi_M5_raw_NC P)}"

definition gi_M5_alternating :: pp_sem_prop where
  "gi_M5_alternating = {w. even (length w)}"

definition gi_M5_counter_input :: "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "gi_M5_counter_input r = pp_lift [0] r \<union> pp_lift [1] gi_M5_alternating"

lemma gi_M5_view_complement:
  "pp_view i (- P) = - pp_view i P"
  by (auto simp: pp_view_def)

lemma gi_M5_raw_NC_view:
  "pp_view i (gi_M5_raw_NC P) = gi_M5_raw_NC (pp_view i P)"
proof -
  have union: "pp_view i (X \<union> Y) = pp_view i X \<union> pp_view i Y" for X Y
    by (auto simp: pp_view_def)
  show ?thesis by (simp only: gi_M5_raw_NC_def union pp_sem_box_equivariant gi_M5_view_complement)
qed

lemma gi_M5_alternating_views_nonextreme:
  "pp_view i gi_M5_alternating \<noteq> {}" "pp_view i gi_M5_alternating \<noteq> UNIV"
proof -
  have different: "([] \<in> pp_view i gi_M5_alternating) \<noteq> ([0] \<in> pp_view i gi_M5_alternating)"
    by (simp add: pp_view_def gi_M5_alternating_def)
  show "pp_view i gi_M5_alternating \<noteq> {}" using different by blast
  show "pp_view i gi_M5_alternating \<noteq> UNIV" using different by blast
qed

lemma gi_M5_alternating_NC_empty:
  "gi_M5_raw_NC gi_M5_alternating = {}"
  using gi_M5_alternating_views_nonextreme
  by (auto simp: gi_M5_raw_NC_def pp_sem_box_def gi_M5_view_complement)

lemma gi_M5_counter_input_views:
  "pp_view [0] (gi_M5_counter_input r) = r"
  "pp_view [1] (gi_M5_counter_input r) = gi_M5_alternating"
  by (auto simp: gi_M5_counter_input_def pp_view_def pp_lift_def append_singleton_eq_iff)

theorem gi_M5_counter_input_fun_prime:
  "pp_e_exact_fun_prime r \<Longrightarrow> pp_e_exact_fun_prime (gi_M5_counter_input r)"
  by (rule gi_exact_M6_fun_prime_preimage[where i="[0]"]; simp only: gi_M5_counter_input_views; assumption)

lemma gi_M5_counter_NC_view_empty:
  "pp_view [1] (gi_M5_raw_NC (gi_M5_counter_input r)) = {}"
  by (simp only: gi_M5_raw_NC_view gi_M5_counter_input_views gi_M5_alternating_NC_empty)

lemma gi_M5_counter_collision_false_on_branch:
  "[1] \<notin> gi_M5_raw_collision (gi_M5_raw_NC (gi_M5_counter_input r))"
proof -
  let ?N = "gi_M5_raw_NC (gi_M5_counter_input r)"
  have not_N: "[1] \<notin> ?N"
    using gi_M5_counter_NC_view_empty[of r] pp_view_membership_at_root[of "[1]" ?N] by auto
  have view_neg: "pp_view [1] (- ?N) = UNIV"
    by (simp only: gi_M5_view_complement gi_M5_counter_NC_view_empty; simp)
  have NC_N: "[1] \<in> gi_M5_raw_NC ?N"
    using view_neg by (simp add: gi_M5_raw_NC_def pp_sem_box_def)
  show ?thesis using not_N NC_N by (simp add: gi_M5_raw_collision_def)
qed

lemma gi_M5_raw_collision_truth:
  "gi_M5_raw_collision UNIV = UNIV"
  by (auto simp: gi_M5_raw_collision_def gi_M5_raw_NC_def pp_sem_box_def pp_view_def)

theorem gi_M5_raw_collision_counterexample:
  "gi_M5_raw_collision (gi_M5_raw_NC (gi_M5_counter_input r)) \<noteq> gi_M5_raw_collision UNIV"
  using gi_M5_counter_collision_false_on_branch[of r] gi_M5_raw_collision_truth by blast

section \<open>Exact evaluation of the actual historical operator\<close>

lemma gi_M5_future_extract_iff:
  "(\<forall>v. prefix (rev i) v \<longrightarrow> pp_e_holds p v) \<longleftrightarrow>
    pp_view i (pp_n_bacon_extract p) = UNIV"
proof
  assume all: "\<forall>v. prefix (rev i) v \<longrightarrow> pp_e_holds p v"
  show "pp_view i (pp_n_bacon_extract p) = UNIV"
  proof (rule set_eqI)
    fix j
    have future: "prefix (rev i) (rev i @ rev j)" by (simp add: prefix_def)
    have "pp_e_holds p (rev i @ rev j)" using all future by blast
    then show "j \<in> pp_view i (pp_n_bacon_extract p) \<longleftrightarrow> j \<in> UNIV"
      by (simp add: pp_view_def pp_n_bacon_extract_def rev_append)
  qed
next
  assume view: "pp_view i (pp_n_bacon_extract p) = UNIV"
  show "\<forall>v. prefix (rev i) v \<longrightarrow> pp_e_holds p v"
  proof (intro allI impI)
    fix v assume "prefix (rev i) v"
    then obtain u where shape: "v = rev i @ u" by (auto simp: prefix_def)
    have "rev u \<in> pp_view i (pp_n_bacon_extract p)" using view by simp
    then show "pp_e_holds p v" by (simp add: shape pp_view_def pp_n_bacon_extract_def rev_append)
  qed
qed

lemma gi_M5_eval_box_raw:
  "pp_n_bacon_extract (pp_e_eval C \<rho> (ObjBox M)) = pp_sem_box (pp_n_bacon_extract (pp_e_eval C \<rho> M))"
proof (rule set_eqI)
  fix i
  have left: "i \<in> pp_n_bacon_extract (pp_e_eval C \<rho> (ObjBox M)) \<longleftrightarrow>
    (\<forall>v. prefix (rev i) v \<longrightarrow> pp_e_holds (pp_e_eval C \<rho> M) v)"
    by (simp add: pp_n_bacon_extract_def pp_e_eval_ObjBox_holds pp_e_prop_eqv_truth_iff)
  show "i \<in> pp_n_bacon_extract (pp_e_eval C \<rho> (ObjBox M)) \<longleftrightarrow>
    i \<in> pp_sem_box (pp_n_bacon_extract (pp_e_eval C \<rho> M))"
    using left gi_M5_future_extract_iff[where i=i and p="pp_e_eval C \<rho> M"]
    by (simp only: pp_sem_box_def mem_Collect_eq)
qed

lemma gi_M5_eval_neg_raw:
  "pp_n_bacon_extract (pp_e_eval C \<rho> (Neg M)) = - pp_n_bacon_extract (pp_e_eval C \<rho> M)"
  by (auto simp: pp_n_bacon_extract_def)

lemma gi_M5_eval_disj_raw:
  "pp_n_bacon_extract (pp_e_eval C \<rho> (Disj M N)) =
    pp_n_bacon_extract (pp_e_eval C \<rho> M) \<union> pp_n_bacon_extract (pp_e_eval C \<rho> N)"
  by (auto simp: pp_n_bacon_extract_def)

lemma gi_M5_eval_iff_raw:
  "pp_n_bacon_extract (pp_e_eval C \<rho> (M \<longleftrightarrow>\<^sub>o N)) =
    {i. (i \<in> pp_n_bacon_extract (pp_e_eval C \<rho> M)) = (i \<in> pp_n_bacon_extract (pp_e_eval C \<rho> N))}"
  by (auto simp: pp_n_bacon_extract_def)

lemma gi_M5_eval_NC_raw:
  "pp_n_bacon_extract (pp_e_eval C \<rho> (pp_noncontingent M)) =
    gi_M5_raw_NC (pp_n_bacon_extract (pp_e_eval C \<rho> M))"
  by (simp only: pp_noncontingent_def gi_M5_eval_disj_raw gi_M5_eval_box_raw gi_M5_eval_neg_raw gi_M5_raw_NC_def)

lemma gi_M5_eval_truth_raw:
  "pp_n_bacon_extract (pp_e_eval C \<rho> ObjTrue) = UNIV"
  by (auto simp: pp_n_bacon_extract_def pp_e_eval_ObjTrue)

lemma gi_M5_eval_collision_raw:
  assumes member: "Elem (pp_e_eval C \<rho> M) (pp_e_domain Prop)"
  shows "pp_n_bacon_extract (pp_e_eval C \<rho> (App pp_M5_collision_operator M)) =
    gi_M5_raw_collision (pp_n_bacon_extract (pp_e_eval C \<rho> M))"
  by (simp only: pp_M5_collision_operator_def pp_e_eval.simps(3,4) Lambda_app[OF member]
    gi_M5_eval_iff_raw gi_M5_eval_NC_raw pp_e_eval.simps(1) extend_env.simps gi_M5_raw_collision_def)

section \<open>The collision consequent is false for the typed counterexample input\<close>

lemma gi_M5_collision_result_typed:
  assumes rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile> gi_M5_collision_result r : Prop"
proof -
  have nt: "\<Gamma> \<turnstile> pp_noncontingent r : Prop" by (rule typed_pp_noncontingent[OF rt])
  have ft: "\<Gamma> \<turnstile> pp_M5_collision_operator : Arr Prop Prop"
    using typed_pp_M5_collision_operator[where \<Gamma>=\<Gamma>] by (simp only: pp_unary_ty_def)
  have left: "\<Gamma> \<turnstile> App pp_M5_collision_operator (pp_noncontingent r) : Prop"
    by (rule has_type.App[OF ft nt])
  have right: "\<Gamma> \<turnstile> App pp_M5_collision_operator ObjTrue : Prop"
    by (rule has_type.App[OF ft typed_ObjTrue])
  show ?thesis unfolding gi_M5_collision_result_def
    by (intro has_type.Conj has_type.Neg has_type.Eq nt typed_ObjTrue left right)
qed

theorem gi_M5_actual_collision_result_false_at_root:
  "\<not> pp_e_holds (pp_e_eval pp_e_generic_internal_constants
    (extend_env (pp_n_bacon_embed (gi_M5_counter_input r)) \<rho>) (gi_M5_collision_result (Var 0))) []"
proof -
  let ?P = "gi_M5_counter_input r"
  let ?env = "extend_env (pp_n_bacon_embed ?P) \<rho>"
  let ?L = "App pp_M5_collision_operator (pp_noncontingent (Var 0))"
  let ?T = "App pp_M5_collision_operator ObjTrue"
  have pm: "Elem (pp_n_bacon_embed ?P) (pp_e_domain Prop)" using pp_n_bacon_embed_in_domain[of ?P] by simp
  have env: "pp_e_env_typed [Prop] ?env" by (rule pp_e_env_typed_extend[OF pp_e_empty_env_typed pm])
  have vt: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have nt: "[Prop] \<turnstile> pp_noncontingent (Var 0) : Prop" by (rule typed_pp_noncontingent[OF vt])
  have ft: "[Prop] \<turnstile> pp_M5_collision_operator : Arr Prop Prop"
    using typed_pp_M5_collision_operator[where \<Gamma>="[Prop]"] by (simp only: pp_unary_ty_def)
  have lm: "Elem (pp_e_eval pp_e_generic_internal_constants ?env ?L) (pp_e_domain Prop)"
    using GenericExactBaconConstants.pp_e_eval_type[OF has_type.App[OF ft nt] env] by (simp only: pp_e_dom_def)
  have tm: "Elem (pp_e_eval pp_e_generic_internal_constants ?env ?T) (pp_e_domain Prop)"
    using GenericExactBaconConstants.pp_e_eval_type[OF has_type.App[OF ft typed_ObjTrue] env] by (simp only: pp_e_dom_def)
  have nm: "Elem (pp_e_eval pp_e_generic_internal_constants ?env (pp_noncontingent (Var 0))) (pp_e_domain Prop)"
    using GenericExactBaconConstants.pp_e_eval_type[OF nt env] by (simp only: pp_e_dom_def)
  have truth_member: "Elem (pp_e_eval pp_e_generic_internal_constants ?env ObjTrue) (pp_e_domain Prop)"
    using GenericExactBaconConstants.pp_e_eval_type[OF typed_ObjTrue env] by (simp only: pp_e_dom_def)
  have left_raw: "pp_n_bacon_extract (pp_e_eval pp_e_generic_internal_constants ?env ?L) =
    gi_M5_raw_collision (gi_M5_raw_NC ?P)"
    by (simp only: gi_M5_eval_collision_raw[OF nm] gi_M5_eval_NC_raw pp_e_eval.simps(1) extend_env.simps;
      simp)
  have right_raw: "pp_n_bacon_extract (pp_e_eval pp_e_generic_internal_constants ?env ?T) = gi_M5_raw_collision UNIV"
    by (simp only: gi_M5_eval_collision_raw[OF truth_member] gi_M5_eval_truth_raw)
  have unequal: "pp_e_eval pp_e_generic_internal_constants ?env ?L \<noteq> pp_e_eval pp_e_generic_internal_constants ?env ?T"
  proof
    assume equal: "pp_e_eval pp_e_generic_internal_constants ?env ?L = pp_e_eval pp_e_generic_internal_constants ?env ?T"
    have raw_equal: "gi_M5_raw_collision (gi_M5_raw_NC ?P) = gi_M5_raw_collision UNIV"
      using arg_cong[OF equal, where f=pp_n_bacon_extract] by (simp only: left_raw right_raw)
    show False by (rule notE[OF gi_M5_raw_collision_counterexample raw_equal])
  qed
  show ?thesis using unequal
    by (simp only: gi_M5_collision_result_def pp_e_eval_Conj_holds pp_e_eval_Eq_holds gi_exact_root_eqv[OF lm tm]; blast)
qed

theorem gi_M5_actual_local_collision_counterexample:
  assumes fp: "pp_e_exact_fun_prime r"
  shows "pp_e_holds (pp_e_eval pp_e_generic_internal_constants
      (extend_env (pp_n_bacon_embed (gi_M5_counter_input r)) \<rho>) (pp_fun_prime (Var 0))) [] \<and>
    \<not> pp_e_holds (pp_e_eval pp_e_generic_internal_constants
      (extend_env (pp_n_bacon_embed (gi_M5_counter_input r)) \<rho>) (gi_M5_collision_result (Var 0))) []"
proof -
  let ?P = "gi_M5_counter_input r"
  have pm: "Elem (pp_n_bacon_embed ?P) (pp_e_domain Prop)" using pp_n_bacon_embed_in_domain[of ?P] by simp
  have env: "pp_e_env_typed [Prop] (extend_env (pp_n_bacon_embed ?P) \<rho>)"
    by (rule pp_e_env_typed_extend[OF pp_e_empty_env_typed pm])
  have raw: "pp_e_exact_fun_prime ?P" by (rule gi_M5_counter_input_fun_prime[OF fp])
  have local_fp: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants
    (extend_env (pp_n_bacon_embed ?P) \<rho>) (pp_fun_prime (Var 0))) []"
    using gi_exact_fun_prime_root_iff[OF typed_var0 env] raw by simp
  show ?thesis by (rule conjI[OF local_fp gi_M5_actual_collision_result_false_at_root])
qed

definition gi_M5_local_collision_universal :: oterm where
  "gi_M5_local_collision_universal = Forall Prop (Imp (pp_fun_prime (Var 0)) (gi_M5_collision_result (Var 0)))"

lemma gi_M5_local_collision_universal_typed:
  "[] \<turnstile> gi_M5_local_collision_universal : Prop"
  unfolding gi_M5_local_collision_universal_def
  by (intro has_type.Forall has_type.Imp typed_pp_fun_prime gi_M5_collision_result_typed typed_var0)

theorem gi_M5_local_collision_universal_false_at_root:
  "\<not> pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> gi_M5_local_collision_universal) []"
proof -
  obtain r where fp: "pp_e_exact_fun_prime r" using pp_e_exact_fun_prime_exists by blast
  have pm: "Elem (pp_n_bacon_embed (gi_M5_counter_input r)) (pp_e_domain Prop)"
    using pp_n_bacon_embed_in_domain[of "gi_M5_counter_input r"] by simp
  show ?thesis using gi_M5_actual_local_collision_counterexample[OF fp, where \<rho>=\<rho>] pm
    by (simp only: gi_M5_local_collision_universal_def pp_e_eval_Forall_holds pp_e_eval_Imp_holds; blast)
qed

lemma gi_M5_local_collision_vocabulary:
  "consts_of gi_M5_local_collision_universal \<subseteq> {pp_pure_name, pp_fun_name}"
  by (simp add: gi_M5_local_collision_universal_def gi_M5_collision_result_def pp_M5_collision_operator_def
    pp_noncontingent_def pp_fun_prime_def pp_pure_def pp_Pure_def ObjBox_def ObjTrue_def
    shift_by_def consts_of_rename)

theorem gi_M5_native_local_collision_false_at_root:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap" and typed: "book_env_typed gi_exact_domain G g"
  shows "\<not> gi_exact_valuation [] (gi_exact_goodman_denote pp_e_generic_internal_constants G g
    (gi_to_book G [] cmap gi_M5_local_collision_universal))"
proof -
  have denotation: "gi_exact_goodman_denote pp_e_generic_internal_constants G g (gi_to_book G [] cmap gi_M5_local_collision_universal) =
    pp_e_eval pp_e_generic_internal_constants pp_e_closed_env gi_M5_local_collision_universal"
    by (rule pp_e_constants.gi_exact_goodman_closed_denotation_translation[OF gi_exact_generic_constants rich
      gi_M5_local_collision_universal_typed typed names gi_M5_local_collision_vocabulary])
  show ?thesis by (simp only: denotation gi_exact_valuation_def; rule gi_M5_local_collision_universal_false_at_root)
qed

theorem gi_M5_local_collision_not_derivable_from_no_PP_QLN:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap"
  shows "\<not> goodman_book_proves gb_signature G (gi_native_QLN_background G)
    (gi_to_book G [] cmap gi_M5_local_collision_universal)"
proof
  assume derivation: "goodman_book_proves gb_signature G (gi_native_QLN_background G)
    (gi_to_book G [] cmap gi_M5_local_collision_universal)"
  have global: "gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gi_to_book G [] cmap gi_M5_local_collision_universal)"
    by (rule pp_e_constants.gi_exact_goodman_extension_global_sound[OF gi_exact_generic_constants rich derivation];
      rule gi_exact_generic_QLN_background_gvalid[OF rich]; assumption)
  have root: "gi_exact_valuation [] (gi_exact_goodman_denote pp_e_generic_internal_constants G
    (gi_exact_default_assignment G) (gi_to_book G [] cmap gi_M5_local_collision_universal))"
    using global gi_exact_default_assignment_typed[where G=G]
    unfolding gi_exact_goodman_global_valid_iff by blast
  have not_root: "\<not> gi_exact_valuation [] (gi_exact_goodman_denote pp_e_generic_internal_constants G
    (gi_exact_default_assignment G) (gi_to_book G [] cmap gi_M5_local_collision_universal))"
    by (rule gi_M5_native_local_collision_false_at_root[OF rich names gi_exact_default_assignment_typed])
  show False by (rule notE[OF not_root root])
qed

corollary gi_M5_local_collision_not_derivable_from_T2_min:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap"
  shows "\<not> goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G [] cmap gi_M5_local_collision_universal)"
proof
  assume derivation: "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G [] cmap gi_M5_local_collision_universal)"
  have subset: "gb_T2_min_axioms G \<subseteq> gi_native_QLN_background G"
    unfolding gb_T2_min_axioms_def gi_native_QLN_background_def gb_recombination_background_def gb_background_axioms_def by blast
  have stronger: "goodman_book_proves gb_signature G (gi_native_QLN_background G)
    (gi_to_book G [] cmap gi_M5_local_collision_universal)"
    by (rule goodman_book_mono[OF derivation subset])
  show False by (rule notE[OF gi_M5_local_collision_not_derivable_from_no_PP_QLN[OF rich names] stronger])
qed

text \<open>
  The counterexample satisfies the LOCAL fun′ antecedent and falsifies the
  actual historical collision conjunction. Its value inequality is not a
  mere difference of current truth values: [1] explicitly distinguishes the
  two output propositions, hence their root identity is false.

  This model validates the original native no-PP QLN background globally.
  It refutes the universal local implication and its native derivability
  from that background, not the old axiom-extension theorem. No identification
  of the counterexample input with the model's fundamental proposition, no
  PP model, and no claim that the operator is injective follows. HOL–ZF scope
  is retained.
\<close>

end
