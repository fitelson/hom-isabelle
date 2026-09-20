theory Bacon_PP_Fun_Prime_Control
  imports 
    "Goodman_Legacy_05.Bacon_PP_Goodman_T6_TU"
    "Goodman_Legacy_04.Bacon_PP_Goodman_Fun_Prime_Axiom_Collapse"
begin

section \<open>The fun-prime classifier and a controlled Boolean operator\<close>

lemma CEV_control_PC:
  assumes "\<Gamma> \<turnstile> A : Prop" "\<forall>v. prop_eval v A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  apply (rule CEV_collapse_taut_plus)
  using assms unfolding prop_tautology_def by blast

lemma CEV_control_box_mono:
  assumes a: "\<Gamma> \<turnstile> A : Prop" and b: "\<Gamma> \<turnstile> B : Prop"
    and ab: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o A) (\<box>\<^sub>o B)"
  using CEV_axiom_necessitation[OF ab]
    CEV_axiom_proves.Base[OF CEV_modal_K[OF a b]]
  unfolding modal_K_def by (rule CEV_axiom_proves.MP)

lemma CEV_fun_prime_possible_box:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime p) (\<diamond>\<^sub>o (\<box>\<^sub>o p))"
proof -
  have ft: "\<Gamma> \<turnstile> pp_fun_prime p : Prop" using p by (rule typed_pp_fun_prime)
  have pt: "\<Gamma> \<turnstile> pp_pure Prop ObjTrue : Prop"
    by (intro typed_pp_pure typed_ObjTrue)
  have dt: "\<Gamma> \<turnstile> \<diamond>\<^sub>o (\<box>\<^sub>o p) : Prop"
    using p by (intro typed_ObjDiamond typed_ObjBox)
  have attain: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_fun_prime p) (Imp (pp_pure Prop ObjTrue) (\<diamond>\<^sub>o (\<box>\<^sub>o p)))"
    using CEV_Goodman_T2c_parameter[
      OF pp_T2_min_axioms_into_T6_extension[OF core] p typed_ObjTrue]
    by (simp only: ObjBox_def)
  have pure: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure Prop ObjTrue"
    using core by (rule pp_ObjTrue_pure_in_core_extension)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp (pp_fun_prime p) (Imp (pp_pure Prop ObjTrue) (\<diamond>\<^sub>o (\<box>\<^sub>o p))))
        (Imp (pp_pure Prop ObjTrue) (Imp (pp_fun_prime p) (\<diamond>\<^sub>o (\<box>\<^sub>o p))))"
    by (rule CEV_control_PC)
      (intro has_type.Imp ft pt dt, simp only: prop_eval.simps, blast)
  show ?thesis using pure CEV_axiom_proves.MP[OF attain taut]
    by (rule CEV_axiom_proves.MP)
qed

theorem CEV_fun_prime_never_necessary:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (\<box>\<^sub>o (pp_fun_prime p))"
proof -
  let ?F = "pp_fun_prime p"
  have ft: "\<Gamma> \<turnstile> ?F : Prop" using p by (rule typed_pp_fun_prime)
  have bpt: "\<Gamma> \<turnstile> \<box>\<^sub>o p : Prop" using p by (rule typed_ObjBox)
  have nbpt: "\<Gamma> \<turnstile> Neg (\<box>\<^sub>o p) : Prop"
    using bpt by (rule has_type.Neg)
  have nonnecessary: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?F (Neg (\<box>\<^sub>o p))"
    using CEV_fun_prime_neq_ObjTrue[OF pp_T2_min_axioms_into_T6_extension[OF core] p]
    by (simp only: ObjBox_def)
  have boxed: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o ?F) (\<box>\<^sub>o (Neg (\<box>\<^sub>o p)))"
    by (rule CEV_control_box_mono[OF ft nbpt nonnecessary])
  have t: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o ?F) ?F"
    using CEV_axiom_proves.Base[OF CEV_modal_T[OF ft]]
    by (simp only: modal_T_def)
  have possible: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?F (\<diamond>\<^sub>o (\<box>\<^sub>o p))"
    by (rule CEV_fun_prime_possible_box[OF core p])
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Imp (\<box>\<^sub>o ?F) (\<box>\<^sub>o (Neg (\<box>\<^sub>o p))))
      (Imp (Imp (\<box>\<^sub>o ?F) ?F)
        (Imp (Imp ?F (\<diamond>\<^sub>o (\<box>\<^sub>o p))) (Neg (\<box>\<^sub>o ?F))))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Neg typed_ObjBox typed_ObjDiamond ft p,
       simp only: ObjDiamond_def prop_eval.simps, blast)
  show ?thesis
    using CEV_axiom_proves.MP[OF possible
      CEV_axiom_proves.MP[OF t CEV_axiom_proves.MP[OF boxed taut]]] .
qed

theorem CEV_fun_prime_iteration_false:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (pp_fun_prime (pp_fun_prime p))"
proof -
  let ?F = "pp_fun_prime p"
  let ?FF = "pp_fun_prime ?F"
  have ft: "\<Gamma> \<turnstile> ?F : Prop" using p by (rule typed_pp_fun_prime)
  have fft: "\<Gamma> \<turnstile> ?FF : Prop" using ft by (rule typed_pp_fun_prime)
  have never: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (Neg (\<box>\<^sub>o ?F))"
    using CEV_fun_prime_never_necessary[OF core p] by (rule CEV_axiom_necessitation)
  have possible: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?FF (\<diamond>\<^sub>o (\<box>\<^sub>o ?F))"
    by (rule CEV_fun_prime_possible_box[OF core ft])
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (\<box>\<^sub>o (Neg (\<box>\<^sub>o ?F)))
      (Imp (Imp ?FF (\<diamond>\<^sub>o (\<box>\<^sub>o ?F))) (Neg ?FF))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Neg typed_ObjBox typed_ObjDiamond ft fft,
       simp only: ObjDiamond_def prop_eval.simps, blast)
  show ?thesis using possible CEV_axiom_proves.MP[OF never taut]
    by (rule CEV_axiom_proves.MP)
qed

theorem CEV_fun_prime_iteration_eq_falsity:
  assumes "pp_T6_core_PP_axioms \<subseteq> T" "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (pp_fun_prime (pp_fun_prime p)) ObjFalse"
  using typed_pp_fun_prime[OF typed_pp_fun_prime[OF assms(2)]]
    CEV_fun_prime_iteration_false[OF assms]
  by (rule CEV_refuted_imp_eq_ObjFalse)

subsection \<open>Conversion and theorem-level identity helpers\<close>

lemma CEV_control_eq_imp:
  assumes a: "\<Gamma> \<turnstile> A : Prop" and b: "\<Gamma> \<turnstile> B : Prop"
    and eq: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
proof -
  have local_a: "\<Gamma> ; T ; {A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    using a by (intro CEV_axiom_from.Assumption) simp
  have local_eq: "\<Gamma> ; T ; {A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop A B"
    using eq by (rule CEV_axiom_from.Theorem)
  have local_b: "\<Gamma> ; T ; {A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
    using a b local_a local_eq by (rule CEV_axiom_from_eq_prop_elim)
  show ?thesis using a local_b by (rule CEV_axiom_from_singleton_imp)
qed

lemma CEV_control_eq_sym:
  assumes "\<Gamma> \<turnstile> A : \<sigma>" "\<Gamma> \<turnstile> B : \<sigma>"
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> B A"
  using CEV_axiom_from_eq_sym[OF assms(1,2)
      CEV_axiom_from.Theorem[OF assms(3)], where S = "{}"]
  by (simp add: CEV_axiom_from_empty_iff)

lemma CEV_control_eq_iff:
  assumes "\<Gamma> \<turnstile> A : Prop" "\<Gamma> \<turnstile> B : Prop"
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o B)"
  using CEV_control_eq_imp[OF assms]
    CEV_control_eq_imp[OF assms(2,1) CEV_control_eq_sym[OF assms]]
  by (rule CEV_axiom_conj_intro)

lemma CEV_control_unary_equivalence:
  assumes f: "\<Gamma> \<turnstile> F : pp_unary_ty" and g: "\<Gamma> \<turnstile> G : pp_unary_ty"
    and pointwise: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (shift F) (Var 0) \<longleftrightarrow>\<^sub>o App (shift G) (Var 0))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq pp_unary_ty F G"
proof -
  have ft: "\<Gamma> \<turnstile> F : arrow_type [Prop] Prop"
    using f by (simp add: pp_unary_ty_def)
  have gt: "\<Gamma> \<turnstile> G : arrow_type [Prop] Prop"
    using g by (simp add: pp_unary_ty_def)
  have zeta: "[Prop] @ \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ zeta_body [Prop] F G"
    using pointwise by (simp add: zeta_body_def fresh_vars_def shift_by_1)
  show ?thesis using CEV_axiom_proves.VectorEquivalence[OF ft gt zeta]
    by (simp add: pp_unary_ty_def)
qed

lemma shift_fun_prime_classifier[simp]:
  "shift pp_fun_prime_classifier = pp_fun_prime_classifier"
  by (simp add: pp_fun_prime_classifier_def pp_fun_prime_def pp_pure_def
    pp_Pure_def shift_def shift_by_def shift_ren_def)

definition pp_fun_prime_purity_builder :: oterm where
  "pp_fun_prime_purity_builder =
    Lam pp_unary_classifier_ty
      (Lam Prop (Forall pp_unary_ty (Forall pp_unary_ty
        (Imp (Conj (App (Var 3) (Var 1)) (App (Var 3) (Var 0)))
          (Imp (Eq Prop (App (Var 1) (Var 2)) (App (Var 0) (Var 2)))
            (Eq pp_unary_ty (Var 1) (Var 0)))))))"

lemma typed_fun_prime_purity_builder:
  "\<Gamma> \<turnstile> pp_fun_prime_purity_builder : pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_fun_prime_purity_builder_def pp_unary_classifier_ty_def
      pp_unary_ty_def lookup_def)

lemma fun_prime_builder_beta:
  "beta_contract (App pp_fun_prime_purity_builder (pp_Pure pp_unary_ty)) pp_fun_prime_classifier"
  using beta_contract.beta[where \<sigma> = pp_unary_classifier_ty
    and M = "Lam Prop (Forall pp_unary_ty (Forall pp_unary_ty
      (Imp (Conj (App (Var 3) (Var 1)) (App (Var 3) (Var 0)))
        (Imp (Eq Prop (App (Var 1) (Var 2)) (App (Var 0) (Var 2)))
          (Eq pp_unary_ty (Var 1) (Var 0))))))"
    and N = "pp_Pure pp_unary_ty"]
  by (simp add: pp_fun_prime_purity_builder_def pp_fun_prime_classifier_def
    pp_fun_prime_def pp_pure_def pp_Pure_def subst0_def shift_by_def shift_ren_def
    shift_def eval_nat_numeral)

lemma CEV_control_pure_logical:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and closed: "[] \<turnstile> M : \<sigma>" and logical: "consts_of M = {}"
    and typed: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure \<sigma> M"
proof -
  have "pp_pure \<sigma> M \<in> pp_T6_core_PP_axioms"
    using closed logical unfolding pp_T6_core_PP_axioms_def
      pp_purity_schema_def pp_logical_vocabulary_def by blast
  then have mem: "pp_pure \<sigma> M \<in> T" using core by blast
  show ?thesis using mem typed_pp_pure[OF typed] by (rule CEV_axiom_proves.Axiom)
qed

theorem CEV_fun_prime_classifier_pure:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty pp_fun_prime_classifier"
proof -
  let ?B = pp_fun_prime_purity_builder
  let ?C = "pp_Pure pp_unary_ty"
  let ?I = "App ?B ?C"
  have ct: "\<Gamma> \<turnstile> ?C : pp_unary_classifier_ty"
    using typed_pp_Pure by (simp add: pp_unary_classifier_ty_def)
  have it: "\<Gamma> \<turnstile> ?I : pp_unary_ty"
    using typed_fun_prime_purity_builder ct by (rule has_type.App)
  have jt: "\<Gamma> \<turnstile> pp_fun_prime_classifier : pp_unary_ty"
    using typed_pp_fun_prime_classifier by (simp add: pp_unary_ty_def)
  have bp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure (pp_unary_classifier_ty \<rightarrow>\<^sub>o pp_unary_ty) ?B"
    by (rule CEV_control_pure_logical[OF core typed_fun_prime_purity_builder _
          typed_fun_prime_purity_builder])
      (simp add: pp_fun_prime_purity_builder_def)
  have pp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_target_PP"
    using core pp_T6_target_axiom
    by (intro CEV_axiom_proves.Axiom) (auto intro: infer_type_sound
      simp: pp_target_PP_def pp_purity_of_pure_def pp_pure_def pp_Pure_def lookup_def)
  have cp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_classifier_ty ?C"
    using pp by (simp add: pp_target_PP_def pp_purity_of_pure_def
      pp_unary_classifier_ty_def pp_unary_ty_def)
  have ip: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty ?I"
    using core pp_T6_application_closure_axiom
      typed_fun_prime_purity_builder ct bp cp
    by (meson pp_axiom_application_closed subsetD)
  have beta: "compatible_step beta_contract
      (pp_pure pp_unary_ty ?I) (pp_pure pp_unary_ty pp_fun_prime_classifier)"
    unfolding pp_pure_def
    by (intro compatible_step.App_right compatible_step.root fun_prime_builder_beta)
  have iff: "\<Gamma> \<turnstile>\<^sub>CEV
      (pp_pure pp_unary_ty ?I \<longleftrightarrow>\<^sub>o pp_pure pp_unary_ty pp_fun_prime_classifier)"
    using typed_pp_pure[OF it] typed_pp_pure[OF jt] beta by (rule CEV_beta_step)
  show ?thesis using ip
    CEV_axiom_proves.Base[OF CEV_beta_left_imp[OF typed_pp_pure[OF it] typed_pp_pure[OF jt] iff]]
    by (rule CEV_axiom_proves.MP)
qed

definition pp_fun_prime_control :: oterm where
  "pp_fun_prime_control = Lam Prop (Var 0 \<longleftrightarrow>\<^sub>o App pp_fun_prime_classifier (Var 0))"

definition pp_fun_prime_control_builder :: oterm where
  "pp_fun_prime_control_builder = Lam pp_unary_ty
    (Lam Prop (Var 0 \<longleftrightarrow>\<^sub>o App (Var 1) (Var 0)))"

lemma typed_fun_prime_control:
  "\<Gamma> \<turnstile> pp_fun_prime_control : pp_unary_ty"
proof -
  have jt: "Prop # \<Gamma> \<turnstile> pp_fun_prime_classifier : Prop \<rightarrow>\<^sub>o Prop"
    by (rule typed_pp_fun_prime_classifier)
  have vp: "Prop # \<Gamma> \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have jp: "Prop # \<Gamma> \<turnstile> App pp_fun_prime_classifier (Var 0) : Prop"
    using jt vp by (rule has_type.App)
  show ?thesis unfolding pp_fun_prime_control_def pp_unary_ty_def
    using vp jp by (intro has_type.Lam has_type.Conj has_type.Imp)
qed

lemma typed_fun_prime_control_builder:
  "\<Gamma> \<turnstile> pp_fun_prime_control_builder : pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_fun_prime_control_builder_def pp_unary_ty_def lookup_def)

lemma fun_prime_control_builder_beta:
  "beta_contract (App pp_fun_prime_control_builder pp_fun_prime_classifier) pp_fun_prime_control"
  using beta_contract.beta[where \<sigma> = pp_unary_ty
    and M = "Lam Prop (Var 0 \<longleftrightarrow>\<^sub>o App (Var 1) (Var 0))"
    and N = pp_fun_prime_classifier]
  by (simp add: pp_fun_prime_control_builder_def pp_fun_prime_control_def
    subst0_def shift_def[symmetric])

lemma fun_prime_control_beta:
  "compatible_step beta_contract (App pp_fun_prime_control p)
    (p \<longleftrightarrow>\<^sub>o App pp_fun_prime_classifier p)"
  using compatible_step.root[where R = beta_contract, OF beta_contract.beta[where \<sigma> = Prop
    and M = "Var 0 \<longleftrightarrow>\<^sub>o App pp_fun_prime_classifier (Var 0)" and N = p]]
  by (simp add: pp_fun_prime_control_def subst0_def pp_fun_prime_classifier_def
    pp_fun_prime_def pp_pure_def pp_Pure_def shift_by_def shift_ren_def shift_def eval_nat_numeral)

lemma CEV_control_beta:
  assumes p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    (App pp_fun_prime_control p \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o App pp_fun_prime_classifier p))"
  using has_type.App[OF typed_fun_prime_control[unfolded pp_unary_ty_def] p]
    p has_type.App[OF typed_pp_fun_prime_classifier p]
    fun_prime_control_beta
  by (intro CEV_beta_step) (auto intro: has_type.Conj has_type.Imp)

lemma CEV_control_pure_beta:
  assumes a: "\<Gamma> \<turnstile> A : \<sigma>" and b: "\<Gamma> \<turnstile> B : \<sigma>"
    and beta: "beta_contract A B"
    and pure: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure \<sigma> A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure \<sigma> B"
proof -
  have step: "compatible_step beta_contract (pp_pure \<sigma> A) (pp_pure \<sigma> B)"
    unfolding pp_pure_def using beta
    by (intro compatible_step.App_right compatible_step.root)
  have iff: "\<Gamma> \<turnstile>\<^sub>CEV (pp_pure \<sigma> A \<longleftrightarrow>\<^sub>o pp_pure \<sigma> B)"
    using typed_pp_pure[OF a] typed_pp_pure[OF b] step by (rule CEV_beta_step)
  show ?thesis using pure
    CEV_axiom_proves.Base[OF CEV_beta_left_imp[OF typed_pp_pure[OF a] typed_pp_pure[OF b] iff]]
    by (rule CEV_axiom_proves.MP)
qed

theorem CEV_fun_prime_control_pure:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty pp_fun_prime_control"
proof -
  have jt: "\<Gamma> \<turnstile> pp_fun_prime_classifier : pp_unary_ty"
    using typed_pp_fun_prime_classifier by (simp add: pp_unary_ty_def)
  have bp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty) pp_fun_prime_control_builder"
    by (rule CEV_control_pure_logical[OF core typed_fun_prime_control_builder _
          typed_fun_prime_control_builder]) (simp add: pp_fun_prime_control_builder_def)
  have cp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty pp_fun_prime_classifier"
    by (rule CEV_fun_prime_classifier_pure[OF core])
  have ip: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty
      (App pp_fun_prime_control_builder pp_fun_prime_classifier)"
    using core pp_T6_application_closure_axiom
      typed_fun_prime_control_builder jt bp cp
    by (meson pp_axiom_application_closed subsetD)
  show ?thesis
    using has_type.App[OF typed_fun_prime_control_builder jt]
      typed_fun_prime_control fun_prime_control_builder_beta ip
    by (rule CEV_control_pure_beta)
qed

lemma CEV_control_eq_trans:
  assumes "\<Gamma> \<turnstile> A : \<sigma>" "\<Gamma> \<turnstile> B : \<sigma>" "\<Gamma> \<turnstile> C : \<sigma>"
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> A B"
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> B C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> A C"
  using CEV_axiom_from_eq_trans[OF assms(1,2,3)
      CEV_axiom_from.Theorem[OF assms(4)] CEV_axiom_from.Theorem[OF assms(5)], where S = "{}"]
  by (simp add: CEV_axiom_from_empty_iff)

lemma CEV_control_J_beta_eq:
  assumes "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (App pp_fun_prime_classifier p) (pp_fun_prime p)"
  using has_type.App[OF typed_pp_fun_prime_classifier assms]
    typed_pp_fun_prime[OF assms]
    CEV_axiom_proves.Base[OF CEV_pp_fun_prime_classifier_beta[OF assms]]
  by (rule CEV_axiom_zeroary_equivalence)

theorem CEV_J_squared_eq_falsity:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (App pp_fun_prime_classifier (App pp_fun_prime_classifier p)) ObjFalse"
proof -
  let ?J = pp_fun_prime_classifier
  have jp: "\<Gamma> \<turnstile> App ?J p : Prop" using typed_pp_fun_prime_classifier p by (rule has_type.App)
  have fp: "\<Gamma> \<turnstile> pp_fun_prime p : Prop" using p by (rule typed_pp_fun_prime)
  have jjp: "\<Gamma> \<turnstile> App ?J (App ?J p) : Prop"
    using typed_pp_fun_prime_classifier jp by (rule has_type.App)
  have jfp: "\<Gamma> \<turnstile> App ?J (pp_fun_prime p) : Prop"
    using typed_pp_fun_prime_classifier fp by (rule has_type.App)
  have ffp: "\<Gamma> \<turnstile> pp_fun_prime (pp_fun_prime p) : Prop"
    using fp by (rule typed_pp_fun_prime)
  have first: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (App ?J (App ?J p)) (App ?J (pp_fun_prime p))"
    using CEV_axiom_from_eq_app_right[OF typed_pp_fun_prime_classifier jp fp
      CEV_axiom_from.Theorem[OF CEV_control_J_beta_eq[OF p]], where S = "{}"]
    by (simp add: CEV_axiom_from_empty_iff)
  have second: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (App ?J (pp_fun_prime p)) ObjFalse"
    using jfp ffp typed_ObjFalse CEV_control_J_beta_eq[OF fp]
      CEV_fun_prime_iteration_eq_falsity[OF core p]
    by (rule CEV_control_eq_trans)
  show ?thesis using jjp jfp typed_ObjFalse first second by (rule CEV_control_eq_trans)
qed

theorem CEV_control_square_if_control_identity:
  assumes p: "\<Gamma> \<turnstile> p : Prop"
    and control_identity: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq Prop (App pp_fun_prime_classifier (App pp_fun_prime_control p))
        (App pp_fun_prime_classifier p)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (App pp_fun_prime_control (App pp_fun_prime_control p)) p"
proof -
  let ?S = pp_fun_prime_control
  let ?J = pp_fun_prime_classifier
  have sp: "\<Gamma> \<turnstile> App ?S p : Prop"
    using typed_fun_prime_control p unfolding pp_unary_ty_def by (rule has_type.App)
  have ssp: "\<Gamma> \<turnstile> App ?S (App ?S p) : Prop"
    using typed_fun_prime_control sp unfolding pp_unary_ty_def by (rule has_type.App)
  have jp: "\<Gamma> \<turnstile> App ?J p : Prop"
    using typed_pp_fun_prime_classifier p by (rule has_type.App)
  have jsp: "\<Gamma> \<turnstile> App ?J (App ?S p) : Prop"
    using typed_pp_fun_prime_classifier sp by (rule has_type.App)
  have control_iff: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    (App ?J (App ?S p) \<longleftrightarrow>\<^sub>o App ?J p)"
    using jsp jp control_identity by (rule CEV_control_eq_iff)
  have b1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?S p \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o App ?J p))"
    using CEV_control_beta[OF p] by (rule CEV_axiom_proves.Base)
  have b2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    (App ?S (App ?S p) \<longleftrightarrow>\<^sub>o (App ?S p \<longleftrightarrow>\<^sub>o App ?J (App ?S p)))"
    using CEV_control_beta[OF sp] by (rule CEV_axiom_proves.Base)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (App ?S p \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o App ?J p))
      (Imp (App ?S (App ?S p) \<longleftrightarrow>\<^sub>o (App ?S p \<longleftrightarrow>\<^sub>o App ?J (App ?S p)))
        (Imp (App ?J (App ?S p) \<longleftrightarrow>\<^sub>o App ?J p)
          (App ?S (App ?S p) \<longleftrightarrow>\<^sub>o p)))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Conj p sp ssp jp jsp,
       simp only: prop_eval.simps, blast)
  have iff: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?S (App ?S p) \<longleftrightarrow>\<^sub>o p)"
    using CEV_axiom_proves.MP[OF control_iff CEV_axiom_proves.MP[OF b2 CEV_axiom_proves.MP[OF b1 taut]]] .
  show ?thesis using ssp p iff by (rule CEV_axiom_zeroary_equivalence)
qed

lemma shift_fun_prime_control[simp]:
  "shift pp_fun_prime_control = pp_fun_prime_control"
  by (simp add: pp_fun_prime_control_def pp_fun_prime_classifier_def pp_fun_prime_def
      pp_pure_def pp_Pure_def shift_def shift_by_def shift_ren_def)

theorem CEV_control_operator_involution_if_control_identity:
  assumes control_identity: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq Prop (App pp_fun_prime_classifier (App pp_fun_prime_control (Var 0)))
        (App pp_fun_prime_classifier (Var 0))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq pp_unary_ty (pp_compose pp_fun_prime_control pp_fun_prime_control) pp_identity_operator"
proof -
  let ?S = pp_fun_prime_control
  let ?v = "Var 0"
  let ?comp = "pp_compose ?S ?S"
  have vp: "Prop # \<Gamma> \<turnstile> ?v : Prop" by (rule typed_var0)
  have sp: "Prop # \<Gamma> \<turnstile> App ?S ?v : Prop"
    using typed_fun_prime_control vp unfolding pp_unary_ty_def by (rule has_type.App)
  have ssp: "Prop # \<Gamma> \<turnstile> App ?S (App ?S ?v) : Prop"
    using typed_fun_prime_control sp unfolding pp_unary_ty_def by (rule has_type.App)
  have cp: "Prop # \<Gamma> \<turnstile> App ?comp ?v : Prop"
    using typed_pp_compose[OF typed_fun_prime_control typed_fun_prime_control] vp
    unfolding pp_unary_ty_def by (rule has_type.App)
  have ip: "Prop # \<Gamma> \<turnstile> App pp_identity_operator ?v : Prop"
    using typed_pp_identity_operator vp unfolding pp_unary_ty_def by (rule has_type.App)
  have square: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?S (App ?S ?v) \<longleftrightarrow>\<^sub>o ?v)"
    using ssp vp CEV_control_square_if_control_identity[OF vp control_identity]
    by (rule CEV_control_eq_iff)
  have cb: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?comp ?v \<longleftrightarrow>\<^sub>o App ?S (App ?S ?v))"
    using CEV_pp_compose_apply[OF typed_fun_prime_control typed_fun_prime_control vp]
    by (rule CEV_axiom_proves.Base)
  have ib: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App pp_identity_operator ?v \<longleftrightarrow>\<^sub>o ?v)"
    using CEV_pp_identity_apply[OF vp] by (rule CEV_axiom_proves.Base)
  have taut: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (App ?comp ?v \<longleftrightarrow>\<^sub>o App ?S (App ?S ?v))
      (Imp (App ?S (App ?S ?v) \<longleftrightarrow>\<^sub>o ?v)
        (Imp (App pp_identity_operator ?v \<longleftrightarrow>\<^sub>o ?v)
          (App ?comp ?v \<longleftrightarrow>\<^sub>o App pp_identity_operator ?v)))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Conj cp ssp vp ip,
       simp only: prop_eval.simps, blast)
  have pointwise: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (shift ?comp) ?v \<longleftrightarrow>\<^sub>o App (shift pp_identity_operator) ?v)"
    using CEV_axiom_proves.MP[OF ib CEV_axiom_proves.MP[OF square CEV_axiom_proves.MP[OF cb taut]]]
    by simp
  show ?thesis using typed_pp_compose[OF typed_fun_prime_control typed_fun_prime_control]
    typed_pp_identity_operator pointwise by (rule CEV_control_unary_equivalence)
qed

theorem CEV_control_agrees_at_fun_prime:
  assumes p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime p) (App pp_fun_prime_control p \<longleftrightarrow>\<^sub>o p)"
proof -
  let ?S = pp_fun_prime_control
  let ?J = pp_fun_prime_classifier
  have sp: "\<Gamma> \<turnstile> App ?S p : Prop"
    using typed_fun_prime_control p unfolding pp_unary_ty_def by (rule has_type.App)
  have jp: "\<Gamma> \<turnstile> App ?J p : Prop"
    using typed_pp_fun_prime_classifier p by (rule has_type.App)
  have fp: "\<Gamma> \<turnstile> pp_fun_prime p : Prop" using p by (rule typed_pp_fun_prime)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (App ?S p \<longleftrightarrow>\<^sub>o (p \<longleftrightarrow>\<^sub>o App ?J p))
      (Imp (App ?J p \<longleftrightarrow>\<^sub>o pp_fun_prime p)
        (Imp (pp_fun_prime p) (App ?S p \<longleftrightarrow>\<^sub>o p)))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Conj sp p jp fp, simp only: prop_eval.simps, blast)
  show ?thesis
    using CEV_axiom_proves.MP[OF CEV_axiom_proves.Base[OF CEV_pp_fun_prime_classifier_beta[OF p]]
      CEV_axiom_proves.MP[OF CEV_axiom_proves.Base[OF CEV_control_beta[OF p]] taut]] .
qed

theorem CEV_control_not_truth_preserving:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (pp_truth_preserving pp_fun_prime_control)"
proof -
  let ?S = pp_fun_prime_control
  let ?J = pp_fun_prime_classifier
  let ?P = ObjTrue
  let ?TP = "pp_truth_preserving ?S"
  have st: "\<Gamma> \<turnstile> App ?S ?P : Prop"
    using typed_fun_prime_control typed_ObjTrue unfolding pp_unary_ty_def by (rule has_type.App)
  have jt: "\<Gamma> \<turnstile> App ?J ?P : Prop"
    using typed_pp_fun_prime_classifier typed_ObjTrue by (rule has_type.App)
  have ft: "\<Gamma> \<turnstile> pp_fun_prime ?P : Prop" by (intro typed_pp_fun_prime typed_ObjTrue)
  have tpt: "\<Gamma> \<turnstile> ?TP : Prop" by (intro typed_pp_truth_preserving typed_fun_prime_control)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (App ?S ?P \<longleftrightarrow>\<^sub>o (?P \<longleftrightarrow>\<^sub>o App ?J ?P))
      (Imp (App ?J ?P \<longleftrightarrow>\<^sub>o pp_fun_prime ?P)
        (Imp (Neg (pp_fun_prime ?P))
          (Imp ?P (Imp (Imp ?TP (App ?S ?P \<longleftrightarrow>\<^sub>o ?P)) (Neg ?TP)))))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Conj has_type.Neg st jt ft tpt typed_ObjTrue,
       simp only: prop_eval.simps, blast)
  show ?thesis using CEV_axiom_proves.MP[
    OF CEV_axiom_truth_preserving_instance[OF typed_ObjTrue typed_fun_prime_control]
    CEV_axiom_proves.MP[OF CEV_axiom_proves_ObjTrue
    CEV_axiom_proves.MP[OF CEV_not_fun_prime_ObjTrue[OF pp_T2_min_axioms_into_T6_extension[OF core]]
    CEV_axiom_proves.MP[OF CEV_axiom_proves.Base[OF CEV_pp_fun_prime_classifier_beta[OF typed_ObjTrue]]
    CEV_axiom_proves.MP[OF CEV_axiom_proves.Base[OF CEV_control_beta[OF typed_ObjTrue]] taut]]]]] .
qed

theorem CEV_control_not_truth_flipping_at_fun_prime:
  assumes p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime p) (Neg (pp_truth_flipping pp_fun_prime_control))"
proof -
  let ?S = pp_fun_prime_control
  let ?F = "pp_fun_prime p"
  let ?TF = "pp_truth_flipping ?S"
  have sp: "\<Gamma> \<turnstile> App ?S p : Prop"
    using typed_fun_prime_control p unfolding pp_unary_ty_def by (rule has_type.App)
  have ft: "\<Gamma> \<turnstile> ?F : Prop" using p by (rule typed_pp_fun_prime)
  have tft: "\<Gamma> \<turnstile> ?TF : Prop" by (intro typed_pp_truth_flipping typed_fun_prime_control)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Imp ?F (App ?S p \<longleftrightarrow>\<^sub>o p))
      (Imp (Imp ?TF (App ?S p \<longleftrightarrow>\<^sub>o Neg p)) (Imp ?F (Neg ?TF)))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Conj has_type.Neg p sp ft tft,
       simp only: prop_eval.simps, blast)
  show ?thesis using CEV_axiom_proves.MP[
    OF CEV_axiom_truth_flipping_instance[OF p typed_fun_prime_control]
      CEV_axiom_proves.MP[OF CEV_control_agrees_at_fun_prime[OF p] taut]] .
qed

theorem CEV_control_not_uniform_at_fun_prime:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T" and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime p)
    (Neg (Disj (pp_truth_preserving pp_fun_prime_control) (pp_truth_flipping pp_fun_prime_control)))"
proof -
  let ?TP = "pp_truth_preserving pp_fun_prime_control"
  let ?TF = "pp_truth_flipping pp_fun_prime_control"
  let ?F = "pp_fun_prime p"
  have ft: "\<Gamma> \<turnstile> ?F : Prop" using p by (rule typed_pp_fun_prime)
  have tpt: "\<Gamma> \<turnstile> ?TP : Prop" by (intro typed_pp_truth_preserving typed_fun_prime_control)
  have tft: "\<Gamma> \<turnstile> ?TF : Prop" by (intro typed_pp_truth_flipping typed_fun_prime_control)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Neg ?TP) (Imp (Imp ?F (Neg ?TF)) (Imp ?F (Neg (Disj ?TP ?TF))))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Neg has_type.Disj ft tpt tft,
       simp only: prop_eval.simps, blast)
  show ?thesis using CEV_axiom_proves.MP[
    OF CEV_control_not_truth_flipping_at_fun_prime[OF p]
      CEV_axiom_proves.MP[OF CEV_control_not_truth_preserving[OF core] taut]] .
qed

lemma subst_fun_prime_classifier[simp]:
  "subst s pp_fun_prime_classifier = pp_fun_prime_classifier"
  by (simp add: pp_fun_prime_classifier_def pp_fun_prime_def pp_pure_def
    pp_Pure_def shift_by_def shift_ren_def eval_nat_numeral)

lemma subst_fun_prime_control[simp]:
  "subst s pp_fun_prime_control = pp_fun_prime_control"
  by (simp add: pp_fun_prime_control_def)

lemma CEV_control_group_member_if_square:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and square: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq pp_unary_ty (pp_compose pp_fun_prime_control pp_fun_prime_control) pp_identity_operator"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_group_member pp_fun_prime_control"
proof -
  let ?S = pp_fun_prime_control
  let ?body = "Conj (pp_pure pp_unary_ty (Var 0))
    (Conj (Eq pp_unary_ty (pp_compose (shift ?S) (Var 0)) pp_identity_operator)
      (Eq pp_unary_ty (pp_compose (Var 0) (shift ?S)) pp_identity_operator))"
  have pure: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty ?S"
    by (rule CEV_fun_prime_control_pure[OF core])
  have witness: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Conj (pp_pure pp_unary_ty ?S)
      (Conj (Eq pp_unary_ty (pp_compose ?S ?S) pp_identity_operator)
        (Eq pp_unary_ty (pp_compose ?S ?S) pp_identity_operator))"
    using pure CEV_axiom_conj_intro[OF square square] by (rule CEV_axiom_conj_intro)
  have extype: "\<Gamma> \<turnstile> Exists pp_unary_ty ?body : Prop"
    using typed_pp_reversible[OF typed_fun_prime_control] by (simp only: pp_reversible_def)
  have bodytype: "pp_unary_ty # \<Gamma> \<turnstile> ?body : Prop"
    using extype by (auto elim: has_type.cases)
  have eg: "\<Gamma> \<turnstile>\<^sub>CEV Imp (subst0 ?S ?body) (Exists pp_unary_ty ?body)"
    using bodytype typed_fun_prime_control
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.EG)
  have inst: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ subst0 ?S ?body"
    using witness by (simp add: subst0_def pp_pure_def pp_Pure_def
      pp_compose_def pp_identity_operator_def subst_lift_shift)
  have rev: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_reversible ?S"
    using CEV_axiom_proves.MP[OF inst CEV_axiom_proves.Base[OF eg]]
    by (simp only: pp_reversible_def)
  show ?thesis unfolding pp_group_member_def
    using pure rev by (rule CEV_axiom_conj_intro)
qed

theorem CEV_control_not_uniform_if_exists_fun_prime:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and exists_in: "pp_exists_fun_prime \<in> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+
    Neg (Disj (pp_truth_preserving pp_fun_prime_control) (pp_truth_flipping pp_fun_prime_control))"
proof -
  let ?S = pp_fun_prime_control
  let ?R = "Neg (Disj (pp_truth_preserving ?S) (pp_truth_flipping ?S))"
  have ft: "[Prop] \<turnstile> pp_fun_prime (Var 0) : Prop"
    by (intro typed_pp_fun_prime typed_var0)
  have rt: "[] \<turnstile> ?R : Prop"
    by (intro has_type.Neg has_type.Disj typed_pp_truth_preserving
      typed_pp_truth_flipping typed_fun_prime_control)
  have parameter: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime (Var 0)) (shift ?R)"
  proof -
    have disj_shift: "\<And>A B. shift (Disj A B) = Disj (shift A) (shift B)"
      by (simp add: shift_def)
    show ?thesis using CEV_control_not_uniform_at_fun_prime[OF core typed_var0]
      by (simp add: disj_shift)
  qed
  have ex_rule: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp pp_exists_fun_prime ?R"
    using CEV_axiom_proves.Inst[OF ft rt parameter]
    by (simp only: pp_exists_fun_prime_def)
  have ex: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_exists_fun_prime"
    using exists_in typed_pp_exists_fun_prime by (rule CEV_axiom_proves.Axiom)
  show ?thesis using ex ex_rule by (rule CEV_axiom_proves.MP)
qed

theorem CEV_control_identity_would_refute_TU:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and exists_in: "pp_exists_fun_prime \<in> T"
    and control_identity: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq Prop (App pp_fun_prime_classifier (App pp_fun_prime_control (Var 0)))
        (App pp_fun_prime_classifier (Var 0))"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg pp_TU"
proof -
  let ?S = pp_fun_prime_control
  let ?U = "Disj (pp_truth_preserving ?S) (pp_truth_flipping ?S)"
  have gt: "[] \<turnstile> pp_group_member ?S : Prop"
    by (intro typed_pp_group_member typed_fun_prime_control)
  have ut: "[] \<turnstile> ?U : Prop"
    by (intro has_type.Disj typed_pp_truth_preserving typed_pp_truth_flipping typed_fun_prime_control)
  have group: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_group_member ?S"
    using core CEV_control_operator_involution_if_control_identity[OF control_identity]
    by (rule CEV_control_group_member_if_square)
  have notu: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg ?U"
    by (rule CEV_control_not_uniform_if_exists_fun_prime[OF core exists_in])
  have tu_type: "[] \<turnstile> pp_TU : Prop" by (rule typed_pp_TU)
  have local_tu: "[] ; T ; {pp_TU} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_TU"
    using tu_type by (intro CEV_axiom_from.Assumption) simp
  have inst: "[] ; T ; {pp_TU} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (pp_group_member ?S) ?U"
    using CEV_axiom_from_UI_typed[OF tu_type[unfolded pp_TU_def]
      typed_fun_prime_control local_tu[unfolded pp_TU_def]]
    by (simp add: subst0_def pp_TU_def)
  have uniform: "[] ; T ; {pp_TU} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?U"
    using CEV_axiom_from.Theorem[OF group] inst by (rule CEV_axiom_from.MP)
  have contradiction: "[] ; T ; {pp_TU} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using uniform CEV_axiom_from.Theorem[OF notu] by (rule CEV_axiom_from_contradiction)
  have imp: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp pp_TU ObjFalse"
    using tu_type contradiction by (rule CEV_axiom_from_singleton_imp)
  show ?thesis using imp
    CEV_axiom_proves.Base[OF CEV_proves_imp_false_to_neg[OF tu_type]]
    by (rule CEV_axiom_proves.MP)
qed

text \<open>
  The control identity remains an explicit DERIVABILITY premise in the last
  theorem. It is not an axiom introduced by this file, and no theorem here
  derives it from PP. A local biconditional is not promoted to identity.
  The result therefore does not establish either inconsistency or failure
  of TU from the original stock alone.
\<close>

ML \<open>
  val checked = [
    @{thm CEV_fun_prime_never_necessary},
    @{thm CEV_fun_prime_iteration_eq_falsity},
    @{thm CEV_J_squared_eq_falsity},
    @{thm CEV_fun_prime_classifier_pure},
    @{thm CEV_fun_prime_control_pure},
    @{thm CEV_control_operator_involution_if_control_identity},
    @{thm CEV_control_not_uniform_if_exists_fun_prime},
    @{thm CEV_control_identity_would_refute_TU}]
  val _ = List.app (fn thm =>
    if null (Thm_Deps.all_oracles [thm]) andalso null (Thm.hyps_of thm)
       andalso null (Thm.tpairs_of thm)
    then () else error "Fun-prime control audit failed") checked
  val _ = writeln "GOODMAN-FUN-PRIME-CONTROL: eight theorem objects kernel-clean"
\<close>

end
