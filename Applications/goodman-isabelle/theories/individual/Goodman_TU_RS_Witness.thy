theory Goodman_TU_RS_Witness
  imports Goodman_TU_Inv_Exhaustion
begin

section \<open>The explicit true-and-fun′ witness for rigid specification\<close>

text \<open>
  R₊ = λp.(p ∧ fun′p). We prove its purity from PP by abstracting
  Pure into a closed logical builder; its purity is not an extra premise.
  Exhaustion is used only through the preceding TU-to-Inv theorem.
  L2 and strong L2 are not assumptions, and no T6 refutation is used.
\<close>

definition gi_RS_plus where
  "gi_RS_plus = Lam Prop (Conj (Var 0) (pp_fun_prime (Var 0)))"

definition gi_RS_plus_builder where
  "gi_RS_plus_builder = Lam (pp_unary_ty \<rightarrow>\<^sub>o Prop)
    (Lam Prop (Conj (Var 0)
      (Forall pp_unary_ty (Forall pp_unary_ty
        (Imp (Conj (App (Var 3) (Var 1)) (App (Var 3) (Var 0)))
          (Imp (Eq Prop (App (Var 1) (Var 2)) (App (Var 0) (Var 2)))
            (Eq pp_unary_ty (Var 1) (Var 0))))))))"

lemma gi_RS_plus_type:
  "\<Gamma> \<turnstile> gi_RS_plus : pp_unary_ty"
  unfolding gi_RS_plus_def pp_unary_ty_def
  by (rule has_type.Lam, rule has_type.Conj;
    (rule typed_var0 | rule typed_pp_fun_prime[OF typed_var0]))

lemma gi_RS_plus_builder_type:
  "\<Gamma> \<turnstile> gi_RS_plus_builder :
    (pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: gi_RS_plus_builder_def pp_unary_ty_def lookup_def)

lemma gi_RS_plus_builder_logical:
  "pp_logical_vocabulary gi_RS_plus_builder"
  by (simp add: gi_RS_plus_builder_def pp_logical_vocabulary_def)

lemma gi_RS_plus_builder_beta:
  "beta_contract (App gi_RS_plus_builder (pp_Pure pp_unary_ty)) gi_RS_plus"
proof -
  have raw: "beta_contract
    (App (Lam (pp_unary_ty \<rightarrow>\<^sub>o Prop)
      (Lam Prop (Conj (Var 0)
        (Forall pp_unary_ty (Forall pp_unary_ty
          (Imp (Conj (App (Var 3) (Var 1)) (App (Var 3) (Var 0)))
            (Imp (Eq Prop (App (Var 1) (Var 2)) (App (Var 0) (Var 2)))
              (Eq pp_unary_ty (Var 1) (Var 0))))))))) (pp_Pure pp_unary_ty))
    (subst0 (pp_Pure pp_unary_ty)
      (Lam Prop (Conj (Var 0)
        (Forall pp_unary_ty (Forall pp_unary_ty
          (Imp (Conj (App (Var 3) (Var 1)) (App (Var 3) (Var 0)))
            (Imp (Eq Prop (App (Var 1) (Var 2)) (App (Var 0) (Var 2)))
              (Eq pp_unary_ty (Var 1) (Var 0)))))))))"
    by (rule beta_contract.beta)
  show ?thesis using raw
    by (simp add: gi_RS_plus_builder_def gi_RS_plus_def pp_fun_prime_def pp_pure_def
      pp_Pure_def subst0_def shift_by_def shift_ren_def shift_def eval_nat_numeral)
qed

lemma gi_RS_plus_pure:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty gi_RS_plus"
proof -
  let ?c = "pp_Pure pp_unary_ty"
  let ?ct = "pp_unary_ty \<rightarrow>\<^sub>o Prop"
  let ?i = "App gi_RS_plus_builder ?c"
  have ct: "\<Gamma> \<turnstile> ?c : ?ct" by (rule typed_pp_Pure)
  have it: "\<Gamma> \<turnstile> ?i : pp_unary_ty"
    by (rule has_type.App[OF gi_RS_plus_builder_type ct])
  have member: "pp_pure (?ct \<rightarrow>\<^sub>o pp_unary_ty) gi_RS_plus_builder \<in> T"
    using core gi_RS_plus_builder_type[where \<Gamma>="[]"] gi_RS_plus_builder_logical
    unfolding pp_T6_core_PP_axioms_def pp_purity_schema_def by blast
  have bp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure (?ct \<rightarrow>\<^sub>o pp_unary_ty) gi_RS_plus_builder"
    by (rule CEV_axiom_proves.Axiom[OF member typed_pp_pure[OF gi_RS_plus_builder_type]])
  have pp_member: "pp_target_PP \<in> T" using core pp_T6_target_axiom by blast
  have cp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure ?ct ?c"
  proof -
    have member': "pp_pure ?ct ?c \<in> T"
      using pp_member by (simp add: pp_target_PP_def pp_purity_of_pure_def pp_unary_ty_def)
    show ?thesis by (rule CEV_axiom_proves.Axiom[OF member' typed_pp_pure[OF ct]])
  qed
  have closure: "pp_application_closure ?ct pp_unary_ty \<in> T"
    using core pp_T6_application_closure_axiom by blast
  have ip: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty ?i"
    by (rule pp_axiom_application_closed[OF closure gi_RS_plus_builder_type ct bp cp])
  have beta: "compatible_step beta_contract
    (pp_pure pp_unary_ty ?i) (pp_pure pp_unary_ty gi_RS_plus)"
    unfolding pp_pure_def
    by (rule compatible_step.App_right, rule compatible_step.root, rule gi_RS_plus_builder_beta)
  have at: "\<Gamma> \<turnstile> pp_pure pp_unary_ty ?i : Prop" by (rule typed_pp_pure[OF it])
  have bt: "\<Gamma> \<turnstile> pp_pure pp_unary_ty gi_RS_plus : Prop"
    by (rule typed_pp_pure[OF gi_RS_plus_type])
  have iff: "\<Gamma> \<turnstile>\<^sub>CEV
    (pp_pure pp_unary_ty ?i \<longleftrightarrow>\<^sub>o pp_pure pp_unary_ty gi_RS_plus)"
    by (rule CEV_beta_step[OF at bt beta])
  show ?thesis by (rule CEV_axiom_proves.MP[OF ip
    CEV_axiom_proves.Base[OF CEV_beta_left_imp[OF at bt iff]]])
qed

lemma gi_RS_plus_shift[simp]: "shift gi_RS_plus = gi_RS_plus"
  by (simp add: gi_RS_plus_def pp_fun_prime_def pp_pure_def pp_Pure_def
    shift_def shift_by_def shift_ren_def)

lemma gi_RS_plus_subst[simp]: "subst s gi_RS_plus = gi_RS_plus"
  by (simp add: gi_RS_plus_def pp_fun_prime_def pp_pure_def pp_Pure_def
    shift_def shift_by_def shift_ren_def)

lemma gi_RS_plus_apply_type:
  "\<Gamma> \<turnstile> p : Prop \<Longrightarrow> \<Gamma> \<turnstile> App gi_RS_plus p : Prop"
  using gi_RS_plus_type[unfolded pp_unary_ty_def] by (rule has_type.App)

lemma gi_RS_plus_beta:
  "compatible_step beta_contract (App gi_RS_plus p) (Conj p (pp_fun_prime p))"
proof (rule compatible_step.root)
  have raw: "beta_contract (App (Lam Prop (Conj (Var 0) (pp_fun_prime (Var 0)))) p)
    (subst0 p (Conj (Var 0) (pp_fun_prime (Var 0))))" by (rule beta_contract.beta)
  show "beta_contract (App gi_RS_plus p) (Conj p (pp_fun_prime p))"
    using raw by (simp add: gi_RS_plus_def subst0_def)
qed

lemma gi_RS_plus_apply_iff:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (App gi_RS_plus p \<longleftrightarrow>\<^sub>o Conj p (pp_fun_prime p))"
  by (rule CEV_beta_step[OF gi_RS_plus_apply_type[OF pt]
    has_type.Conj[OF pt typed_pp_fun_prime[OF pt]] gi_RS_plus_beta])

lemma gi_RS_plus_elim:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
    and rp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gi_RS_plus p"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj p (pp_fun_prime p)"
  by (rule CEV_axiom_from.MP[OF rp CEV_axiom_from_conj_left[OF
    CEV_axiom_from.Theorem[OF CEV_axiom_proves.Base[OF gi_RS_plus_apply_iff[OF pt]]]]])

lemma gi_RS_plus_intro:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
    and p: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s p"
    and fp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gi_RS_plus p"
  by (rule CEV_axiom_from.MP[OF CEV_axiom_from_conj_intro[OF p fp] CEV_axiom_from_conj_right[OF
    CEV_axiom_from.Theorem[OF CEV_axiom_proves.Base[OF gi_RS_plus_apply_iff[OF pt]]]]])

lemma gi_RS_plus_only_fun_prime:
  "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_spec_only_fun_prime gi_RS_plus"
proof -
  have pt: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have rt: "[Prop] \<turnstile> App gi_RS_plus (Var 0) : Prop" by (rule gi_RS_plus_apply_type[OF pt])
  have rp: "[Prop] ; T ; {App gi_RS_plus (Var 0)} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gi_RS_plus (Var 0)"
    by (rule CEV_axiom_from.Assumption; (simp | rule rt))
  have fp: "[Prop] ; T ; {App gi_RS_plus (Var 0)} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime (Var 0)"
    by (rule CEV_axiom_from_conj_right[OF gi_RS_plus_elim[OF pt rp]])
  have body: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App gi_RS_plus (Var 0)) (pp_fun_prime (Var 0))"
    by (rule CEV_axiom_from_singleton_imp[OF rt fp])
  have bt: "[Prop] \<turnstile> Imp (App gi_RS_plus (Var 0)) (pp_fun_prime (Var 0)) : Prop"
    by (rule CEV_axiom_proves_formula[OF body])
  show ?thesis unfolding pp_spec_only_fun_prime_def
    using CEV_axiom_generalize_theorem[OF bt body] by simp
qed

subsection \<open>Instantiation: choose a true member of a negation pair\<close>

lemma gi_RS_plus_exist_intro:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
    and p: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s p"
    and fp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_spec_instantiated gi_RS_plus"
proof -
  have inst: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    subst0 p (App (shift gi_RS_plus) (Var 0))"
    using gi_RS_plus_intro[OF pt p fp]
    by (simp add: subst0_def subst_lift_shift)
  show ?thesis unfolding pp_spec_instantiated_def
    by (rule CEV_axiom_from_EG_typed_RS[OF
      typed_pp_spec_instantiated[OF gi_RS_plus_type, unfolded pp_spec_instantiated_def] pt inst])
qed

lemma gi_RS_plus_instantiated_from_fun_prime:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T" and pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime p) (pp_spec_instantiated gi_RS_plus)"
proof -
  let ?f = "pp_fun_prime p"
  let ?e = "pp_spec_instantiated gi_RS_plus"
  have ft: "\<Gamma> \<turnstile> ?f : Prop" by (rule typed_pp_fun_prime[OF pt])
  have nt: "\<Gamma> \<turnstile> Neg p : Prop" by (rule has_type.Neg[OF pt])
  have et: "\<Gamma> \<turnstile> ?e : Prop" by (rule typed_pp_spec_instantiated[OF gi_RS_plus_type])
  have fp: "\<Gamma> ; T ; {?f} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?f"
    by (rule CEV_axiom_from.Assumption; (simp | rule ft))
  have em_base: "\<Gamma> \<turnstile>\<^sub>CEV Disj p (Neg p)"
    by (rule CEV_prop_tautology;
      unfold prop_tautology_def; intro conjI;
      (rule has_type.Disj[OF pt nt] | simp))
  have em: "\<Gamma> ; T ; {?f} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Disj p (Neg p)"
    by (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Base[OF em_base])
  have positive: "\<Gamma> ; T ; insert p {?f} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?e"
  proof -
    have truth: "\<Gamma> ; T ; insert p {?f} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s p"
      by (rule CEV_axiom_from.Assumption; (simp | rule pt))
    have free: "\<Gamma> ; T ; insert p {?f} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?f"
      by (rule CEV_axiom_from_mono[OF fp]; blast)
    show ?thesis by (rule gi_RS_plus_exist_intro[OF pt truth free])
  qed
  have negative: "\<Gamma> ; T ; insert (Neg p) {?f} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?e"
  proof -
    have truth: "\<Gamma> ; T ; insert (Neg p) {?f} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg p"
      by (rule CEV_axiom_from.Assumption; (simp | rule nt))
    have free: "\<Gamma> ; T ; insert (Neg p) {?f} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?f"
      by (rule CEV_axiom_from_mono[OF fp]; blast)
    have neg_free: "\<Gamma> ; T ; insert (Neg p) {?f} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime (Neg p)"
      by (rule CEV_axiom_from.MP[OF free CEV_axiom_from.Theorem[OF
        CEV_fun_prime_under_negation[OF core pt]]])
    show ?thesis by (rule gi_RS_plus_exist_intro[OF nt truth neg_free])
  qed
  have result: "\<Gamma> ; T ; {?f} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?e"
    by (rule CEV_axiom_from_T5_disj_cases[OF pt nt et em positive negative])
  show ?thesis by (rule CEV_axiom_from_singleton_imp[OF ft result])
qed

lemma gi_RS_plus_instantiated:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T" and existence: "pp_exists_fun_prime \<in> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_spec_instantiated gi_RS_plus"
proof -
  have ft: "[Prop] \<turnstile> pp_fun_prime (Var 0) : Prop"
    by (rule typed_pp_fun_prime[OF typed_var0])
  have et: "[] \<turnstile> pp_spec_instantiated gi_RS_plus : Prop"
    by (rule typed_pp_spec_instantiated[OF gi_RS_plus_type])
  have pt: "[Prop] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have raw: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime (Var 0)) (pp_spec_instantiated gi_RS_plus)"
    by (rule gi_RS_plus_instantiated_from_fun_prime[OF core pt])
  have body: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime (Var 0)) (shift (pp_spec_instantiated gi_RS_plus))"
    using raw by simp
  have imp: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp pp_exists_fun_prime (pp_spec_instantiated gi_RS_plus)"
    unfolding pp_exists_fun_prime_def by (rule CEV_axiom_proves.Inst[OF ft et body])
  have premise: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_exists_fun_prime"
    by (rule CEV_axiom_proves.Axiom[OF existence typed_pp_exists_fun_prime])
  show ?thesis by (rule CEV_axiom_proves.MP[OF premise imp])
qed

subsection \<open>Rigidity: identity is harmless and negation cannot join two true inputs\<close>

lemma gi_RS_standard_same_truth_equal:
  assumes zt: "\<Gamma> \<turnstile> Z : pp_unary_ty" and pt: "\<Gamma> \<turnstile> p : Prop"
    and qt: "\<Gamma> \<turnstile> q : Prop"
    and p: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s p"
    and q: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s q"
    and image: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop q (App Z p)"
    and standard: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty Z (gi_uniform_operator b)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p q"
proof -
  have zpt: "\<Gamma> \<turnstile> App Z p : Prop"
    by (rule has_type.App[OF zt[unfolded pp_unary_ty_def] pt])
  have opt: "\<Gamma> \<turnstile> App (gi_uniform_operator b) p : Prop"
    by (rule has_type.App[OF gi_uniform_operator_type[unfolded pp_unary_ty_def] pt])
  have app_eq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App Z p) (App (gi_uniform_operator b) p)"
    by (rule CEV_axiom_from_pp_apply_cong_left[OF zt gi_uniform_operator_type pt standard])
  have qop: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop q (App (gi_uniform_operator b) p)"
    by (rule CEV_axiom_from_eq_trans[OF qt zpt opt image app_eq])
  show ?thesis
  proof (cases b)
    case False
    have it: "\<Gamma> \<turnstile> App pp_identity_operator p : Prop"
      by (rule has_type.App[OF typed_pp_identity_operator[unfolded pp_unary_ty_def] pt])
    have qid: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop q (App pp_identity_operator p)"
      using qop by (simp only: False gi_uniform_operator_def if_False)
    have beta: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App pp_identity_operator p) p"
      by (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Base,
        rule CEV_pp_identity_operator_apply_eq[OF pt])
    have qp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop q p"
      by (rule CEV_axiom_from_eq_trans[OF qt it pt qid beta])
    show ?thesis by (rule CEV_axiom_from_eq_sym[OF qt pt qp])
  next
    case True
    have nt: "\<Gamma> \<turnstile> Neg p : Prop" by (rule has_type.Neg[OF pt])
    have npt: "\<Gamma> \<turnstile> App pp_negation_operator p : Prop"
      by (rule has_type.App[OF typed_pp_negation_operator[unfolded pp_unary_ty_def] pt])
    have qneg: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop q (App pp_negation_operator p)"
      using qop by (simp only: True gi_uniform_operator_def if_True)
    have beta: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App pp_negation_operator p) (Neg p)"
      by (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Base,
        rule CEV_pp_negation_apply_eq[OF pt])
    have qnp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop q (Neg p)"
      by (rule CEV_axiom_from_eq_trans[OF qt npt nt qneg beta])
    have np: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg p"
      by (rule CEV_axiom_from_eq_prop_elim[OF qt nt q qnp])
    have et: "\<Gamma> \<turnstile> Eq Prop p q : Prop" by (rule has_type.Eq[OF pt qt])
    have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp p (Imp (Neg p) (Eq Prop p q))"
      by (rule CEV_prop_tautology; unfold prop_tautology_def;
        intro conjI; (rule has_type.Imp[OF pt has_type.Imp[OF nt et]] | simp))
    show ?thesis by (rule CEV_axiom_from.MP[OF np CEV_axiom_from.MP[OF p
      CEV_axiom_from.Theorem[OF CEV_axiom_proves.Base[OF taut]]]])
  qed
qed

lemma gi_RS_plus_rigidity_local:
  assumes stock: "pp_T1_axioms \<subseteq> T" and tu: "pp_TU \<in> T"
    and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty" and pt: "\<Gamma> \<turnstile> p : Prop"
    and qt: "\<Gamma> \<turnstile> q : Prop"
    and group: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member Z"
    and rp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gi_RS_plus p"
    and rq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gi_RS_plus q"
    and image: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop q (App Z p)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p q"
proof -
  have p: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s p"
    by (rule CEV_axiom_from_conj_left[OF gi_RS_plus_elim[OF pt rp]])
  have q: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s q"
    by (rule CEV_axiom_from_conj_left[OF gi_RS_plus_elim[OF qt rq]])
  have classification: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Disj (Eq pp_unary_ty Z pp_identity_operator) (Eq pp_unary_ty Z pp_negation_operator)"
    by (rule CEV_axiom_from.MP[OF group CEV_axiom_from.Theorem[OF
      gi_TU_Exhaustion_group_classification[OF stock tu zt]]])
  have step: "\<And>b. \<Gamma> ; T ; insert (Eq pp_unary_ty Z (gi_uniform_operator b)) S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p q"
  proof -
    fix b
    let ?E = "Eq pp_unary_ty Z (gi_uniform_operator b)"
    have p': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s p"
      by (rule CEV_axiom_from_mono[OF p]; blast)
    have q': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s q"
      by (rule CEV_axiom_from_mono[OF q]; blast)
    have im': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop q (App Z p)"
      by (rule CEV_axiom_from_mono[OF image]; blast)
    have et: "\<Gamma> \<turnstile> ?E : Prop" by (rule has_type.Eq[OF zt gi_uniform_operator_type])
    have eq: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
      by (rule CEV_axiom_from.Assumption; (simp | rule et))
    show "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p q"
      by (rule gi_RS_standard_same_truth_equal[OF zt pt qt p' q' im' eq])
  qed
  have left: "\<Gamma> ; T ; insert (Eq pp_unary_ty Z pp_identity_operator) S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p q"
    using step[of False] by (simp only: gi_uniform_operator_def if_False)
  have right: "\<Gamma> ; T ; insert (Eq pp_unary_ty Z pp_negation_operator) S
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p q"
    using step[of True] by (simp only: gi_uniform_operator_def if_True)
  show ?thesis by (rule CEV_axiom_from_T5_disj_cases[OF
    has_type.Eq[OF zt typed_pp_identity_operator] has_type.Eq[OF zt typed_pp_negation_operator]
    has_type.Eq[OF pt qt] classification left right])
qed

definition gi_RS_plus_rigid_body where
  "gi_RS_plus_rigid_body Z p q = Imp
    (Conj (pp_group_member Z)
      (Conj (App gi_RS_plus p) (Conj (App gi_RS_plus q) (Eq Prop q (App Z p)))))
    (Eq Prop p q)"

lemma gi_RS_plus_rigid_parameter:
  assumes stock: "pp_T1_axioms \<subseteq> T" and tu: "pp_TU \<in> T"
    and zt: "\<Gamma> \<turnstile> Z : pp_unary_ty" and pt: "\<Gamma> \<turnstile> p : Prop"
    and qt: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gi_RS_plus_rigid_body Z p q"
proof -
  let ?A = "Conj (pp_group_member Z)
    (Conj (App gi_RS_plus p) (Conj (App gi_RS_plus q) (Eq Prop q (App Z p))))"
  have zpt: "\<Gamma> \<turnstile> App Z p : Prop"
    by (rule has_type.App[OF zt[unfolded pp_unary_ty_def] pt])
  have at: "\<Gamma> \<turnstile> ?A : Prop"
    by (intro has_type.Conj;
      (rule typed_pp_group_member[OF zt] | rule gi_RS_plus_apply_type[OF pt]
        | rule gi_RS_plus_apply_type[OF qt] | rule has_type.Eq[OF qt zpt]))
  have a: "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    by (rule CEV_axiom_from.Assumption; (simp | rule at))
  have g: "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_group_member Z"
    by (rule CEV_axiom_from_conj_left[OF a])
  have rp: "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gi_RS_plus p"
    by (rule CEV_axiom_from_conj_left[OF CEV_axiom_from_conj_right[OF a]])
  have rq: "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gi_RS_plus q"
    by (rule CEV_axiom_from_conj_left[OF CEV_axiom_from_conj_right[OF CEV_axiom_from_conj_right[OF a]]])
  have image: "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop q (App Z p)"
    by (rule CEV_axiom_from_conj_right[OF CEV_axiom_from_conj_right[OF CEV_axiom_from_conj_right[OF a]]])
  have result: "\<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p q"
    by (rule gi_RS_plus_rigidity_local[OF stock tu zt pt qt g rp rq image])
  show ?thesis unfolding gi_RS_plus_rigid_body_def
    by (rule CEV_axiom_from_singleton_imp[OF at result])
qed

lemma gi_RS_plus_rigid:
  assumes stock: "pp_T1_axioms \<subseteq> T" and tu: "pp_TU \<in> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_spec_rigid gi_RS_plus"
proof -
  let ?B = "gi_RS_plus_rigid_body (Var 2) (Var 1) (Var 0)"
  have zt: "[Prop, Prop, pp_unary_ty] \<turnstile> Var 2 : pp_unary_ty"
    by (rule has_type.Var; simp add: lookup_def)
  have pt: "[Prop, Prop, pp_unary_ty] \<turnstile> Var 1 : Prop"
    by (rule has_type.Var; simp add: lookup_def)
  have qt: "[Prop, Prop, pp_unary_ty] \<turnstile> Var 0 : Prop" by (rule typed_var0)
  have body: "[Prop, Prop, pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+ ?B"
    by (rule gi_RS_plus_rigid_parameter[OF stock tu zt pt qt])
  have bt: "[Prop, Prop, pp_unary_ty] \<turnstile> ?B : Prop"
    by (rule CEV_axiom_proves_formula[OF body])
  have allq: "[Prop, pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall Prop ?B"
    by (rule CEV_axiom_generalize_theorem[OF bt body])
  have allp: "[pp_unary_ty] ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall Prop (Forall Prop ?B)"
    by (rule CEV_axiom_generalize_theorem[OF has_type.Forall[OF bt] allq])
  have allz: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall pp_unary_ty (Forall Prop (Forall Prop ?B))"
    by (rule CEV_axiom_generalize_theorem[OF has_type.Forall[OF has_type.Forall[OF bt]] allp])
  show ?thesis using allz by (simp add: pp_spec_rigid_def gi_RS_plus_rigid_body_def)
qed

section \<open>The actual witness, and then the existential RS conclusion\<close>

theorem gi_CEV_TU_RS_explicit_witness:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and exhaustion: "pp_zeroary_exhaustion \<in> T"
    and existence: "pp_exists_fun_prime \<in> T" and tu: "pp_TU \<in> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_rigid_specification gi_RS_plus"
proof -
  have t1: "pp_T1_axioms \<subseteq> T"
    using core exhaustion unfolding pp_T1_axioms_def pp_T6_core_PP_axioms_def by blast
  have purity: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty gi_RS_plus"
    by (rule gi_RS_plus_pure[OF core])
  have instantiated: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_spec_instantiated gi_RS_plus"
    by (rule gi_RS_plus_instantiated[OF core existence])
  have only: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_spec_only_fun_prime gi_RS_plus"
    by (rule gi_RS_plus_only_fun_prime)
  have rigid: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_spec_rigid gi_RS_plus"
    by (rule gi_RS_plus_rigid[OF t1 tu])
  show ?thesis unfolding pp_rigid_specification_def
    by (rule CEV_axiom_conj_intro[OF purity CEV_axiom_conj_intro[OF instantiated
      CEV_axiom_conj_intro[OF only rigid]]])
qed

theorem gi_CEV_TU_Exhaustion_PP_exists_implies_RS:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and exhaustion: "pp_zeroary_exhaustion \<in> T"
    and existence: "pp_exists_fun_prime \<in> T" and tu: "pp_TU \<in> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_RS"
proof -
  have witness: "[] ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    subst0 gi_RS_plus (pp_rigid_specification (Var 0))"
    using CEV_axiom_from.Theorem[OF gi_CEV_TU_RS_explicit_witness[OF assms], where S="{}"]
    by (simp add: subst0_def)
  have result: "[] ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_RS"
    unfolding pp_RS_def
    by (rule CEV_axiom_from_EG_typed_RS[OF typed_pp_RS[unfolded pp_RS_def] gi_RS_plus_type witness])
  show ?thesis using result by (simp only: CEV_axiom_from_empty_iff)
qed

definition gi_TU_RS_axioms where
  "gi_TU_RS_axioms = pp_T6_core_PP_axioms \<union>
    {pp_zeroary_exhaustion, pp_exists_fun_prime, pp_TU}"

corollary gi_CEV_TU_RS_exact_witness:
  "[] ; gi_TU_RS_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_rigid_specification gi_RS_plus"
  by (rule gi_CEV_TU_RS_explicit_witness; auto simp: gi_TU_RS_axioms_def)

corollary gi_CEV_TU_RS_exact_stock:
  "[] ; gi_TU_RS_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_RS"
  by (rule gi_CEV_TU_Exhaustion_PP_exists_implies_RS; auto simp: gi_TU_RS_axioms_def)

text \<open>
  The conclusion certifies this particular R₊, rather than just obtaining
  an arbitrary formula from an inconsistent stock. The only impossible
  case eliminated in its rigidity proof is the local negation case:
  p and q are both true, whereas q=¬p would make p false. No theorem
  asserting falsity of the whole added stock is used.

  This settles a scope-corrected implication with zeroary Exhaustion.
  It does not settle whether TU implies RS in the weaker stock lacking
  Exhaustion, nor whether either direction of incomparability holds there.
\<close>

end
