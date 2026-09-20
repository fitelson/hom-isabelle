theory Bacon_PP_Control_Range
  imports 
    "Goodman_Legacy_Control_Heredity.Bacon_PP_Fun_Prime_Control_Heredity"
begin

section \<open>The range of the fun-prime control operator\<close>

definition pp_control_range_witness :: oterm where
  "pp_control_range_witness = Exists Prop
    (pp_fun_prime (App pp_fun_prime_control (Var 0)))"

definition pp_control_square :: oterm where
  "pp_control_square = pp_compose pp_fun_prime_control pp_fun_prime_control"

lemma typed_control_range_witness:
  "\<Gamma> \<turnstile> pp_control_range_witness : Prop"
  unfolding pp_control_range_witness_def
  using has_type.App[OF typed_fun_prime_control[unfolded pp_unary_ty_def] typed_var0]
  by (intro has_type.Exists typed_pp_fun_prime)

lemma typed_control_square:
  "\<Gamma> \<turnstile> pp_control_square : pp_unary_ty"
  unfolding pp_control_square_def
  by (intro typed_pp_compose typed_fun_prime_control)

lemma shift_control_square[simp]: "shift pp_control_square = pp_control_square"
  by (simp add: pp_control_square_def)

lemma subst_control_square[simp]: "subst s pp_control_square = pp_control_square"
  by (simp add: pp_control_square_def pp_compose_def subst_lift_shift)

lemma CEV_range_local_compose_agreement:
  assumes a: "\<Gamma> \<turnstile> A : pp_unary_ty" and b: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and f: "\<Gamma> \<turnstile> F : pp_unary_ty" and p: "\<Gamma> \<turnstile> p : Prop"
    and e: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App A (App F p)) (App B (App F p))"
  shows "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App (pp_compose A F) p) (App (pp_compose B F) p)"
proof -
  have fp: "\<Gamma> \<turnstile> App F p : Prop" using f p unfolding pp_unary_ty_def by (rule has_type.App)
  have ap: "\<Gamma> \<turnstile> App A (App F p) : Prop" using a fp unfolding pp_unary_ty_def by (rule has_type.App)
  have bp: "\<Gamma> \<turnstile> App B (App F p) : Prop" using b fp unfolding pp_unary_ty_def by (rule has_type.App)
  have ac: "\<Gamma> \<turnstile> App (pp_compose A F) p : Prop"
    using typed_pp_compose[OF a f] p unfolding pp_unary_ty_def by (rule has_type.App)
  have bc: "\<Gamma> \<turnstile> App (pp_compose B F) p : Prop"
    using typed_pp_compose[OF b f] p unfolding pp_unary_ty_def by (rule has_type.App)
  have left: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App (pp_compose A F) p) (App A (App F p))"
    using CEV_pp_compose_apply_eq[OF a f p] by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have right0: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App (pp_compose B F) p) (App B (App F p))"
    using CEV_pp_compose_apply_eq[OF b f p] by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have right: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App B (App F p)) (App (pp_compose B F) p)"
    using bc bp right0 by (rule CEV_axiom_from_eq_sym)
  have mid: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App (pp_compose A F) p) (App B (App F p))"
    using ac ap bp left e by (rule CEV_axiom_from_eq_trans)
  show ?thesis using ac bp bc mid right by (rule CEV_axiom_from_eq_trans)
qed

lemma CEV_range_local_application_after_composition:
  assumes a: "\<Gamma> \<turnstile> A : pp_unary_ty" and b: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and f: "\<Gamma> \<turnstile> F : pp_unary_ty" and p: "\<Gamma> \<turnstile> p : Prop"
    and e: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty (pp_compose A F) (pp_compose B F)"
  shows "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App A (App F p)) (App B (App F p))"
proof -
  have af: "\<Gamma> \<turnstile> pp_compose A F : pp_unary_ty" using a f by (rule typed_pp_compose)
  have bf: "\<Gamma> \<turnstile> pp_compose B F : pp_unary_ty" using b f by (rule typed_pp_compose)
  have fp: "\<Gamma> \<turnstile> App F p : Prop" using f p unfolding pp_unary_ty_def by (rule has_type.App)
  have ap: "\<Gamma> \<turnstile> App A (App F p) : Prop" using a fp unfolding pp_unary_ty_def by (rule has_type.App)
  have bp: "\<Gamma> \<turnstile> App B (App F p) : Prop" using b fp unfolding pp_unary_ty_def by (rule has_type.App)
  have ac: "\<Gamma> \<turnstile> App (pp_compose A F) p : Prop" using af p unfolding pp_unary_ty_def by (rule has_type.App)
  have bc: "\<Gamma> \<turnstile> App (pp_compose B F) p : Prop" using bf p unfolding pp_unary_ty_def by (rule has_type.App)
  have apps: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App (pp_compose A F) p) (App (pp_compose B F) p)"
    using af bf p e by (rule CEV_axiom_from_pp_apply_cong_left)
  have left0: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App (pp_compose A F) p) (App A (App F p))"
    using CEV_pp_compose_apply_eq[OF a f p] by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have left: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App A (App F p)) (App (pp_compose A F) p)"
    using ac ap left0 by (rule CEV_axiom_from_eq_sym)
  have right: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App (pp_compose B F) p) (App B (App F p))"
    using CEV_pp_compose_apply_eq[OF b f p] by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have mid: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App A (App F p)) (App (pp_compose B F) p)"
    using ap ac bc left apps by (rule CEV_axiom_from_eq_trans)
  show ?thesis using ap bc bp mid right by (rule CEV_axiom_from_eq_trans)
qed

lemma CEV_range_local_transfer:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop" and q: "\<Gamma> \<turnstile> q : Prop"
    and a: "\<Gamma> \<turnstile> A : pp_unary_ty" and b: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and fp: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
    and fsq: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime (App pp_fun_prime_control q)"
    and pa: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty A"
    and pb: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty B"
    and eq: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App A (App pp_fun_prime_control p)) (App B (App pp_fun_prime_control p))"
  shows "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty A B"
proof -
  let ?S = pp_fun_prime_control
  have st: "\<Gamma> \<turnstile> ?S : pp_unary_ty" by (rule typed_fun_prime_control)
  have ps: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty ?S"
    using CEV_fun_prime_control_pure[OF core] by (rule CEV_axiom_from.Theorem)
  have ast: "\<Gamma> \<turnstile> pp_compose A ?S : pp_unary_ty" using a st by (rule typed_pp_compose)
  have bst: "\<Gamma> \<turnstile> pp_compose B ?S : pp_unary_ty" using b st by (rule typed_pp_compose)
  have pas: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty (pp_compose A ?S)"
    using core a st pa ps by (rule pp_compose_pure_from)
  have pbs: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty (pp_compose B ?S)"
    using core b st pb ps by (rule pp_compose_pure_from)
  have at_p: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App (pp_compose A ?S) p) (App (pp_compose B ?S) p)"
    using a b st p eq by (rule CEV_range_local_compose_agreement)
  have operators: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq pp_unary_ty (pp_compose A ?S) (pp_compose B ?S)"
    using p ast bst fp pas pbs at_p by (rule CEV_axiom_from_fun_prime)
  have at_q: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App A (App ?S q)) (App B (App ?S q))"
    using a b st q operators by (rule CEV_range_local_application_after_composition)
  have sq: "\<Gamma> \<turnstile> App ?S q : Prop" using st q unfolding pp_unary_ty_def by (rule has_type.App)
  show ?thesis using sq a b fsq pa pb at_q by (rule CEV_axiom_from_fun_prime)
qed

lemma CEV_range_transfer_parameter:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop" and q: "\<Gamma> \<turnstile> q : Prop"
    and a: "\<Gamma> \<turnstile> A : pp_unary_ty" and b: "\<Gamma> \<turnstile> B : pp_unary_ty"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Conj (pp_fun_prime p) (pp_fun_prime (App pp_fun_prime_control q)))
      (Imp (Conj (pp_pure pp_unary_ty A) (pp_pure pp_unary_ty B))
        (Imp (Eq Prop (App A (App pp_fun_prime_control p)) (App B (App pp_fun_prime_control p)))
          (Eq pp_unary_ty A B)))"
proof -
  let ?S = pp_fun_prime_control
  let ?H = "Conj (pp_fun_prime p) (pp_fun_prime (App ?S q))"
  let ?PC = "Conj (pp_pure pp_unary_ty A) (pp_pure pp_unary_ty B)"
  let ?EQ = "Eq Prop (App A (App ?S p)) (App B (App ?S p))"
  let ?L = "insert ?EQ (insert ?PC {?H})"
  have sp: "\<Gamma> \<turnstile> App ?S p : Prop" using typed_fun_prime_control p unfolding pp_unary_ty_def by (rule has_type.App)
  have sq: "\<Gamma> \<turnstile> App ?S q : Prop" using typed_fun_prime_control q unfolding pp_unary_ty_def by (rule has_type.App)
  have ht: "\<Gamma> \<turnstile> ?H : Prop" using typed_pp_fun_prime[OF p] typed_pp_fun_prime[OF sq] by (rule has_type.Conj)
  have pct: "\<Gamma> \<turnstile> ?PC : Prop" using typed_pp_pure[OF a] typed_pp_pure[OF b] by (rule has_type.Conj)
  have eqt: "\<Gamma> \<turnstile> ?EQ : Prop"
    using has_type.App[OF a[unfolded pp_unary_ty_def] sp] has_type.App[OF b[unfolded pp_unary_ty_def] sp]
    by (rule has_type.Eq)
  have h: "\<Gamma> ; T ; ?L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H" using ht by (intro CEV_axiom_from.Assumption) simp
  have pc: "\<Gamma> ; T ; ?L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?PC" using pct by (intro CEV_axiom_from.Assumption) simp
  have eq: "\<Gamma> ; T ; ?L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?EQ" using eqt by (intro CEV_axiom_from.Assumption) simp
  have result: "\<Gamma> ; T ; ?L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty A B"
    using core p q a b CEV_axiom_from_conj_left[OF h] CEV_axiom_from_conj_right[OF h]
      CEV_axiom_from_conj_left[OF pc] CEV_axiom_from_conj_right[OF pc] eq
    by (rule CEV_range_local_transfer)
  have d1: "\<Gamma> ; T ; insert ?PC {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?EQ (Eq pp_unary_ty A B)"
    using eqt result by (rule CEV_axiom_from_deduction)
  have d2: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?PC (Imp ?EQ (Eq pp_unary_ty A B))"
    using pct d1 by (rule CEV_axiom_from_deduction)
  show ?thesis using ht d2 by (rule CEV_axiom_from_singleton_imp)
qed

lemma shift_two_control_app:
  "shift_by 2 (App pp_fun_prime_control p) = App pp_fun_prime_control (shift_by 2 p)"
  using shift_shift_eq_shift_by_2[of "App pp_fun_prime_control p"]
    shift_shift_eq_shift_by_2[of p] by simp

theorem CEV_control_separation_transfer:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop" and q: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Conj (pp_fun_prime p) (pp_fun_prime (App pp_fun_prime_control q)))
      (pp_fun_prime (App pp_fun_prime_control p))"
proof -
  let ?U = pp_unary_ty
  let ?S = pp_fun_prime_control
  let ?H = "Conj (pp_fun_prime p) (pp_fun_prime (App ?S q))"
  let ?p2 = "shift_by 2 p"
  let ?q2 = "shift_by 2 q"
  let ?BODY = "Imp (Conj (pp_pure ?U (Var 1)) (pp_pure ?U (Var 0)))
    (Imp (Eq Prop (App (Var 1) (App ?S ?p2)) (App (Var 0) (App ?S ?p2)))
      (Eq ?U (Var 1) (Var 0)))"
  have p2: "?U # ?U # \<Gamma> \<turnstile> ?p2 : Prop"
    using shift_by_preserves_typing[OF p, of "[?U,?U]"] by (simp add: numeral_2_eq_2)
  have q2: "?U # ?U # \<Gamma> \<turnstile> ?q2 : Prop"
    using shift_by_preserves_typing[OF q, of "[?U,?U]"] by (simp add: numeral_2_eq_2)
  have v1: "?U # ?U # \<Gamma> \<turnstile> Var 1 : ?U" by (rule has_type.Var) (simp add: lookup_def)
  have v0: "?U # ?U # \<Gamma> \<turnstile> Var 0 : ?U" by (rule typed_var0)
  have htype: "\<Gamma> \<turnstile> ?H : Prop"
    using typed_pp_fun_prime[OF p]
      typed_pp_fun_prime[OF has_type.App[OF typed_fun_prime_control[unfolded pp_unary_ty_def] q]]
    by (rule has_type.Conj)
  have parameter: "?U # ?U # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (shift (shift ?H)) ?BODY"
    using CEV_range_transfer_parameter[OF core p2 q2 v1 v0]
    by (simp add: shift_shift_eq_shift_by_2)
  have bt: "?U # ?U # \<Gamma> \<turnstile> ?BODY : Prop"
    using CEV_axiom_proves_formula[OF parameter] by (auto elim: has_type.cases)
  have h1: "?U # \<Gamma> \<turnstile> shift ?H : Prop" using htype by (rule typed_shift_ctx)
  have gen1: "?U # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ?H) (Forall ?U ?BODY)"
    using h1 bt parameter by (rule CEV_axiom_proves.Gen)
  have gen2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?H (Forall ?U (Forall ?U ?BODY))"
    using htype has_type.Forall[OF bt] gen1 by (rule CEV_axiom_proves.Gen)
  show ?thesis using gen2 by (simp only: pp_fun_prime_def shift_two_control_app)
qed

theorem CEV_control_fun_prime_on_range_forward:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T" and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime (App pp_fun_prime_control p))
      (pp_fun_prime (App pp_fun_prime_control (App pp_fun_prime_control p)))"
proof -
  let ?S = pp_fun_prime_control
  let ?F = "pp_fun_prime (App ?S p)"
  let ?G = "pp_fun_prime (App ?S (App ?S p))"
  have sp: "\<Gamma> \<turnstile> App ?S p : Prop"
    using typed_fun_prime_control p unfolding pp_unary_ty_def by (rule has_type.App)
  have ft: "\<Gamma> \<turnstile> ?F : Prop" using sp by (rule typed_pp_fun_prime)
  have gt: "\<Gamma> \<turnstile> ?G : Prop"
    using has_type.App[OF typed_fun_prime_control[unfolded pp_unary_ty_def] sp]
    by (rule typed_pp_fun_prime)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Imp (Conj ?F ?F) ?G) (Imp ?F ?G)"
    by (rule CEV_control_PC) (intro has_type.Imp has_type.Conj ft gt, simp only: prop_eval.simps, blast)
  show ?thesis using CEV_control_separation_transfer[OF core sp p] taut by (rule CEV_axiom_proves.MP)
qed

theorem CEV_control_identity_on_S_range:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (App pp_fun_prime_classifier (App pp_fun_prime_control (App pp_fun_prime_control p)))
      (App pp_fun_prime_classifier (App pp_fun_prime_control p))"
proof -
  let ?S = pp_fun_prime_control
  let ?J = pp_fun_prime_classifier
  have core: "pp_T6_core_PP_axioms \<subseteq> T" using ax by blast
  have sp: "\<Gamma> \<turnstile> App ?S p : Prop"
    using typed_fun_prime_control p unfolding pp_unary_ty_def by (rule has_type.App)
  have ssp: "\<Gamma> \<turnstile> App ?S (App ?S p) : Prop"
    using typed_fun_prime_control sp unfolding pp_unary_ty_def by (rule has_type.App)
  have fsp: "\<Gamma> \<turnstile> pp_fun_prime (App ?S p) : Prop" using sp by (rule typed_pp_fun_prime)
  have fssp: "\<Gamma> \<turnstile> pp_fun_prime (App ?S (App ?S p)) : Prop" using ssp by (rule typed_pp_fun_prime)
  have iff: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    (pp_fun_prime (App ?S (App ?S p)) \<longleftrightarrow>\<^sub>o pp_fun_prime (App ?S p))"
    using CEV_control_reflects_fun_prime_PP_exhaustion[OF ax sp]
      CEV_control_fun_prime_on_range_forward[OF core p] by (rule CEV_axiom_conj_intro)
  have eq: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (pp_fun_prime (App ?S (App ?S p))) (pp_fun_prime (App ?S p))"
    using fssp fsp iff by (rule CEV_axiom_zeroary_equivalence)
  have jsp: "\<Gamma> \<turnstile> App ?J (App ?S p) : Prop"
    using typed_pp_fun_prime_classifier sp by (rule has_type.App)
  have jssp: "\<Gamma> \<turnstile> App ?J (App ?S (App ?S p)) : Prop"
    using typed_pp_fun_prime_classifier ssp by (rule has_type.App)
  have first: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (App ?J (App ?S (App ?S p))) (pp_fun_prime (App ?S p))"
    using jssp fssp fsp CEV_control_J_beta_eq[OF ssp] eq by (rule CEV_control_eq_trans)
  show ?thesis using jssp fsp jsp first
    CEV_control_eq_sym[OF jsp fsp CEV_control_J_beta_eq[OF sp]] by (rule CEV_control_eq_trans)
qed

theorem CEV_control_cube_pointwise:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (App pp_fun_prime_control (App pp_fun_prime_control (App pp_fun_prime_control p)))
      (App pp_fun_prime_control p)"
  using has_type.App[OF typed_fun_prime_control[unfolded pp_unary_ty_def] p]
    CEV_control_identity_on_S_range[OF ax p] by (rule CEV_control_square_if_control_identity)

lemma CEV_control_square_fixes_range:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (App pp_control_square (App pp_fun_prime_control p)) (App pp_fun_prime_control p)"
proof -
  let ?S = pp_fun_prime_control
  have sp: "\<Gamma> \<turnstile> App ?S p : Prop"
    using typed_fun_prime_control p unfolding pp_unary_ty_def by (rule has_type.App)
  have ssp: "\<Gamma> \<turnstile> App ?S (App ?S p) : Prop"
    using typed_fun_prime_control sp unfolding pp_unary_ty_def by (rule has_type.App)
  have sssp: "\<Gamma> \<turnstile> App ?S (App ?S (App ?S p)) : Prop"
    using typed_fun_prime_control ssp unfolding pp_unary_ty_def by (rule has_type.App)
  have psp: "\<Gamma> \<turnstile> App pp_control_square (App ?S p) : Prop"
    using typed_control_square sp unfolding pp_unary_ty_def by (rule has_type.App)
  have beta: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App pp_control_square (App ?S p)) (App ?S (App ?S (App ?S p)))"
    unfolding pp_control_square_def using CEV_pp_compose_apply_eq[OF typed_fun_prime_control typed_fun_prime_control sp]
    by (rule CEV_axiom_proves.Base)
  show ?thesis using psp sssp sp beta CEV_control_cube_pointwise[OF ax p]
    by (rule CEV_control_eq_trans)
qed

theorem CEV_control_cube_eq_control:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq pp_unary_ty (pp_compose pp_control_square pp_fun_prime_control) pp_fun_prime_control"
proof -
  let ?S = pp_fun_prime_control
  let ?P = pp_control_square
  let ?V = "Var 0"
  let ?C = "pp_compose ?P ?S"
  have vp: "Prop # \<Gamma> \<turnstile> ?V : Prop" by (rule typed_var0)
  have sp: "Prop # \<Gamma> \<turnstile> App ?S ?V : Prop"
    using typed_fun_prime_control vp unfolding pp_unary_ty_def by (rule has_type.App)
  have psp: "Prop # \<Gamma> \<turnstile> App ?P (App ?S ?V) : Prop"
    using typed_control_square sp unfolding pp_unary_ty_def by (rule has_type.App)
  have cp: "Prop # \<Gamma> \<turnstile> App ?C ?V : Prop"
    using typed_pp_compose[OF typed_control_square typed_fun_prime_control] vp
    unfolding pp_unary_ty_def by (rule has_type.App)
  have beta: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App ?C ?V) (App ?P (App ?S ?V))"
    using CEV_pp_compose_apply_eq[OF typed_control_square typed_fun_prime_control vp]
    by (rule CEV_axiom_proves.Base)
  have eq: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App ?C ?V) (App ?S ?V)"
    using cp psp sp beta CEV_control_square_fixes_range[OF ax vp] by (rule CEV_control_eq_trans)
  have pointwise: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (shift ?C) ?V \<longleftrightarrow>\<^sub>o App (shift ?S) ?V)"
    using CEV_control_eq_iff[OF cp sp eq] by simp
  show ?thesis using typed_pp_compose[OF typed_control_square typed_fun_prime_control]
    typed_fun_prime_control pointwise by (rule CEV_control_unary_equivalence)
qed

lemma CEV_range_square_pure:
  assumes "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty pp_control_square"
  using pp_compose_pure_from[OF assms typed_fun_prime_control typed_fun_prime_control
      CEV_axiom_from.Theorem[OF CEV_fun_prime_control_pure[OF assms]]
      CEV_axiom_from.Theorem[OF CEV_fun_prime_control_pure[OF assms]], where S = "{}"]
  by (simp add: CEV_axiom_from_empty_iff pp_control_square_def)

lemma CEV_range_witness_square_parameter:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
    and q: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime (App pp_fun_prime_control q)) (Eq pp_unary_ty pp_control_square pp_identity_operator)"
proof -
  let ?S = pp_fun_prime_control
  let ?P = pp_control_square
  let ?I = pp_identity_operator
  let ?sq = "App ?S q"
  let ?H = "pp_fun_prime ?sq"
  have core: "pp_T6_core_PP_axioms \<subseteq> T" using ax by blast
  have sq: "\<Gamma> \<turnstile> ?sq : Prop"
    using typed_fun_prime_control q unfolding pp_unary_ty_def by (rule has_type.App)
  have psq: "\<Gamma> \<turnstile> App ?P ?sq : Prop"
    using typed_control_square sq unfolding pp_unary_ty_def by (rule has_type.App)
  have isq: "\<Gamma> \<turnstile> App ?I ?sq : Prop"
    using typed_pp_identity_operator sq unfolding pp_unary_ty_def by (rule has_type.App)
  have ht: "\<Gamma> \<turnstile> ?H : Prop" using sq by (rule typed_pp_fun_prime)
  have h: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using ht by (intro CEV_axiom_from.Assumption) simp
  have fixed_value: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?P ?sq) ?sq"
    using CEV_control_square_fixes_range[OF ax q] by (rule CEV_axiom_from.Theorem)
  have ib: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ?sq (App ?I ?sq)"
    using isq sq CEV_axiom_from.Theorem[OF CEV_axiom_proves.Base[OF CEV_pp_identity_operator_apply_eq[OF sq]]]
    by (rule CEV_axiom_from_eq_sym)
  have agree: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?P ?sq) (App ?I ?sq)"
    using psq sq isq fixed_value ib by (rule CEV_axiom_from_eq_trans)
  have result: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty ?P ?I"
    using sq typed_control_square typed_pp_identity_operator h
      CEV_axiom_from.Theorem[OF CEV_range_square_pure[OF core]]
      CEV_axiom_from.Theorem[OF pp_identity_operator_pure_in_core_extension[OF pp_T2_min_axioms_into_T6_extension[OF core]]] agree
    by (rule CEV_axiom_from_fun_prime)
  show ?thesis using ht result by (rule CEV_axiom_from_singleton_imp)
qed

theorem CEV_control_range_witness_implies_square_identity:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp pp_control_range_witness (Eq pp_unary_ty pp_control_square pp_identity_operator)"
proof -
  let ?F = "pp_fun_prime (App pp_fun_prime_control (Var 0))"
  let ?E = "Eq pp_unary_ty pp_control_square pp_identity_operator"
  have ft: "Prop # \<Gamma> \<turnstile> ?F : Prop"
    using has_type.App[OF typed_fun_prime_control[unfolded pp_unary_ty_def] typed_var0]
    by (rule typed_pp_fun_prime)
  have et: "\<Gamma> \<turnstile> ?E : Prop" using typed_control_square typed_pp_identity_operator by (rule has_type.Eq)
  have param: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?F (shift ?E)"
    using CEV_range_witness_square_parameter[OF ax typed_var0] by simp
  show ?thesis using CEV_axiom_proves.Inst[OF ft et param]
    by (simp only: pp_control_range_witness_def)
qed

lemma CEV_range_EG:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and mt: "\<Gamma> \<turnstile> M : \<sigma>"
    and inst: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s subst0 M A"
  shows "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Exists \<sigma> A"
proof -
  have rule: "\<Gamma> \<turnstile>\<^sub>CEV Imp (subst0 M A) (Exists \<sigma> A)"
    using body mt by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.EG)
  show ?thesis using inst CEV_axiom_from.Theorem[OF CEV_axiom_proves.Base[OF rule]]
    by (rule CEV_axiom_from.MP)
qed

lemma CEV_range_witness_intro:
  assumes q: "\<Gamma> \<turnstile> q : Prop"
    and f: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime (App pp_fun_prime_control q)"
  shows "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_control_range_witness"
proof -
  have bt: "Prop # \<Gamma> \<turnstile> pp_fun_prime (App pp_fun_prime_control (Var 0)) : Prop"
    using has_type.App[OF typed_fun_prime_control[unfolded pp_unary_ty_def] typed_var0]
    by (rule typed_pp_fun_prime)
  have inst: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    subst0 q (pp_fun_prime (App pp_fun_prime_control (Var 0)))"
    using f by (simp add: subst0_def)
  show ?thesis unfolding pp_control_range_witness_def using bt q inst by (rule CEV_range_EG)
qed

theorem CEV_control_square_idempotent:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq pp_unary_ty
    (pp_compose pp_control_square pp_control_square) pp_control_square"
proof -
  let ?S = pp_fun_prime_control
  let ?P = pp_control_square
  have pst: "\<Gamma> \<turnstile> pp_compose ?P ?S : pp_unary_ty"
    using typed_control_square typed_fun_prime_control by (rule typed_pp_compose)
  have pp: "\<Gamma> \<turnstile> pp_compose ?P ?P : pp_unary_ty"
    using typed_control_square typed_control_square by (rule typed_pp_compose)
  have midt: "\<Gamma> \<turnstile> pp_compose (pp_compose ?P ?S) ?S : pp_unary_ty"
    using pst typed_fun_prime_control by (rule typed_pp_compose)
  have assoc0: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq pp_unary_ty (pp_compose (pp_compose ?P ?S) ?S) (pp_compose ?P ?P)"
    using CEV_axiom_proves.Base[OF CEV_pp_compose_associative[OF typed_control_square typed_fun_prime_control typed_fun_prime_control]]
    by (simp only: pp_control_square_def)
  have assoc: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq pp_unary_ty (pp_compose ?P ?P) (pp_compose (pp_compose ?P ?S) ?S)"
    using midt pp assoc0 by (rule CEV_control_eq_sym)
  have cube: "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty (pp_compose ?P ?S) ?S"
    using CEV_control_cube_eq_control[OF ax] by (rule CEV_axiom_from.Theorem)
  have reduced_local: "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq pp_unary_ty (pp_compose (pp_compose ?P ?S) ?S) (pp_compose ?S ?S)"
    using pst typed_fun_prime_control typed_fun_prime_control cube
    by (rule CEV_axiom_from_pp_compose_cong_left)
  have reduced: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq pp_unary_ty (pp_compose (pp_compose ?P ?S) ?S) ?P"
    using reduced_local by (simp add: CEV_axiom_from_empty_iff pp_control_square_def)
  show ?thesis using pp midt typed_control_square assoc reduced by (rule CEV_control_eq_trans)
qed

lemma shift_control_range_witness[simp]:
  "shift pp_control_range_witness = pp_control_range_witness"
  by (simp add: pp_control_range_witness_def pp_fun_prime_control_def
      pp_fun_prime_classifier_def pp_fun_prime_def pp_pure_def pp_Pure_def
      shift_def shift_by_def shift_ren_def)

lemma CEV_range_curry:
  assumes a: "\<Gamma> \<turnstile> A : Prop" and b: "\<Gamma> \<turnstile> B : Prop"
    and c: "\<Gamma> \<turnstile> C : Prop"
    and local_result: "\<Gamma> ; T ; {Conj A B} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (Imp B C)"
proof -
  have implication: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Conj A B) C"
    using has_type.Conj[OF a b] local_result by (rule CEV_axiom_from_singleton_imp)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Imp (Conj A B) C) (Imp A (Imp B C))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Conj a b c, simp only: prop_eval.simps, blast)
  show ?thesis using implication taut by (rule CEV_axiom_proves.MP)
qed

lemma CEV_range_square_identity_witness_parameter:
  assumes p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime p)
    (Imp (Eq pp_unary_ty pp_control_square pp_identity_operator) pp_control_range_witness)"
proof -
  let ?S = pp_fun_prime_control
  let ?P = pp_control_square
  let ?I = pp_identity_operator
  let ?F = "pp_fun_prime p"
  let ?E = "Eq pp_unary_ty ?P ?I"
  let ?H = "Conj ?F ?E"
  have sp: "\<Gamma> \<turnstile> App ?S p : Prop"
    using typed_fun_prime_control p unfolding pp_unary_ty_def by (rule has_type.App)
  have ssp: "\<Gamma> \<turnstile> App ?S (App ?S p) : Prop"
    using typed_fun_prime_control sp unfolding pp_unary_ty_def by (rule has_type.App)
  have pp: "\<Gamma> \<turnstile> App ?P p : Prop"
    using typed_control_square p unfolding pp_unary_ty_def by (rule has_type.App)
  have ip: "\<Gamma> \<turnstile> App ?I p : Prop"
    using typed_pp_identity_operator p unfolding pp_unary_ty_def by (rule has_type.App)
  have ft: "\<Gamma> \<turnstile> ?F : Prop" using p by (rule typed_pp_fun_prime)
  have et: "\<Gamma> \<turnstile> ?E : Prop" using typed_control_square typed_pp_identity_operator by (rule has_type.Eq)
  have h: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using has_type.Conj[OF ft et] by (intro CEV_axiom_from.Assumption) simp
  have f: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using h by (rule CEV_axiom_from_conj_left)
  have e: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using h by (rule CEV_axiom_from_conj_right)
  have apps: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?P p) (App ?I p)"
    using typed_control_square typed_pp_identity_operator p e by (rule CEV_axiom_from_pp_apply_cong_left)
  have ib: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?I p) p"
    using CEV_pp_identity_operator_apply_eq[OF p] by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have pp_eq: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?P p) p"
    using pp ip p apps ib by (rule CEV_axiom_from_eq_trans)
  have rev: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p (App ?P p)"
    using pp p pp_eq by (rule CEV_axiom_from_eq_sym)
  have beta: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?P p) (App ?S (App ?S p))"
    unfolding pp_control_square_def using CEV_pp_compose_apply_eq[OF typed_fun_prime_control typed_fun_prime_control p]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have final_eq: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop p (App ?S (App ?S p))"
    using p pp ssp rev beta by (rule CEV_axiom_from_eq_trans)
  have fss: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime (App ?S (App ?S p))"
    using f CEV_axiom_from.MP[OF final_eq CEV_axiom_from.Theorem[OF CEV_axiom_fun_prime_eq_transport[OF p ssp]]]
    by (rule CEV_axiom_from.MP)
  have witness: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_control_range_witness"
    using sp fss by (rule CEV_range_witness_intro)
  show ?thesis using ft et typed_control_range_witness witness by (rule CEV_range_curry)
qed

theorem CEV_control_square_identity_implies_range_witness:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp pp_exists_fun_prime
    (Imp (Eq pp_unary_ty pp_control_square pp_identity_operator) pp_control_range_witness)"
proof -
  let ?Q = "Imp (Eq pp_unary_ty pp_control_square pp_identity_operator) pp_control_range_witness"
  have qt: "\<Gamma> \<turnstile> ?Q : Prop"
    by (intro has_type.Imp has_type.Eq typed_control_square typed_pp_identity_operator typed_control_range_witness)
  have parameter: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime (Var 0)) (shift ?Q)"
    using CEV_range_square_identity_witness_parameter[OF typed_var0] by simp
  show ?thesis using CEV_axiom_proves.Inst[OF typed_pp_fun_prime[OF typed_var0] qt parameter]
    by (simp only: pp_exists_fun_prime_def)
qed

lemma CEV_range_no_witness_excludes_fun_prime:
  assumes p: "\<Gamma> \<turnstile> p : Prop"
    and no: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg pp_control_range_witness"
  shows "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (pp_fun_prime (App pp_fun_prime_control p))"
proof -
  let ?F = "pp_fun_prime (App pp_fun_prime_control p)"
  have ft: "\<Gamma> \<turnstile> ?F : Prop"
    using has_type.App[OF typed_fun_prime_control[unfolded pp_unary_ty_def] p] by (rule typed_pp_fun_prime)
  have assumption: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using ft by (intro CEV_axiom_from.Assumption) simp
  have implication: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?F pp_control_range_witness"
    using ft CEV_range_witness_intro[OF p assumption] by (rule CEV_axiom_from_singleton_imp)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Imp ?F pp_control_range_witness) (Imp (Neg pp_control_range_witness) (Neg ?F))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Neg ft typed_control_range_witness, simp only: prop_eval.simps, blast)
  show ?thesis using no CEV_axiom_from.Theorem[OF CEV_axiom_proves.MP[OF implication taut]]
    by (rule CEV_axiom_from.MP)
qed

lemma CEV_range_no_witness_square_value:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
    and no: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg pp_control_range_witness"
  shows "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop
    (App pp_control_square p) (App (pp_compose pp_negation_operator pp_fun_prime_control) p)"
proof -
  let ?S = pp_fun_prime_control
  let ?P = pp_control_square
  let ?N = pp_negation_operator
  have sp: "\<Gamma> \<turnstile> App ?S p : Prop"
    using typed_fun_prime_control p unfolding pp_unary_ty_def by (rule has_type.App)
  have ssp: "\<Gamma> \<turnstile> App ?S (App ?S p) : Prop"
    using typed_fun_prime_control sp unfolding pp_unary_ty_def by (rule has_type.App)
  have pp: "\<Gamma> \<turnstile> App ?P p : Prop"
    using typed_control_square p unfolding pp_unary_ty_def by (rule has_type.App)
  have nsp: "\<Gamma> \<turnstile> Neg (App ?S p) : Prop" using sp by (rule has_type.Neg)
  have napps: "\<Gamma> \<turnstile> App ?N (App ?S p) : Prop"
    using typed_pp_negation_operator sp unfolding pp_unary_ty_def by (rule has_type.App)
  have ncp: "\<Gamma> \<turnstile> App (pp_compose ?N ?S) p : Prop"
    using typed_pp_compose[OF typed_pp_negation_operator typed_fun_prime_control] p
    unfolding pp_unary_ty_def by (rule has_type.App)
  have ss_neg: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?S (App ?S p)) (Neg (App ?S p))"
    using CEV_range_no_witness_excludes_fun_prime[OF p no]
      CEV_axiom_from.Theorem[OF CEV_control_eq_negation_when_not_fun_prime[OF ax sp]]
    by (rule CEV_axiom_from.MP)
  have pb: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?P p) (App ?S (App ?S p))"
    unfolding pp_control_square_def using CEV_pp_compose_apply_eq[OF typed_fun_prime_control typed_fun_prime_control p]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have nc: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App (pp_compose ?N ?S) p) (App ?N (App ?S p))"
    using CEV_pp_compose_apply_eq[OF typed_pp_negation_operator typed_fun_prime_control p]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have nb: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?N (App ?S p)) (Neg (App ?S p))"
    using CEV_pp_negation_apply_eq[OF sp]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have n_eq: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App (pp_compose ?N ?S) p) (Neg (App ?S p))"
    using ncp napps nsp nc nb by (rule CEV_axiom_from_eq_trans)
  have nrev: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (Neg (App ?S p)) (App (pp_compose ?N ?S) p)"
    using ncp nsp n_eq by (rule CEV_axiom_from_eq_sym)
  have mid: "\<Gamma> ; T ; L \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App ?P p) (Neg (App ?S p))"
    using pp ssp nsp pb ss_neg by (rule CEV_axiom_from_eq_trans)
  show ?thesis using pp nsp ncp mid nrev by (rule CEV_axiom_from_eq_trans)
qed

lemma CEV_range_negation_compose_pure:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty
    (pp_compose pp_negation_operator pp_fun_prime_control)"
proof -
  have member: "pp_pure pp_unary_ty pp_negation_operator \<in> T"
    using core pp_negation_operator_purity_axiom unfolding pp_T6_core_PP_axioms_def by blast
  have negpure: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty pp_negation_operator"
    using member typed_pp_pure[OF typed_pp_negation_operator] by (rule CEV_axiom_proves.Axiom)
  show ?thesis using pp_compose_pure_from[OF core typed_pp_negation_operator typed_fun_prime_control
    CEV_axiom_from.Theorem[OF negpure] CEV_axiom_from.Theorem[OF CEV_fun_prime_control_pure[OF core]], where S = "{}"]
    by (simp only: CEV_axiom_from_empty_iff)
qed

lemma CEV_range_negative_operator_parameter:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
    and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime p)
    (Imp (Neg pp_control_range_witness)
      (Eq pp_unary_ty pp_control_square (pp_compose pp_negation_operator pp_fun_prime_control)))"
proof -
  let ?P = pp_control_square
  let ?NS = "pp_compose pp_negation_operator pp_fun_prime_control"
  let ?F = "pp_fun_prime p"
  let ?NE = "Neg pp_control_range_witness"
  let ?H = "Conj ?F ?NE"
  have core: "pp_T6_core_PP_axioms \<subseteq> T" using ax by blast
  have nst: "\<Gamma> \<turnstile> ?NS : pp_unary_ty"
    by (intro typed_pp_compose typed_pp_negation_operator typed_fun_prime_control)
  have ft: "\<Gamma> \<turnstile> ?F : Prop" using p by (rule typed_pp_fun_prime)
  have nt: "\<Gamma> \<turnstile> ?NE : Prop" by (intro has_type.Neg typed_control_range_witness)
  have et: "\<Gamma> \<turnstile> Eq pp_unary_ty ?P ?NS : Prop"
    using typed_control_square nst by (rule has_type.Eq)
  have h: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H"
    using has_type.Conj[OF ft nt] by (intro CEV_axiom_from.Assumption) simp
  have f: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using h by (rule CEV_axiom_from_conj_left)
  have no: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?NE"
    using h by (rule CEV_axiom_from_conj_right)
  have eq: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq pp_unary_ty ?P ?NS"
    using p typed_control_square nst f
      CEV_axiom_from.Theorem[OF CEV_range_square_pure[OF core]]
      CEV_axiom_from.Theorem[OF CEV_range_negation_compose_pure[OF core]]
      CEV_range_no_witness_square_value[OF ax p no]
    by (rule CEV_axiom_from_fun_prime)
  show ?thesis using ft nt et eq by (rule CEV_range_curry)
qed

theorem CEV_control_no_range_witness_implies_negative_square:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp pp_exists_fun_prime
    (Imp (Neg pp_control_range_witness)
      (Eq pp_unary_ty pp_control_square (pp_compose pp_negation_operator pp_fun_prime_control)))"
proof -
  let ?Q = "Imp (Neg pp_control_range_witness)
    (Eq pp_unary_ty pp_control_square (pp_compose pp_negation_operator pp_fun_prime_control))"
  have qt: "\<Gamma> \<turnstile> ?Q : Prop"
    by (intro has_type.Imp has_type.Neg has_type.Eq typed_control_square
      typed_control_range_witness typed_pp_compose typed_pp_negation_operator typed_fun_prime_control)
  have parameter: "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime (Var 0)) (shift ?Q)"
    using CEV_range_negative_operator_parameter[OF ax typed_var0] by simp
  show ?thesis using CEV_axiom_proves.Inst[OF typed_pp_fun_prime[OF typed_var0] qt parameter]
    by (simp only: pp_exists_fun_prime_def)
qed

lemma typed_range_exists_fun_prime:
  "\<Gamma> \<turnstile> pp_exists_fun_prime : Prop"
  unfolding pp_exists_fun_prime_def by (intro has_type.Exists typed_pp_fun_prime typed_var0)

theorem CEV_control_range_witness_iff_square_identity:
  assumes ax: "insert pp_zeroary_exhaustion pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp pp_exists_fun_prime
    (pp_control_range_witness \<longleftrightarrow>\<^sub>o
      Eq pp_unary_ty pp_control_square pp_identity_operator)"
proof -
  let ?W = pp_exists_fun_prime
  let ?E = pp_control_range_witness
  let ?I = "Eq pp_unary_ty pp_control_square pp_identity_operator"
  have it: "\<Gamma> \<turnstile> ?I : Prop"
    by (intro has_type.Eq typed_control_square typed_pp_identity_operator)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (Imp ?E ?I) (Imp (Imp ?W (Imp ?I ?E)) (Imp ?W (?E \<longleftrightarrow>\<^sub>o ?I)))"
    by (rule CEV_control_PC)
      (intro has_type.Imp has_type.Conj typed_range_exists_fun_prime typed_control_range_witness it,
       simp only: prop_eval.simps, blast)
  show ?thesis using CEV_axiom_proves.MP[OF CEV_control_square_identity_implies_range_witness
    CEV_axiom_proves.MP[OF CEV_control_range_witness_implies_square_identity[OF ax] taut]] .
qed

end
