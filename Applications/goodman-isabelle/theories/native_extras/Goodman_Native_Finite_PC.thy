theory Goodman_Native_Finite_PC
  imports Goodman_Native_T6_Extras
    "Goodman_Integration_Individual.Goodman_T1_Transfer"
begin

section \<open>Finite pure comprehension: the disjunction of identity properties\<close>

text \<open>
  Goodman's notes, p.3 (PC bullet): "In finite cases PC is a theorem
  (finite disjunctions of pure things are pure by application closure)."
  For parameters a₁,…,aₙ of one type σ we form Pₙ = λx.(x = aₙ ∨ … ∨ x = a₁),
  with P₀ = λx.⊥, and prove from the logical-purity and application-closure
  schemas alone: Pure(a₁) ∧ … ∧ Pure(aₙ) → Pure(Pₙ) ∧ ∀x.(Pₙ x ↔ (x = aₙ ∨ … ∨ x = a₁)).
  The parameters are the context variables Var 0,…,Var (n−1); the closed
  endpoint quantifies them universally. Identity is Leibniz identity at σ;
  the membership clause is a material biconditional. No PP, Exhaustion,
  Recombination, or fundamentality assumption occurs, and this is finite
  comprehension only: nothing is asserted about infinite pluralities.
\<close>

subsection \<open>The constructor-calculus family\<close>

fun gi_PC_disj :: "otype \<Rightarrow> nat \<Rightarrow> oterm" where
  "gi_PC_disj \<sigma> 0 = ObjFalse"
| "gi_PC_disj \<sigma> (Suc n) = Disj (Eq \<sigma> (Var 0) (Var (Suc n))) (gi_PC_disj \<sigma> n)"

definition gi_PC_selector where
  "gi_PC_selector \<sigma> n = Lam \<sigma> (gi_PC_disj \<sigma> n)"

fun gi_PC_hyp :: "otype \<Rightarrow> nat \<Rightarrow> oterm" where
  "gi_PC_hyp \<sigma> 0 = ObjTrue"
| "gi_PC_hyp \<sigma> (Suc n) = Conj (pp_pure \<sigma> (Var n)) (gi_PC_hyp \<sigma> n)"

definition gi_PC_membership where
  "gi_PC_membership \<sigma> n =
    Forall \<sigma> (App (shift (gi_PC_selector \<sigma> n)) (Var 0) \<longleftrightarrow>\<^sub>o gi_PC_disj \<sigma> n)"

definition gi_PC_matrix where
  "gi_PC_matrix \<sigma> n = Imp (gi_PC_hyp \<sigma> n)
    (Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (gi_PC_selector \<sigma> n)) (gi_PC_membership \<sigma> n))"

fun gi_PC_sentence :: "otype \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> oterm" where
  "gi_PC_sentence \<sigma> n 0 = gi_PC_matrix \<sigma> n"
| "gi_PC_sentence \<sigma> n (Suc m) = Forall \<sigma> (gi_PC_sentence \<sigma> n m)"

definition gi_finite_PC where
  "gi_finite_PC \<sigma> n = gi_PC_sentence \<sigma> n n"

definition gi_finite_PC_axioms where
  "gi_finite_PC_axioms = pp_purity_schema \<union> pp_application_closure_schema"

subsection \<open>Typing\<close>

lemma gi_PC_lookup_Suc: "lookup (\<tau> # \<Gamma>) (Suc i) = lookup \<Gamma> i"
  by (simp add: lookup_def)

lemma gi_PC_disj_type:
  assumes ctx: "\<And>i. i < n \<Longrightarrow> lookup \<Gamma> i = Some \<sigma>"
  shows "\<sigma> # \<Gamma> \<turnstile> gi_PC_disj \<sigma> n : Prop"
  using ctx
proof (induction n)
  case 0 show ?case by (simp add: typed_ObjFalse)
next
  case (Suc n)
  have param: "\<sigma> # \<Gamma> \<turnstile> Var (Suc n) : \<sigma>"
    by (rule has_type.Var) (simp add: gi_PC_lookup_Suc Suc.prems)
  have rest: "\<sigma> # \<Gamma> \<turnstile> gi_PC_disj \<sigma> n : Prop" by (rule Suc.IH) (simp add: Suc.prems)
  show ?case by (simp only: gi_PC_disj.simps; intro has_type.Disj has_type.Eq typed_var0 param rest)
qed

lemma gi_PC_selector_type:
  assumes ctx: "\<And>i. i < n \<Longrightarrow> lookup \<Gamma> i = Some \<sigma>"
  shows "\<Gamma> \<turnstile> gi_PC_selector \<sigma> n : \<sigma> \<rightarrow>\<^sub>o Prop"
  unfolding gi_PC_selector_def by (rule has_type.Lam[OF gi_PC_disj_type[OF ctx]])

lemma gi_PC_hyp_type:
  assumes ctx: "\<And>i. i < n \<Longrightarrow> lookup \<Gamma> i = Some \<sigma>"
  shows "\<Gamma> \<turnstile> gi_PC_hyp \<sigma> n : Prop"
  using ctx
proof (induction n)
  case 0 show ?case by (simp add: typed_ObjTrue)
next
  case (Suc n)
  have param: "\<Gamma> \<turnstile> Var n : \<sigma>" by (rule has_type.Var) (simp add: Suc.prems)
  show ?case
    by (simp only: gi_PC_hyp.simps; intro has_type.Conj typed_pp_pure[OF param] Suc.IH; simp add: Suc.prems)
qed

lemma gi_PC_membership_type:
  assumes ctx: "\<And>i. i < n \<Longrightarrow> lookup \<Gamma> i = Some \<sigma>"
  shows "\<Gamma> \<turnstile> gi_PC_membership \<sigma> n : Prop"
  unfolding gi_PC_membership_def
  by (intro has_type.Forall has_type.Conj has_type.Imp
    typed_shift_app[OF gi_PC_selector_type[OF ctx]] gi_PC_disj_type[OF ctx])

lemma gi_PC_matrix_type:
  assumes ctx: "\<And>i. i < n \<Longrightarrow> lookup \<Gamma> i = Some \<sigma>"
  shows "\<Gamma> \<turnstile> gi_PC_matrix \<sigma> n : Prop"
  unfolding gi_PC_matrix_def
  by (intro has_type.Imp has_type.Conj gi_PC_hyp_type[OF ctx]
    typed_pp_pure[OF gi_PC_selector_type[OF ctx]] gi_PC_membership_type[OF ctx])

subsection \<open>Reindexing: the shifted selector applied to the bound variable\<close>

lemma gi_PC_disj_reindex:
  "subst0 (Var 0) (rename (lift_ren Suc) (gi_PC_disj \<sigma> n)) = gi_PC_disj \<sigma> n"
  by (induction n) (simp_all add: ObjFalse_def ObjTrue_def subst0_def)

lemma gi_PC_selector_apply_beta:
  "compatible_step beta_contract (App (shift (gi_PC_selector \<sigma> n)) (Var 0)) (gi_PC_disj \<sigma> n)"
proof (rule compatible_step.root)
  have raw: "beta_contract (App (Lam \<sigma> (rename (lift_ren Suc) (gi_PC_disj \<sigma> n))) (Var 0))
    (subst0 (Var 0) (rename (lift_ren Suc) (gi_PC_disj \<sigma> n)))"
    by (rule beta_contract.beta)
  show "beta_contract (App (shift (gi_PC_selector \<sigma> n)) (Var 0)) (gi_PC_disj \<sigma> n)"
    using raw by (simp only: gi_PC_selector_def shift_def rename.simps gi_PC_disj_reindex)
qed

subsection \<open>The fixed closed logical step builder λa.λQ.λx.(x = a ∨ Q x)\<close>

definition gi_PC_step_builder where
  "gi_PC_step_builder \<sigma> = Lam \<sigma> (Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
    (Disj (Eq \<sigma> (Var 0) (Var 2)) (App (Var 1) (Var 0)))))"

lemma gi_PC_step_builder_type:
  "\<Gamma> \<turnstile> gi_PC_step_builder \<sigma> :
    \<sigma> \<rightarrow>\<^sub>o ((\<sigma> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o (\<sigma> \<rightarrow>\<^sub>o Prop))"
  unfolding gi_PC_step_builder_def
  by (intro has_type.Lam has_type.Disj has_type.Eq has_type.App has_type.Var; simp add: lookup_def)

lemma gi_PC_step_builder_logical:
  "pp_logical_vocabulary (gi_PC_step_builder \<sigma>)"
  by (simp add: gi_PC_step_builder_def pp_logical_vocabulary_def)

definition gi_PC_step_partial where
  "gi_PC_step_partial \<sigma> n = Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
    (Disj (Eq \<sigma> (Var 0) (Var (Suc (Suc n)))) (App (Var 1) (Var 0))))"

definition gi_PC_step_applied where
  "gi_PC_step_applied \<sigma> n = Lam \<sigma>
    (Disj (Eq \<sigma> (Var 0) (Var (Suc n))) (App (shift (gi_PC_selector \<sigma> n)) (Var 0)))"

lemma gi_PC_step_partial_type:
  assumes param: "lookup \<Gamma> n = Some \<sigma>"
  shows "\<Gamma> \<turnstile> gi_PC_step_partial \<sigma> n : (\<sigma> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o (\<sigma> \<rightarrow>\<^sub>o Prop)"
proof -
  let ?\<Delta> = "\<sigma> # (\<sigma> \<rightarrow>\<^sub>o Prop) # \<Gamma>"
  have v2: "?\<Delta> \<turnstile> Var (Suc (Suc n)) : \<sigma>"
    by (rule has_type.Var) (simp add: gi_PC_lookup_Suc param)
  have v1: "?\<Delta> \<turnstile> Var 1 : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Var) (simp add: lookup_def)
  have v0: "?\<Delta> \<turnstile> Var 0 : \<sigma>" by (rule typed_var0)
  have app: "?\<Delta> \<turnstile> App (Var 1) (Var 0) : Prop" by (rule has_type.App[OF v1 v0])
  show ?thesis unfolding gi_PC_step_partial_def
    by (intro has_type.Lam has_type.Disj has_type.Eq v0 v2 app)
qed

lemma gi_PC_step_applied_type:
  assumes ctx: "\<And>i. i < Suc n \<Longrightarrow> lookup \<Gamma> i = Some \<sigma>"
  shows "\<Gamma> \<turnstile> gi_PC_step_applied \<sigma> n : \<sigma> \<rightarrow>\<^sub>o Prop"
proof -
  have param: "\<sigma> # \<Gamma> \<turnstile> Var (Suc n) : \<sigma>"
    by (rule has_type.Var) (simp add: gi_PC_lookup_Suc ctx)
  have sel: "\<sigma> # \<Gamma> \<turnstile> App (shift (gi_PC_selector \<sigma> n)) (Var 0) : Prop"
    by (rule typed_shift_app[OF gi_PC_selector_type]) (simp add: ctx)
  show ?thesis unfolding gi_PC_step_applied_def
    by (intro has_type.Lam has_type.Disj has_type.Eq typed_var0 param sel)
qed

lemma gi_PC_step_beta1:
  "compatible_step beta_contract (App (App (gi_PC_step_builder \<sigma>) (Var n)) (gi_PC_selector \<sigma> n))
    (App (gi_PC_step_partial \<sigma> n) (gi_PC_selector \<sigma> n))"
proof (rule compatible_step.App_left, rule compatible_step.root)
  have raw: "beta_contract (App (Lam \<sigma> (Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
      (Disj (Eq \<sigma> (Var 0) (Var 2)) (App (Var 1) (Var 0)))))) (Var n))
    (subst0 (Var n) (Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
      (Disj (Eq \<sigma> (Var 0) (Var 2)) (App (Var 1) (Var 0))))))"
    by (rule beta_contract.beta)
  show "beta_contract (App (gi_PC_step_builder \<sigma>) (Var n)) (gi_PC_step_partial \<sigma> n)"
    using raw by (simp add: gi_PC_step_builder_def gi_PC_step_partial_def subst0_def eval_nat_numeral)
qed

lemma gi_PC_step_beta2:
  "compatible_step beta_contract (App (gi_PC_step_partial \<sigma> n) (gi_PC_selector \<sigma> n))
    (gi_PC_step_applied \<sigma> n)"
proof (rule compatible_step.root)
  have raw: "beta_contract (App (Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
      (Disj (Eq \<sigma> (Var 0) (Var (Suc (Suc n)))) (App (Var 1) (Var 0))))) (gi_PC_selector \<sigma> n))
    (subst0 (gi_PC_selector \<sigma> n) (Lam \<sigma>
      (Disj (Eq \<sigma> (Var 0) (Var (Suc (Suc n)))) (App (Var 1) (Var 0)))))"
    by (rule beta_contract.beta)
  show "beta_contract (App (gi_PC_step_partial \<sigma> n) (gi_PC_selector \<sigma> n)) (gi_PC_step_applied \<sigma> n)"
    using raw by (simp add: gi_PC_step_partial_def gi_PC_step_applied_def subst0_def shift_def)
qed

lemma gi_PC_step_beta3:
  "compatible_step beta_contract (gi_PC_step_applied \<sigma> n) (gi_PC_selector \<sigma> (Suc n))"
  unfolding gi_PC_step_applied_def gi_PC_selector_def gi_PC_disj.simps
  by (rule compatible_step.Lam_body, rule compatible_step.Disj_right,
    rule gi_PC_selector_apply_beta[unfolded gi_PC_selector_def])

subsection \<open>Purity transport along a β-step\<close>

lemma gi_PC_pure_beta_from:
  assumes mt: "\<Gamma> \<turnstile> M : \<tau>" and nt: "\<Gamma> \<turnstile> N : \<tau>"
    and step: "compatible_step beta_contract M N"
    and pure: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<tau> M"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<tau> N"
proof -
  have at: "\<Gamma> \<turnstile> pp_pure \<tau> M : Prop" by (rule typed_pp_pure[OF mt])
  have bt: "\<Gamma> \<turnstile> pp_pure \<tau> N : Prop" by (rule typed_pp_pure[OF nt])
  have fstep: "compatible_step beta_contract (pp_pure \<tau> M) (pp_pure \<tau> N)"
    unfolding pp_pure_def by (rule compatible_step.App_right[OF step])
  have iff: "\<Gamma> \<turnstile>\<^sub>CEV (pp_pure \<tau> M \<longleftrightarrow>\<^sub>o pp_pure \<tau> N)"
    by (rule CEV_beta_step[OF at bt fstep])
  show ?thesis by (rule CEV_axiom_from.MP[OF pure CEV_axiom_from.Theorem[OF
    CEV_axiom_proves.Base[OF CEV_beta_left_imp[OF at bt iff]]]])
qed

subsection \<open>Purity of the selector by induction on the list length\<close>

lemma gi_PC_closed_logical_pure:
  assumes stock: "gi_finite_PC_axioms \<subseteq> T" and mt: "[] \<turnstile> M : \<tau>"
    and logical: "pp_logical_vocabulary M"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<tau> M"
proof -
  have member: "pp_pure \<tau> M \<in> T"
    using stock mt logical unfolding gi_finite_PC_axioms_def pp_purity_schema_def by blast
  have typed: "\<Gamma> \<turnstile> pp_pure \<tau> M : Prop"
    by (rule typed_pp_pure[OF gi_old_closed_weaken[OF mt]])
  show ?thesis by (rule CEV_axiom_from.Theorem[OF CEV_axiom_proves.Axiom[OF member typed]])
qed

lemma gi_PC_empty_selector_logical: "pp_logical_vocabulary (gi_PC_selector \<sigma> 0)"
  by (simp add: gi_PC_selector_def pp_logical_vocabulary_def ObjFalse_def ObjTrue_def)

theorem gi_PC_empty_selector_pure:
  assumes stock: "gi_finite_PC_axioms \<subseteq> T"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (gi_PC_selector \<sigma> 0)"
  by (rule gi_PC_closed_logical_pure[OF stock gi_PC_selector_type gi_PC_empty_selector_logical]) simp

theorem gi_PC_selector_pure_from:
  assumes stock: "gi_finite_PC_axioms \<subseteq> T"
    and ctx: "\<And>i. i < n \<Longrightarrow> lookup \<Gamma> i = Some \<sigma>"
    and hyps: "\<And>i. i < n \<Longrightarrow> \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<sigma> (Var i)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (gi_PC_selector \<sigma> n)"
  using ctx hyps
proof (induction n)
  case 0 show ?case by (rule gi_PC_empty_selector_pure[OF stock])
next
  case (Suc n)
  let ?u = "\<sigma> \<rightarrow>\<^sub>o Prop"
  let ?C = "gi_PC_step_builder \<sigma>"
  let ?Q = "gi_PC_selector \<sigma> n"
  have ctx_n: "\<And>i. i < n \<Longrightarrow> lookup \<Gamma> i = Some \<sigma>" using Suc.prems(1) by simp
  have param_lookup: "lookup \<Gamma> n = Some \<sigma>" using Suc.prems(1) by simp
  have at: "\<Gamma> \<turnstile> Var n : \<sigma>" by (rule has_type.Var[OF param_lookup])
  have qt: "\<Gamma> \<turnstile> ?Q : ?u" by (rule gi_PC_selector_type[OF ctx_n])
  have ct: "\<Gamma> \<turnstile> ?C : \<sigma> \<rightarrow>\<^sub>o (?u \<rightarrow>\<^sub>o ?u)" by (rule gi_PC_step_builder_type)
  have cat: "\<Gamma> \<turnstile> App ?C (Var n) : ?u \<rightarrow>\<^sub>o ?u" by (rule has_type.App[OF ct at])
  have caqt: "\<Gamma> \<turnstile> App (App ?C (Var n)) ?Q : ?u" by (rule has_type.App[OF cat qt])
  have pt: "\<Gamma> \<turnstile> App (gi_PC_step_partial \<sigma> n) ?Q : ?u"
    by (rule has_type.App[OF gi_PC_step_partial_type[OF param_lookup] qt])
  have appt: "\<Gamma> \<turnstile> gi_PC_step_applied \<sigma> n : ?u" by (rule gi_PC_step_applied_type[OF Suc.prems(1)])
  have selt: "\<Gamma> \<turnstile> gi_PC_selector \<sigma> (Suc n) : ?u" by (rule gi_PC_selector_type[OF Suc.prems(1)])
  have pure_C: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure (\<sigma> \<rightarrow>\<^sub>o (?u \<rightarrow>\<^sub>o ?u)) ?C"
    by (rule gi_PC_closed_logical_pure[OF stock gi_PC_step_builder_type gi_PC_step_builder_logical])
  have pure_a: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<sigma> (Var n)" by (rule Suc.prems(2)) simp
  have pure_Q: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure ?u ?Q"
  proof (rule Suc.IH)
    fix i assume "i < n" then show "lookup \<Gamma> i = Some \<sigma>" by (rule ctx_n)
  next
    fix i assume "i < n" then show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<sigma> (Var i)"
      by (intro Suc.prems(2)) simp
  qed
  have closure1: "pp_application_closure \<sigma> (?u \<rightarrow>\<^sub>o ?u) \<in> T"
    and closure2: "pp_application_closure ?u ?u \<in> T"
    using stock unfolding gi_finite_PC_axioms_def pp_application_closure_schema_def by blast+
  have pure_Ca: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure (?u \<rightarrow>\<^sub>o ?u) (App ?C (Var n))"
    by (rule pp_axiom_application_closed_from[OF closure1 ct at pure_C pure_a])
  have pure_CaQ: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure ?u (App (App ?C (Var n)) ?Q)"
    by (rule pp_axiom_application_closed_from[OF closure2 cat qt pure_Ca pure_Q])
  have step1: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure ?u (App (gi_PC_step_partial \<sigma> n) ?Q)"
    by (rule gi_PC_pure_beta_from[OF caqt pt gi_PC_step_beta1 pure_CaQ])
  have step2: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure ?u (gi_PC_step_applied \<sigma> n)"
    by (rule gi_PC_pure_beta_from[OF pt appt gi_PC_step_beta2 step1])
  show ?case by (rule gi_PC_pure_beta_from[OF appt selt gi_PC_step_beta3 step2])
qed

subsection \<open>Membership, hypothesis extraction, and the closed sentence\<close>

theorem gi_PC_membership_theorem:
  assumes ctx: "\<And>i. i < n \<Longrightarrow> lookup \<Gamma> i = Some \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gi_PC_membership \<sigma> n"
proof -
  let ?A = "App (shift (gi_PC_selector \<sigma> n)) (Var 0)"
  let ?D = "gi_PC_disj \<sigma> n"
  have at: "\<sigma> # \<Gamma> \<turnstile> ?A : Prop" by (rule typed_shift_app[OF gi_PC_selector_type[OF ctx]])
  have dt: "\<sigma> # \<Gamma> \<turnstile> ?D : Prop" by (rule gi_PC_disj_type[OF ctx])
  have iff: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV (?A \<longleftrightarrow>\<^sub>o ?D)"
    by (rule CEV_beta_step[OF at dt gi_PC_selector_apply_beta])
  have body: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (?A \<longleftrightarrow>\<^sub>o ?D)" by (rule CEV_axiom_proves.Base[OF iff])
  have bt: "\<sigma> # \<Gamma> \<turnstile> (?A \<longleftrightarrow>\<^sub>o ?D) : Prop" by (intro has_type.Conj has_type.Imp at dt)
  show ?thesis unfolding gi_PC_membership_def by (rule CEV_axiom_generalize_theorem[OF bt body])
qed

lemma gi_PC_hyp_elim:
  assumes lt: "i < n" and hyp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s gi_PC_hyp \<sigma> n"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure \<sigma> (Var i)"
  using lt hyp
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "i = n")
    case True
    show ?thesis using CEV_axiom_from_conj_left[OF Suc.prems(2)[unfolded gi_PC_hyp.simps]]
      by (simp only: True)
  next
    case False
    have lt: "i < n" using Suc.prems(1) False by simp
    show ?thesis by (rule Suc.IH[OF lt CEV_axiom_from_conj_right[OF Suc.prems(2)[unfolded gi_PC_hyp.simps]]])
  qed
qed

theorem gi_PC_matrix_theorem:
  assumes stock: "gi_finite_PC_axioms \<subseteq> T"
    and ctx: "\<And>i. i < n \<Longrightarrow> lookup \<Gamma> i = Some \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gi_PC_matrix \<sigma> n"
proof -
  let ?H = "gi_PC_hyp \<sigma> n"
  have ht: "\<Gamma> \<turnstile> ?H : Prop" by (rule gi_PC_hyp_type[OF ctx])
  have h: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?H" by (rule CEV_axiom_from.Assumption[OF _ ht]) simp
  have pure: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (gi_PC_selector \<sigma> n)"
    by (rule gi_PC_selector_pure_from[OF stock ctx gi_PC_hyp_elim[OF _ h]])
  have mem: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s gi_PC_membership \<sigma> n"
    by (rule CEV_axiom_from.Theorem[OF gi_PC_membership_theorem[OF ctx]])
  have both: "\<Gamma> ; T ; {?H} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (gi_PC_selector \<sigma> n)) (gi_PC_membership \<sigma> n)"
    by (rule CEV_axiom_from_conj_intro[OF pure mem])
  show ?thesis unfolding gi_PC_matrix_def by (rule CEV_axiom_from_singleton_imp[OF ht both])
qed

theorem gi_PC_sentence_theorem:
  assumes stock: "gi_finite_PC_axioms \<subseteq> T" and mn: "m \<le> n"
    and ctx: "\<And>i. i < n - m \<Longrightarrow> lookup \<Gamma> i = Some \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gi_PC_sentence \<sigma> n m"
  using mn ctx
proof (induction m arbitrary: \<Gamma>)
  case 0
  show ?case by (simp only: gi_PC_sentence.simps; rule gi_PC_matrix_theorem[OF stock]) (simp add: "0.prems")
next
  case (Suc m)
  note outer_le = Suc.prems(1) and outer_ctx = Suc.prems(2)
  have inner_ctx: "\<And>i. i < n - m \<Longrightarrow> lookup (\<sigma> # \<Gamma>) i = Some \<sigma>"
  proof -
    fix i assume lt: "i < n - m"
    show "lookup (\<sigma> # \<Gamma>) i = Some \<sigma>"
    proof (cases i)
      case 0 then show ?thesis by (simp add: lookup_def)
    next
      case (Suc j)
      have "j < n - Suc m" using lt Suc by simp
      then have "lookup \<Gamma> j = Some \<sigma>" by (rule outer_ctx)
      then show ?thesis by (simp add: Suc gi_PC_lookup_Suc)
    qed
  qed
  have body: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ gi_PC_sentence \<sigma> n m"
    by (rule Suc.IH[OF _ inner_ctx]) (use outer_le in simp)
  have bt: "\<sigma> # \<Gamma> \<turnstile> gi_PC_sentence \<sigma> n m : Prop" by (rule CEV_axiom_proves_formula[OF body])
  show ?case by (simp only: gi_PC_sentence.simps; rule CEV_axiom_generalize_theorem[OF bt body])
qed

theorem gi_CEV_finite_PC:
  assumes stock: "gi_finite_PC_axioms \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ gi_finite_PC \<sigma> n"
  unfolding gi_finite_PC_def by (rule gi_PC_sentence_theorem[OF stock order_refl]) simp

corollary gi_CEV_finite_PC_exact_stock:
  "[] ; gi_finite_PC_axioms \<turnstile>\<^sub>CEV\<^sup>+ gi_finite_PC \<sigma> n"
  by (rule gi_CEV_finite_PC[OF subset_refl])

corollary gi_CEV_finite_PC_empty:
  "[] ; gi_finite_PC_axioms \<turnstile>\<^sub>CEV\<^sup>+ gi_finite_PC \<sigma> 0"
  by (rule gi_CEV_finite_PC_exact_stock)

lemma gi_finite_PC_typed: "[] \<turnstile> gi_finite_PC \<sigma> n : Prop"
  by (rule CEV_axiom_proves_formula[OF gi_CEV_finite_PC_exact_stock])

lemma gi_finite_PC_axioms_closed:
  "A \<in> gi_finite_PC_axioms \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding gi_finite_PC_axioms_def
  by (auto intro: pp_purity_schema_typed pp_application_closure_schema_typed)

section \<open>The independently written native family and its literal correspondence\<close>

text \<open>
  The native formulas are written directly in the named language on an
  explicit chart ns: parameter aᵢ₊₁ is NVar (ns ! i) and the bound variable
  of the selector is the fresh name for σ on the chart. Falsity is the
  source representative ¬⊤₀ and the empty hypothesis is ⊤₀, both taken on
  the chart as in the T1 transfer. The selector occurring under the
  membership binder is the same λ-term with its parameter indices moved
  past that binder (offset 2), exactly as the constructor formula has it.
\<close>

fun gb_PC_disj :: "sgcontext \<Rightarrow> otype \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> gb_term" where
  "gb_PC_disj G \<sigma> d ns 0 = book_not G (gi_old_top G ns)"
| "gb_PC_disj G \<sigma> d ns (Suc n) =
    book_or G (book_leibniz G \<sigma> (NVar (ns ! 0)) (NVar (ns ! (n + d)))) (gb_PC_disj G \<sigma> d ns n)"

definition gb_PC_selector where
  "gb_PC_selector G \<sigma> ns n =
    (let x = named_chart_fresh G ns \<sigma> in NLam x (gb_PC_disj G \<sigma> 1 (x # ns) n))"

definition gb_PC_shifted_selector where
  "gb_PC_shifted_selector G \<sigma> ns n =
    (let x = named_chart_fresh G ns \<sigma> in NLam x (gb_PC_disj G \<sigma> 2 (x # ns) n))"

fun gb_PC_hyp :: "sgcontext \<Rightarrow> otype \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> gb_term" where
  "gb_PC_hyp G \<sigma> ns 0 = gi_old_top G ns"
| "gb_PC_hyp G \<sigma> ns (Suc n) = book_and G (gb_pure \<sigma> (NVar (ns ! n))) (gb_PC_hyp G \<sigma> ns n)"

definition gb_PC_membership where
  "gb_PC_membership G \<sigma> ns n =
    (let x = named_chart_fresh G ns \<sigma>
     in book_all G x (gb_T6_iff G (NApp (gb_PC_shifted_selector G \<sigma> (x # ns) n) (NVar x))
       (gb_PC_disj G \<sigma> 1 (x # ns) n)))"

definition gb_PC_matrix where
  "gb_PC_matrix G \<sigma> ns n = book_imp (gb_PC_hyp G \<sigma> ns n)
    (book_and G (gb_pure (Arr \<sigma> Prop) (gb_PC_selector G \<sigma> ns n)) (gb_PC_membership G \<sigma> ns n))"

fun gb_PC_sentence :: "sgcontext \<Rightarrow> otype \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gb_term" where
  "gb_PC_sentence G \<sigma> ns n 0 = gb_PC_matrix G \<sigma> ns n"
| "gb_PC_sentence G \<sigma> ns n (Suc m) =
    (let a = named_chart_fresh G ns \<sigma> in book_all G a (gb_PC_sentence G \<sigma> (a # ns) n m))"

definition gb_finite_PC where
  "gb_finite_PC G \<sigma> n = gb_PC_sentence G \<sigma> [] n n"

definition gb_finite_PC_axioms where
  "gb_finite_PC_axioms G = gb_purity_schema G \<union> gb_application_schema G"

lemma gi_PC_disj_translation:
  "gi_to_book G ns k (gi_PC_disj \<sigma> n) = gb_PC_disj G \<sigma> 1 ns n"
  by (induction n) (simp_all add: ObjFalse_def gi_true_translation)

lemma gi_PC_disj_shift_translation:
  "gi_to_book G ns k (rename (lift_ren Suc) (gi_PC_disj \<sigma> n)) = gb_PC_disj G \<sigma> 2 ns n"
  by (induction n) (simp_all add: ObjFalse_def ObjTrue_def gi_old_top_def Let_def)

lemma gi_PC_selector_translation:
  "gi_to_book G ns k (gi_PC_selector \<sigma> n) = gb_PC_selector G \<sigma> ns n"
  by (simp add: gi_PC_selector_def gb_PC_selector_def gi_PC_disj_translation Let_def)

lemma gi_PC_shifted_selector_translation:
  "gi_to_book G ns k (shift (gi_PC_selector \<sigma> n)) = gb_PC_shifted_selector G \<sigma> ns n"
  by (simp add: gi_PC_selector_def gb_PC_shifted_selector_def shift_def
    gi_PC_disj_shift_translation Let_def)

lemma gi_PC_hyp_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G ns k (gi_PC_hyp \<sigma> n) = gb_PC_hyp G \<sigma> ns n"
  by (induction n) (simp_all add: gi_true_translation gi_pure_translation)

lemma gi_PC_membership_translation:
  "gi_to_book G ns k (gi_PC_membership \<sigma> n) = gb_PC_membership G \<sigma> ns n"
  by (simp add: gi_PC_membership_def gb_PC_membership_def gb_T6_iff_def
    gi_PC_shifted_selector_translation gi_PC_disj_translation Let_def)

lemma gi_PC_matrix_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G ns k (gi_PC_matrix \<sigma> n) = gb_PC_matrix G \<sigma> ns n"
  by (simp add: gi_PC_matrix_def gb_PC_matrix_def gi_PC_hyp_translation gi_pure_translation
    gi_PC_selector_translation gi_PC_membership_translation)

lemma gi_PC_sentence_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G ns k (gi_PC_sentence \<sigma> n m) = gb_PC_sentence G \<sigma> ns n m"
  by (induction m arbitrary: ns) (simp_all add: gi_PC_matrix_translation Let_def)

theorem gi_finite_PC_native_translation:
  "gi_goodman_names k \<Longrightarrow> gi_to_book G [] k (gi_finite_PC \<sigma> n) = gb_finite_PC G \<sigma> n"
  by (simp add: gi_finite_PC_def gb_finite_PC_def gi_PC_sentence_translation)

subsection \<open>Declared-signature admissibility of the constructor sentence\<close>

lemma gi_PC_disj_admitted:
  "gi_constants_admitted k \<Sigma> (gi_PC_disj \<sigma> n)"
  by (induction n) (simp_all add: ObjFalse_def ObjTrue_def)

lemma gi_PC_hyp_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature (gi_PC_hyp \<sigma> n)"
  by (induction n) (simp_all add: ObjTrue_def pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def)

lemma gi_PC_matrix_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature (gi_PC_matrix \<sigma> n)"
  by (simp add: gi_PC_matrix_def gi_PC_membership_def gi_PC_selector_def gi_PC_hyp_admitted
    gi_PC_disj_admitted pp_pure_def pp_Pure_def gi_goodman_names_def gb_signature_def
    shift_def gi_constants_rename)

lemma gi_PC_sentence_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature (gi_PC_sentence \<sigma> n m)"
  by (induction m) (simp_all add: gi_PC_matrix_admitted)

lemma gi_finite_PC_admitted:
  "gi_goodman_names k \<Longrightarrow> gi_constants_admitted k gb_signature (gi_finite_PC \<sigma> n)"
  by (simp add: gi_finite_PC_def gi_PC_sentence_admitted)

subsection \<open>The native stock: logical purity and application closure only\<close>

lemma gb_finite_PC_axioms_language:
  "sg_rich G \<Longrightarrow> A \<in> gb_finite_PC_axioms G \<Longrightarrow> book_theory_formula gb_signature G A"
  unfolding gb_finite_PC_axioms_def gb_application_schema_def
  by (auto intro: gb_purity_schema_language gb_application_closure_language)

lemma gb_finite_PC_axioms_closed:
  "A \<in> gb_finite_PC_axioms G \<Longrightarrow> named_fv A = {}"
  unfolding gb_finite_PC_axioms_def gb_application_schema_def
  by (auto simp: gb_purity_schema_closed gb_basic_axioms_closed)

lemma gb_finite_PC_axioms_subset_T1:
  "gb_finite_PC_axioms G \<subseteq> gb_T1_axioms G"
  unfolding gb_finite_PC_axioms_def gb_T1_axioms_def by blast

theorem gi_finite_PC_stock_inclusion:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "image (gi_to_book G [] k) gi_finite_PC_axioms \<subseteq> gb_finite_PC_axioms G"
  unfolding gi_finite_PC_axioms_def gb_finite_PC_axioms_def image_Un
  using gi_purity_schema_inclusion[OF rich names] gi_application_schema_equality[OF names, of G]
  by blast

lemma gi_finite_PC_axiom_from_native:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and member: "A \<in> gi_finite_PC_axioms"
  shows "goodman_book_proves (\<lambda>_. UNIV) G (gb_finite_PC_axioms G) (gi_to_book G [] k A)"
proof -
  have native: "gi_to_book G [] k A \<in> gb_finite_PC_axioms G"
    using gi_finite_PC_stock_inclusion[OF rich names] member by blast
  have language: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G [] k A)"
    by (rule gi_gb_universal_language[OF gb_finite_PC_axioms_language[OF rich native]])
  show ?thesis by (rule goodman_book_proves.Axiom[OF native language])
qed

theorem gi_finite_PC_native_preservation:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and derivation: "\<Gamma> ; gi_finite_PC_axioms \<turnstile>\<^sub>CEV\<^sup>+ A"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted k gb_signature A"
  shows "goodman_book_proves gb_signature G (gb_finite_PC_axioms G) (gi_to_book G ns k A)"
proof -
  have universal: "goodman_book_proves (\<lambda>_. UNIV) G (gb_finite_PC_axioms G) (gi_to_book G ns k A)"
    by (rule gi_native_package_preservation[OF rich derivation gi_finite_PC_axioms_closed
      gi_finite_PC_axiom_from_native[OF rich names] chart distinct])
  show ?thesis by (rule gi_native_conclusion_restrict[OF rich derivation chart admitted
    universal gb_finite_PC_axioms_language[OF rich]])
qed

subsection \<open>The native endpoints\<close>

theorem gi_native_finite_PC:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_finite_PC_axioms G) (gb_finite_PC G \<sigma> n)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have translated: "goodman_book_proves gb_signature G (gb_finite_PC_axioms G)
      (gi_to_book G [] k (gi_finite_PC \<sigma> n))"
    by (rule gi_finite_PC_native_preservation[OF rich names gi_CEV_finite_PC_exact_stock _ _
      gi_finite_PC_admitted[OF names]]; simp)
  show ?thesis using translated by (simp only: gi_finite_PC_native_translation[OF names])
qed

corollary gi_native_finite_PC_empty:
  "sg_rich G \<Longrightarrow> goodman_book_proves gb_signature G (gb_finite_PC_axioms G) (gb_finite_PC G \<sigma> 0)"
  by (rule gi_native_finite_PC)

corollary gi_native_finite_PC_T1_stock:
  "sg_rich G \<Longrightarrow> goodman_book_proves gb_signature G (gb_T1_axioms G) (gb_finite_PC G \<sigma> n)"
  by (rule goodman_book_mono[OF gi_native_finite_PC gb_finite_PC_axioms_subset_T1])

lemma gi_PC_empty_selector_purity_admitted:
  "gi_goodman_names k \<Longrightarrow>
    gi_constants_admitted k gb_signature (pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (gi_PC_selector \<sigma> 0))"
  by (simp add: gi_PC_selector_def ObjFalse_def ObjTrue_def pp_pure_def pp_Pure_def
    gi_goodman_names_def gb_signature_def)

theorem gi_native_empty_selector_pure:
  assumes rich: "sg_rich G"
  shows "goodman_book_proves gb_signature G (gb_finite_PC_axioms G)
    (gb_pure (Arr \<sigma> Prop) (gb_PC_selector G \<sigma> [] 0))"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have original: "[] ; gi_finite_PC_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (gi_PC_selector \<sigma> 0)"
    using gi_PC_empty_selector_pure[OF subset_refl, where \<Gamma>="[]" and S="{}"]
    by (simp only: CEV_axiom_from_empty_iff)
  have translated: "goodman_book_proves gb_signature G (gb_finite_PC_axioms G)
      (gi_to_book G [] k (pp_pure (\<sigma> \<rightarrow>\<^sub>o Prop) (gi_PC_selector \<sigma> 0)))"
    by (rule gi_finite_PC_native_preservation[OF rich names original _ _
      gi_PC_empty_selector_purity_admitted[OF names]]; simp)
  show ?thesis using translated
    by (simp only: gi_pure_translation[OF names] gi_PC_selector_translation)
qed

lemma gb_finite_PC_language_closed:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_finite_PC G \<sigma> n)"
    and "named_fv (gb_finite_PC G \<sigma> n) = {}"
  using gi_native_T6_extra_language_closed[where G=G and M="gi_finite_PC \<sigma> n" and B="gb_finite_PC G \<sigma> n",
    OF rich gi_finite_PC_typed gi_finite_PC_admitted gi_finite_PC_native_translation] by blast+

text \<open>
  gb_finite_PC G σ n is a closed formula of the declared Pure/Fun signature,
  derivable in C⁺ from the native logical-purity and application-closure
  schemas alone, for every type σ and every finite length n; n = 0 is the
  empty selector λx.¬⊤₀. This is finite pure comprehension for the listed
  parameters. It does not establish PC for infinite pluralities or
  comprehension for arbitrary, potentially infinite external subsets of
  a pure stock. In particular, it does not establish the external full PC
  used by T9.
\<close>

text \<open>
  gi_finite_PC σ n is the closed sentence
  ∀aₙ…∀a₁. (Pure(a₁) ∧ … ∧ Pure(aₙ) ∧ ⊤₀) → (Pure(λx.(x = aₙ ∨ … ∨ x = a₁ ∨ ⊥₀)) ∧
  ∀x.((λx.…) x ↔ (x = aₙ ∨ … ∨ x = a₁ ∨ ⊥₀))),
  proved from the logical-purity and application-closure schemas alone,
  for every type σ and every n, with n = 0 giving the empty selector λx.⊥₀.
  The proof is an explicit induction on n in the constructor calculus.
\<close>

end
