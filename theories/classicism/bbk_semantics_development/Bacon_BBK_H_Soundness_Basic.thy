theory Bacon_BBK_H_Soundness_Basic
  imports Bacon_BBK_Substitution
begin

section \<open>The first H-soundness clauses for BBK models\<close>

text \<open>
  Γ ⊢ₕ A ⇒ 𝔐,g ⊨ A: first check PC, Ref, LL, MP, β, η, and ∃xₑ(x =ₑ x). Bacon–Dorr,
  Figure 2; Theorem 3.2, pp. 44–45.

  Isabelle representation: The PC bridge applies prop_eval to semantic truth values.
  Primitive logical atoms may still have distinct denotations with the same truth
  value.

  Status: Rule-level soundness ingredients; the quantifier rules and complete
  induction are in the next theory.
\<close>

context bbk_model
begin

lemma bbk_validI:
  assumes typed: "\<Gamma> \<turnstile> A : Prop"
    and sig: "bbk_in_signature signature A"
    and truth: "\<And>g. bbk_env_typed domain \<Gamma> g \<Longrightarrow>
      valuation (denote g A)"
  shows "bbk_valid_in_context \<Gamma> A"
  unfolding bbk_valid_in_context_def bbk_satisfies_def
  using typed sig truth by blast

subsection \<open>The propositional evaluation bridge\<close>

text \<open>
  v(⟦A⟧g) = evalPC(v ∘ ⟦·⟧g, A). Bacon–Dorr, Figure 2; Theorem 3.2, pp. 44–45.

  Isabelle representation: The existing prop_eval function treats equations,
  applications, and quantified formulas as atoms while evaluating the displayed
  Boolean constructors.

  Status: The bridge proves PC soundness with typing and signature guards; it makes no
  identity claim about propositions.
\<close>

lemma bbk_prop_eval:
  assumes typed: "\<Gamma> \<turnstile> A : Prop"
    and sig: "bbk_in_signature signature A"
    and env: "bbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g A) =
    prop_eval (\<lambda>B. valuation (denote g B)) A"
  using typed sig
proof (induction A)
  case (Var n)
  show ?case by (simp only: prop_eval.simps)
next
  case (Const c \<sigma>)
  show ?case by (simp only: prop_eval.simps)
next
  case (App F A)
  show ?case by (simp only: prop_eval.simps)
next
  case (Lam \<sigma> M)
  show ?case by (simp only: prop_eval.simps)
next
  case (Eq \<sigma> M N)
  show ?case by (simp only: prop_eval.simps)
next
  case (Neg A)
  have A: "\<Gamma> \<turnstile> A : Prop"
    using Neg.prems(1) by (cases rule: has_type.cases) assumption
  have sigA: "bbk_in_signature signature A"
    using Neg.prems(2) by simp
  have bridge: "valuation (denote g A) =
      prop_eval (\<lambda>B. valuation (denote g B)) A"
    using Neg.IH[OF A sigA] .
  show ?case
    using valuation_neg[OF A sigA env] bridge
    by (simp only: prop_eval.simps)
next
  case (Conj A B)
  have A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    using Conj.prems(1) by (auto elim: has_type.cases)
  have sigA: "bbk_in_signature signature A" and sigB: "bbk_in_signature signature B"
    using Conj.prems(2) by simp_all
  show ?case
    using valuation_conj[OF A B sigA sigB env]
      Conj.IH(1)[OF A sigA] Conj.IH(2)[OF B sigB]
    by (simp only: prop_eval.simps)
next
  case (Disj A B)
  have A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    using Disj.prems(1) by (auto elim: has_type.cases)
  have sigA: "bbk_in_signature signature A" and sigB: "bbk_in_signature signature B"
    using Disj.prems(2) by simp_all
  show ?case
    using valuation_disj[OF A B sigA sigB env]
      Disj.IH(1)[OF A sigA] Disj.IH(2)[OF B sigB]
    by (simp only: prop_eval.simps)
next
  case (Imp A B)
  have A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    using Imp.prems(1) by (auto elim: has_type.cases)
  have sigA: "bbk_in_signature signature A" and sigB: "bbk_in_signature signature B"
    using Imp.prems(2) by simp_all
  show ?case
    using valuation_imp[OF A B sigA sigB env]
      Imp.IH(1)[OF A sigA] Imp.IH(2)[OF B sigB]
    by (simp only: prop_eval.simps)
next
  case (Forall \<sigma> A)
  show ?case by (simp only: prop_eval.simps)
next
  case (Exists \<sigma> A)
  show ?case by (simp only: prop_eval.simps)
qed

lemma bbk_PC_valid:
  assumes taut: "prop_tautology \<Gamma> A"
    and sig: "bbk_in_signature signature A"
  shows "bbk_valid_in_context \<Gamma> A"
proof -
  have typed: "\<Gamma> \<turnstile> A : Prop"
    using taut unfolding prop_tautology_def by blast
  have truth: "valuation (denote g A)" if env: "bbk_env_typed domain \<Gamma> g" for g
  proof -
    have "prop_eval (\<lambda>B. valuation (denote g B)) A"
      using taut unfolding prop_tautology_def by blast
    then show ?thesis using bbk_prop_eval[OF typed sig env] by blast
  qed
  show ?thesis using typed sig truth by (rule bbk_validI)
qed

lemma bbk_iff_valuation:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and sigA: "bbk_in_signature signature A"
    and sigB: "bbk_in_signature signature B"
    and env: "bbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (A \<longleftrightarrow>\<^sub>o B)) =
    (valuation (denote g A) = valuation (denote g B))"
proof -
  have typed: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    by (intro has_type.Conj has_type.Imp A B)
  have sig: "bbk_in_signature signature (A \<longleftrightarrow>\<^sub>o B)"
    using sigA sigB by simp
  note bridge = bbk_prop_eval[OF typed sig env]
  show ?thesis
    using bridge bbk_prop_eval[OF A sigA env] bbk_prop_eval[OF B sigB env]
    by (simp only: prop_eval.simps; blast)
qed

subsection \<open>Identity and local inference\<close>

text \<open>
  a = b ⇒ (Fa ⇒ Fb), and A, A ⇒ B ⊢ B. Bacon–Dorr, Figure 2; Theorem 3.2, pp. 44–45.

  Isabelle representation: Actual denotational equality and application congruence
  validate LL; the corresponding local lemmas also handle Ref and MP.

  Status: No pointwise function-extensionality assumption is used.
\<close>

lemma bbk_Ref_valid:
  assumes "\<Gamma> \<turnstile> M : \<sigma>" and "bbk_in_signature signature M"
  shows "bbk_valid_in_context \<Gamma> (Eq \<sigma> M M)"
  using assms by (rule reflexivity_valid)

lemma bbk_LL_valid:
  assumes A: "\<Gamma> \<turnstile> A : \<sigma>" and B: "\<Gamma> \<turnstile> B : \<sigma>"
    and F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
    and sigA: "bbk_in_signature signature A"
    and sigB: "bbk_in_signature signature B"
    and sigF: "bbk_in_signature signature F"
  shows "bbk_valid_in_context \<Gamma>
    (Imp (Eq \<sigma> A B) (Imp (App F A) (App F B)))"
proof -
  let ?E = "Eq \<sigma> A B"
  let ?P = "App F A"
  let ?Q = "App F B"
  have E: "\<Gamma> \<turnstile> ?E : Prop" by (rule has_type.Eq[OF A B])
  have P: "\<Gamma> \<turnstile> ?P : Prop" by (rule has_type.App[OF F A])
  have Q: "\<Gamma> \<turnstile> ?Q : Prop" by (rule has_type.App[OF F B])
  have PQ: "\<Gamma> \<turnstile> Imp ?P ?Q : Prop" by (rule has_type.Imp[OF P Q])
  have typed: "\<Gamma> \<turnstile> Imp ?E (Imp ?P ?Q) : Prop"
    by (rule has_type.Imp[OF E PQ])
  have sigE: "bbk_in_signature signature ?E"
    and sigP: "bbk_in_signature signature ?P"
    and sigQ: "bbk_in_signature signature ?Q"
    using sigA sigB sigF by simp_all
  have sigPQ: "bbk_in_signature signature (Imp ?P ?Q)"
    using sigP sigQ by simp
  have sig: "bbk_in_signature signature (Imp ?E (Imp ?P ?Q))"
    using sigE sigPQ by simp
  have truth: "valuation (denote g (Imp ?E (Imp ?P ?Q)))"
    if env: "bbk_env_typed domain \<Gamma> g" for g
  proof -
    have implication: "valuation (denote g ?E) \<longrightarrow>
        (valuation (denote g ?P) \<longrightarrow> valuation (denote g ?Q))"
    proof (intro impI)
      assume eq_true: "valuation (denote g ?E)"
        and p_true: "valuation (denote g ?P)"
      have same: "denote g A = denote g B"
        using eq_true valuation_identity[OF A B sigA sigB env] by blast
      have same_app: "denote g ?P = denote g ?Q"
        using F A F B sigP sigQ env env refl same
        by (rule denote_application_cong)
      show "valuation (denote g ?Q)" using p_true same_app by simp
    qed
    show ?thesis
      using implication valuation_imp[OF E PQ sigE sigPQ env]
        valuation_imp[OF P Q sigP sigQ env] by blast
  qed
  show ?thesis using typed sig truth by (rule bbk_validI)
qed

lemma bbk_MP_valid:
  assumes "bbk_valid_in_context \<Gamma> A"
    and "bbk_valid_in_context \<Gamma> (Imp A B)"
  shows "bbk_valid_in_context \<Gamma> B"
  using assms by (rule modus_ponens_valid)

subsection \<open>Conversion uses denotational equality, not extensionality\<close>

text \<open>
  A ≡βη B ⇒ 𝔐,g ⊨ A ↔ B. Bacon–Dorr, Definition 3.1, pp. 43–44.

  Isabelle representation: The typed beta_eta_equiv relation feeds the model's
  denotational conversion clause; the valuation bridge yields the object-language
  biconditional.

  Status: Both β and η rule instances are covered, with explicit language guards.
\<close>

lemma bbk_conversion_valid:
  assumes conv: "beta_eta_equiv \<Gamma> Prop A B"
    and sigA: "bbk_in_signature signature A"
    and sigB: "bbk_in_signature signature B"
  shows "bbk_valid_in_context \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have A: "\<Gamma> \<turnstile> A : Prop" by (rule beta_eta_equiv_left_type[OF conv])
  have B: "\<Gamma> \<turnstile> B : Prop" by (rule beta_eta_equiv_right_type[OF conv])
  have typed: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    by (intro has_type.Conj has_type.Imp A B)
  have sig: "bbk_in_signature signature (A \<longleftrightarrow>\<^sub>o B)"
    using sigA sigB by simp
  have truth: "valuation (denote g (A \<longleftrightarrow>\<^sub>o B))"
    if env: "bbk_env_typed domain \<Gamma> g" for g
  proof -
    have "denote g A = denote g B"
      using conv sigA sigB env by (rule denote_beta_eta)
    then show ?thesis
      using bbk_iff_valuation[OF A B sigA sigB env] by simp
  qed
  show ?thesis using typed sig truth by (rule bbk_validI)
qed

lemma bbk_Beta_valid:
  assumes "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step beta_contract A B"
    and "bbk_in_signature signature A" and "bbk_in_signature signature B"
  shows "bbk_valid_in_context \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have "beta_eta_equiv \<Gamma> Prop A B"
    using assms(1,2,3) by (rule beta_eta_equiv.Beta)
  then show ?thesis using assms(4,5) by (rule bbk_conversion_valid)
qed

lemma bbk_Eta_valid:
  assumes "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step eta_contract A B"
    and "bbk_in_signature signature A" and "bbk_in_signature signature B"
  shows "bbk_valid_in_context \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have "beta_eta_equiv \<Gamma> Prop A B"
    using assms(1,2,3) by (rule beta_eta_equiv.Eta)
  then show ?thesis using assms(4,5) by (rule bbk_conversion_valid)
qed

subsection \<open>Individual Existence\<close>

text \<open>
  𝔐,g ⊨ ∃xₑ(x =ₑ x). Bacon–Dorr, Figure 2; Theorem 3.2, pp. 44–45.

  Isabelle representation: domain_nonempty supplies an individual; bbk_extend makes it
  the bound variable's value, and the identity clause establishes reflexivity.

  Status: Nonemptiness discharges this represented H instance; no named witness is
  required.
\<close>

lemma bbk_IndividualExistence_valid:
  "bbk_valid_in_context \<Gamma> (Exists Ind (Eq Ind (Var 0) (Var 0)))"
proof -
  let ?A = "Eq Ind (Var 0) (Var 0)"
  have x: "Ind # \<Gamma> \<turnstile> Var 0 : Ind" by simp
  have A: "Ind # \<Gamma> \<turnstile> ?A : Prop" by (rule has_type.Eq[OF x x])
  have typed: "\<Gamma> \<turnstile> Exists Ind ?A : Prop" by (rule has_type.Exists[OF A])
  have sigA: "bbk_in_signature signature ?A" by simp
  have sig: "bbk_in_signature signature (Exists Ind ?A)" by simp
  have truth: "valuation (denote g (Exists Ind ?A))"
    if env: "bbk_env_typed domain \<Gamma> g" for g
  proof -
    obtain a where a: "a \<in> domain Ind" using domain_nonempty by blast
    have extended: "bbk_env_typed domain (Ind # \<Gamma>) (bbk_extend a g)"
      using env a by (rule bbk_env_extend)
    have sigx: "bbk_in_signature signature (Var 0)" by simp
    have refl: "valuation (denote (bbk_extend a g) ?A)"
      using valuation_identity[OF x x sigx sigx extended] by simp
    have "\<exists>a \<in> domain Ind. valuation (denote (bbk_extend a g) ?A)"
      using a refl by blast
    then show ?thesis using valuation_exists[OF A sigA env] by blast
  qed
  show ?thesis using typed sig truth by (rule bbk_validI)
qed

end

end
