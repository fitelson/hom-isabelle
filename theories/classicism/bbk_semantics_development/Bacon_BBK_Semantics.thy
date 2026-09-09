theory Bacon_BBK_Semantics
  imports Bacon_Classicism.Bacon_Conversion
begin

section \<open>BBK semantics for the represented language\<close>

text \<open>
  𝔐 = (D, ⟦·⟧, v), with Dσ ≠ ∅ and 𝔐,g ⊨ M =σ N ⇔ ⟦M⟧g = ⟦N⟧g. Bacon–Dorr,
  Definition 3.1, pp. 43–44.

  Isabelle representation: The locale fixes whole-term interpretation and valuation
  for the full type system F and typed-string signatures. It does not impose full
  function spaces or identify propositions by their truth values. Injective de Bruijn
  renaming coherence is an explicit encoding condition, not a printed extra BBK axiom.

  Status: Conditional semantic interface; no model is constructed here. Correspondence
  with named variables and first-class logical constants remains a separate
  translation.
\<close>

type_synonym bbk_signature = "otype \<Rightarrow> string set"

fun bbk_in_signature :: "bbk_signature \<Rightarrow> oterm \<Rightarrow> bool" where
  "bbk_in_signature \<Sigma> (Var n) = True"
| "bbk_in_signature \<Sigma> (Const c \<sigma>) = (c \<in> \<Sigma> \<sigma>)"
| "bbk_in_signature \<Sigma> (App M N) =
    (bbk_in_signature \<Sigma> M \<and> bbk_in_signature \<Sigma> N)"
| "bbk_in_signature \<Sigma> (Lam \<sigma> M) = bbk_in_signature \<Sigma> M"
| "bbk_in_signature \<Sigma> (Eq \<sigma> M N) =
    (bbk_in_signature \<Sigma> M \<and> bbk_in_signature \<Sigma> N)"
| "bbk_in_signature \<Sigma> (Neg A) = bbk_in_signature \<Sigma> A"
| "bbk_in_signature \<Sigma> (Conj A B) =
    (bbk_in_signature \<Sigma> A \<and> bbk_in_signature \<Sigma> B)"
| "bbk_in_signature \<Sigma> (Disj A B) =
    (bbk_in_signature \<Sigma> A \<and> bbk_in_signature \<Sigma> B)"
| "bbk_in_signature \<Sigma> (Imp A B) =
    (bbk_in_signature \<Sigma> A \<and> bbk_in_signature \<Sigma> B)"
| "bbk_in_signature \<Sigma> (Forall \<sigma> A) = bbk_in_signature \<Sigma> A"
| "bbk_in_signature \<Sigma> (Exists \<sigma> A) = bbk_in_signature \<Sigma> A"

lemma bbk_in_signature_mono:
  assumes "bbk_in_signature \<Sigma> M" and "\<And>\<sigma>. \<Sigma> \<sigma> \<subseteq> \<Sigma>' \<sigma>"
  shows "bbk_in_signature \<Sigma>' M"
  using assms by (induction M) auto

lemma bbk_in_universal_signature[simp]:
  "bbk_in_signature (\<lambda>_. UNIV) M"
  by (induction M) auto

text \<open>
  Free variables are de Bruijn slots.  Entering a binder removes slot zero
  and lowers the remaining slots.  Assignments are total HOL functions, but
  only their values at the finitely many context slots are constrained.
  Undefined off-context values have no semantic significance.
\<close>

fun bbk_fv :: "oterm \<Rightarrow> nat set" where
  "bbk_fv (Var n) = {n}"
| "bbk_fv (Const c \<sigma>) = {}"
| "bbk_fv (App M N) = bbk_fv M \<union> bbk_fv N"
| "bbk_fv (Lam \<sigma> M) = {n. Suc n \<in> bbk_fv M}"
| "bbk_fv (Eq \<sigma> M N) = bbk_fv M \<union> bbk_fv N"
| "bbk_fv (Neg A) = bbk_fv A"
| "bbk_fv (Conj A B) = bbk_fv A \<union> bbk_fv B"
| "bbk_fv (Disj A B) = bbk_fv A \<union> bbk_fv B"
| "bbk_fv (Imp A B) = bbk_fv A \<union> bbk_fv B"
| "bbk_fv (Forall \<sigma> A) = {n. Suc n \<in> bbk_fv A}"
| "bbk_fv (Exists \<sigma> A) = {n. Suc n \<in> bbk_fv A}"

definition bbk_env_typed ::
    "(otype \<Rightarrow> 'v set) \<Rightarrow> ctx \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> bool" where
  "bbk_env_typed D \<Gamma> g \<longleftrightarrow>
    (\<forall>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<longrightarrow> g n \<in> D \<sigma>)"

definition bbk_extend :: "'v \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> nat \<Rightarrow> 'v" where
  "bbk_extend a g = case_nat a g"

lemma bbk_extend_zero[simp]: "bbk_extend a g 0 = a"
  by (simp add: bbk_extend_def)

lemma bbk_extend_Suc[simp]: "bbk_extend a g (Suc n) = g n"
  by (simp add: bbk_extend_def)

lemma bbk_env_empty[simp]: "bbk_env_typed D [] g"
  by (simp add: bbk_env_typed_def lookup_def)

lemma bbk_env_lookup:
  assumes "bbk_env_typed D \<Gamma> g" and "lookup \<Gamma> n = Some \<sigma>"
  shows "g n \<in> D \<sigma>"
  using assms unfolding bbk_env_typed_def by blast

lemma bbk_env_extend:
  assumes "bbk_env_typed D \<Gamma> g" and "a \<in> D \<sigma>"
  shows "bbk_env_typed D (\<sigma> # \<Gamma>) (bbk_extend a g)"
proof (unfold bbk_env_typed_def, intro allI impI)
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "bbk_extend a g n \<in> D \<tau>"
  proof (cases n)
    case 0
    have "\<tau> = \<sigma>"
      using lookup by (simp add: 0)
    then show ?thesis
      using assms(2) by (simp add: 0)
  next
    case (Suc m)
    have old_lookup: "lookup \<Gamma> m = Some \<tau>"
      using lookup by (simp add: Suc)
    have "g m \<in> D \<tau>"
      using assms(1) old_lookup by (rule bbk_env_lookup)
    then show ?thesis
      by (simp add: Suc)
  qed
qed

lemma bbk_env_tail:
  assumes "bbk_env_typed D (\<sigma> # \<Gamma>) g"
  shows "bbk_env_typed D \<Gamma> (\<lambda>n. g (Suc n))"
  using assms unfolding bbk_env_typed_def by fastforce

lemma bbk_env_exists:
  assumes "\<And>\<sigma>. D \<sigma> \<noteq> {}"
  shows "\<exists>g. bbk_env_typed D \<Gamma> g"
proof (induction \<Gamma>)
  case Nil
  then show ?case by simp
next
  case (Cons \<sigma> \<Gamma>)
  obtain g where g: "bbk_env_typed D \<Gamma> g"
    using Cons.IH by blast
  obtain a where a: "a \<in> D \<sigma>"
    using assms by blast
  show ?case
    using bbk_env_extend[OF g a] by blast
qed

section \<open>The model interface\<close>

text \<open>
  ⟦x⟧g = g(x); ⟦M⟧g depends only on g↾FV(M); M ≡βη N ⇒ ⟦M⟧g = ⟦N⟧g. Bacon–Dorr,
  Definition 3.1, pp. 43–44.

  Isabelle representation: The fields below spell out typing, application congruence,
  locality, conversion, and logical truth clauses. denote_rename additionally records
  the de Bruijn encoding coherence.

  Status: Model assumptions are explicit; subsequent theorems are relative to them.
\<close>

locale bbk_model =
  fixes signature :: bbk_signature
    and domain :: "otype \<Rightarrow> 'v set"
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> oterm \<Rightarrow> 'v"
    and valuation :: "'v \<Rightarrow> bool"
  assumes domain_nonempty: "domain \<sigma> \<noteq> {}"
    and denote_type:
      "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> bbk_in_signature signature M \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow> denote g M \<in> domain \<sigma>"
    and denote_var:
      "lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       denote g (Var n) = g n"
    and denote_application_cong:
      "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau> \<Longrightarrow> \<Gamma> \<turnstile> A : \<sigma> \<Longrightarrow>
       \<Delta> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o \<tau> \<Longrightarrow> \<Delta> \<turnstile> B : \<sigma> \<Longrightarrow>
       bbk_in_signature signature (App F A) \<Longrightarrow>
       bbk_in_signature signature (App G B) \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow> bbk_env_typed domain \<Delta> h \<Longrightarrow>
       denote g F = denote h G \<Longrightarrow> denote g A = denote h B \<Longrightarrow>
       denote g (App F A) = denote h (App G B)"
    and denote_locality:
      "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> \<Delta> \<turnstile> M : \<sigma> \<Longrightarrow>
       bbk_in_signature signature M \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow> bbk_env_typed domain \<Delta> h \<Longrightarrow>
       (\<And>n. n \<in> bbk_fv M \<Longrightarrow> g n = h n) \<Longrightarrow>
       denote g M = denote h M"
    and denote_rename:
      "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> bbk_in_signature signature M \<Longrightarrow>
       inj r \<Longrightarrow> bbk_env_typed domain \<Delta> g \<Longrightarrow>
       (\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow>
         lookup \<Delta> (r n) = Some \<tau>) \<Longrightarrow>
       denote g (rename r M) = denote (\<lambda>n. g (r n)) M"
    and denote_beta_eta:
      "beta_eta_equiv \<Gamma> \<sigma> M N \<Longrightarrow>
       bbk_in_signature signature M \<Longrightarrow> bbk_in_signature signature N \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow> denote g M = denote g N"
    and valuation_neg:
      "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> bbk_in_signature signature A \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Neg A)) = (\<not> valuation (denote g A))"
    and valuation_conj:
      "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
       bbk_in_signature signature A \<Longrightarrow> bbk_in_signature signature B \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Conj A B)) =
         (valuation (denote g A) \<and> valuation (denote g B))"
    and valuation_disj:
      "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
       bbk_in_signature signature A \<Longrightarrow> bbk_in_signature signature B \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Disj A B)) =
         (valuation (denote g A) \<or> valuation (denote g B))"
    and valuation_imp:
      "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
       bbk_in_signature signature A \<Longrightarrow> bbk_in_signature signature B \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Imp A B)) =
         (valuation (denote g A) \<longrightarrow> valuation (denote g B))"
    and valuation_forall:
      "\<sigma> # \<Gamma> \<turnstile> A : Prop \<Longrightarrow> bbk_in_signature signature A \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Forall \<sigma> A)) =
         (\<forall>a \<in> domain \<sigma>. valuation (denote (bbk_extend a g) A))"
    and valuation_exists:
      "\<sigma> # \<Gamma> \<turnstile> A : Prop \<Longrightarrow> bbk_in_signature signature A \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Exists \<sigma> A)) =
         (\<exists>a \<in> domain \<sigma>. valuation (denote (bbk_extend a g) A))"
    and valuation_identity:
      "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> N : \<sigma> \<Longrightarrow>
       bbk_in_signature signature M \<Longrightarrow> bbk_in_signature signature N \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Eq \<sigma> M N)) = (denote g M = denote g N)"
begin

text \<open>
  Clause correspondence: domain_nonempty is (i); denote_type is the typing
  requirement in (ii); denote_var, denote_application_cong, denote_locality,
  and denote_beta_eta are (ii.a--d).  The valuation clauses are (iii.a--f),
  with a separate material-implication clause for our primitive Imp syntax.
  These constrain truth values, not the identities of proposition denotations.
  The additional denote_rename field records the de Bruijn encoding
  coherence explained above; it is not a separately printed clause of
  Definition 3.1.
\<close>

definition bbk_satisfies :: "(nat \<Rightarrow> 'v) \<Rightarrow> oterm \<Rightarrow> bool" where
  "bbk_satisfies g A \<longleftrightarrow> valuation (denote g A)"

definition bbk_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "bbk_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and> bbk_in_signature signature A \<and>
    (\<forall>g. bbk_env_typed domain \<Gamma> g \<longrightarrow> bbk_satisfies g A)"

lemma typed_environment_exists:
  "\<exists>g. bbk_env_typed domain \<Gamma> g"
  by (rule bbk_env_exists[OF domain_nonempty])

lemma closed_denotation_independent:
  assumes "\<Gamma> \<turnstile> M : \<sigma>" and "\<Delta> \<turnstile> M : \<sigma>"
    and "bbk_in_signature signature M"
    and "bbk_env_typed domain \<Gamma> g" and "bbk_env_typed domain \<Delta> h"
    and "bbk_fv M = {}"
  shows "denote g M = denote h M"
  using assms by (intro denote_locality) auto

lemma constant_denotation_independent:
  assumes "c \<in> signature \<sigma>"
    and "bbk_env_typed domain \<Gamma> g" and "bbk_env_typed domain \<Delta> h"
  shows "denote g (Const c \<sigma>) = denote h (Const c \<sigma>)"
  using assms by (intro closed_denotation_independent) auto

lemma valid_formula:
  assumes "bbk_valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms unfolding bbk_valid_in_context_def by blast

lemma valid_satisfies:
  assumes "bbk_valid_in_context \<Gamma> A" and "bbk_env_typed domain \<Gamma> g"
  shows "bbk_satisfies g A"
  using assms unfolding bbk_valid_in_context_def by blast

lemma identity_satisfied_iff:
  assumes "\<Gamma> \<turnstile> M : \<sigma>" and "\<Gamma> \<turnstile> N : \<sigma>"
    and "bbk_in_signature signature M" and "bbk_in_signature signature N"
    and "bbk_env_typed domain \<Gamma> g"
  shows "bbk_satisfies g (Eq \<sigma> M N) \<longleftrightarrow> denote g M = denote g N"
  unfolding bbk_satisfies_def using assms by (rule valuation_identity)

lemma reflexivity_valid:
  assumes "\<Gamma> \<turnstile> M : \<sigma>" and "bbk_in_signature signature M"
  shows "bbk_valid_in_context \<Gamma> (Eq \<sigma> M M)"
  using assms identity_satisfied_iff
  unfolding bbk_valid_in_context_def by auto

lemma modus_ponens_valid:
  assumes "bbk_valid_in_context \<Gamma> A"
    and "bbk_valid_in_context \<Gamma> (Imp A B)"
  shows "bbk_valid_in_context \<Gamma> B"
proof -
  have A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and sig_A: "bbk_in_signature signature A"
    and sig_B: "bbk_in_signature signature B"
    using assms unfolding bbk_valid_in_context_def
    by (auto elim: has_type.cases)
  have truth: "bbk_satisfies g B" if env: "bbk_env_typed domain \<Gamma> g" for g
  proof -
    have "bbk_satisfies g A" and "bbk_satisfies g (Imp A B)"
      using assms env by (auto intro: valid_satisfies)
    then show ?thesis
      unfolding bbk_satisfies_def
      using valuation_imp[OF A B sig_A sig_B env] by blast
  qed
  show ?thesis
    unfolding bbk_valid_in_context_def using B sig_B truth by blast
qed

text \<open>
  The following soundness files prove the propositional, identity, conversion,
  and quantifier cases, then assemble the complete H induction.  This file
  introduces the semantic interface and elementary consequences only.
  No soundness, model-existence, or completeness theorem is assumed as a
  locale field.
\<close>

end

end
