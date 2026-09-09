theory Bacon_Deduction
  imports Bacon_Beta
begin

section \<open>The minimal higher-order logic H\<close>

text \<open>
  This theory gives a Hilbert-style derivability system for Bacon's minimal
  classical higher-order logic H.  The judgment \<open>\<Gamma> \<turnstile>\<^sub>H A\<close> says that the
  object-language formula \<open>A\<close> is a theorem of H in type context \<open>\<Gamma>\<close>.

  The rules are arranged to mirror the Bacon-Dorr axiomatization of H:
  propositional classical logic, universal instantiation, existential
  generalization, typed reflexivity, Leibniz's law, beta/eta conversion in
  formula contexts, modus ponens, and the Hilbert-Ackermann generalization and
  instantiation rules.

  Three judgments must be kept separate:

  \<^item> \<open>\<Gamma> \<turnstile> A : Prop\<close> says that \<open>A\<close> is a well-formed formula;
  \<^item> \<open>\<Gamma> \<turnstile>\<^sub>H A\<close> says that \<open>A\<close> is an H theorem; and
  \<^item> \<open>\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A\<close> is finite local derivability from the
    formula list \<open>\<Delta>\<close> using assumptions, H theorems, and modus ponens.

  Thus \<open>\<Gamma>\<close> is always a typing context, not a set of formula assumptions.
  The local relation is proof-engineering infrastructure rather than Bacon's
  notion of an H-theory, which is itself closed under all theorem rules.

  The source's Figure 2 has the PC, UI, EG, Ref, LL, beta, eta, MP, Gen, and
  Inst principles represented below.  \<open>IndividualExistence\<close> adds
  \<open>\<exists>x\<^sub>e. x =\<^sub>e x\<close>: Bacon and Dorr explain that this restores H when
  working in the named-variable-free presentation analogous to the present
  context-indexed calculus.  It is a rule of the represented object calculus,
  not an additional axiom of Isabelle/HOL.
\<close>

subsection \<open>Propositional tautologies\<close>

text \<open>
  Truth-functional tautologies are evaluated over the displayed propositional
  connectives.  Non-truth-functional formulas, such as equations, quantified
  formulas, and applications of propositional terms, are treated as atomic by
  the valuation.
\<close>

fun prop_eval :: "(oterm \<Rightarrow> bool) \<Rightarrow> oterm \<Rightarrow> bool" where
  "prop_eval v (Var n) = v (Var n)"
| "prop_eval v (Const c \<sigma>) = v (Const c \<sigma>)"
| "prop_eval v (App M N) = v (App M N)"
| "prop_eval v (Lam \<sigma> M) = v (Lam \<sigma> M)"
| "prop_eval v (Eq \<sigma> M N) = v (Eq \<sigma> M N)"
| "prop_eval v (Neg A) = (\<not> prop_eval v A)"
| "prop_eval v (Conj A B) = (prop_eval v A \<and> prop_eval v B)"
| "prop_eval v (Disj A B) = (prop_eval v A \<or> prop_eval v B)"
| "prop_eval v (Imp A B) = (prop_eval v A \<longrightarrow> prop_eval v B)"
| "prop_eval v (Forall \<sigma> A) = v (Forall \<sigma> A)"
| "prop_eval v (Exists \<sigma> A) = v (Exists \<sigma> A)"

definition prop_tautology :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "prop_tautology \<Gamma> A \<longleftrightarrow> \<Gamma> \<turnstile> A : Prop \<and> (\<forall>v. prop_eval v A)"

lemma prop_tautology_imp_self:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "prop_tautology \<Gamma> (Imp A A)"
  unfolding prop_tautology_def
  using assms by auto

subsection \<open>Conversion inside formula contexts\<close>

inductive compatible_step :: "(oterm \<Rightarrow> oterm \<Rightarrow> bool) \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> bool"
  for R :: "oterm \<Rightarrow> oterm \<Rightarrow> bool" where
  root[intro]: "R M N \<Longrightarrow> compatible_step R M N"
| App_left[intro]: "compatible_step R M M' \<Longrightarrow>
    compatible_step R (App M N) (App M' N)"
| App_right[intro]: "compatible_step R N N' \<Longrightarrow>
    compatible_step R (App M N) (App M N')"
| Lam_body[intro]: "compatible_step R M M' \<Longrightarrow>
    compatible_step R (Lam \<sigma> M) (Lam \<sigma> M')"
| Eq_left[intro]: "compatible_step R M M' \<Longrightarrow>
    compatible_step R (Eq \<sigma> M N) (Eq \<sigma> M' N)"
| Eq_right[intro]: "compatible_step R N N' \<Longrightarrow>
    compatible_step R (Eq \<sigma> M N) (Eq \<sigma> M N')"
| Neg_body[intro]: "compatible_step R A A' \<Longrightarrow>
    compatible_step R (Neg A) (Neg A')"
| Conj_left[intro]: "compatible_step R A A' \<Longrightarrow>
    compatible_step R (Conj A B) (Conj A' B)"
| Conj_right[intro]: "compatible_step R B B' \<Longrightarrow>
    compatible_step R (Conj A B) (Conj A B')"
| Disj_left[intro]: "compatible_step R A A' \<Longrightarrow>
    compatible_step R (Disj A B) (Disj A' B)"
| Disj_right[intro]: "compatible_step R B B' \<Longrightarrow>
    compatible_step R (Disj A B) (Disj A B')"
| Imp_left[intro]: "compatible_step R A A' \<Longrightarrow>
    compatible_step R (Imp A B) (Imp A' B)"
| Imp_right[intro]: "compatible_step R B B' \<Longrightarrow>
    compatible_step R (Imp A B) (Imp A B')"
| Forall_body[intro]: "compatible_step R A A' \<Longrightarrow>
    compatible_step R (Forall \<sigma> A) (Forall \<sigma> A')"
| Exists_body[intro]: "compatible_step R A A' \<Longrightarrow>
    compatible_step R (Exists \<sigma> A) (Exists \<sigma> A')"

inductive eta_contract :: "oterm \<Rightarrow> oterm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>\<eta>" 50) where
  eta[intro]: "Lam \<sigma> (App (shift F) (Var 0)) \<rightarrow>\<^sub>\<eta> F"

subsection \<open>H theoremhood\<close>

inductive H_proves :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" ("_ \<turnstile>\<^sub>H _" [50, 50] 50) where
  PC[intro]: "prop_tautology \<Gamma> A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>H A"
| IndividualExistence[intro]:
    "\<Gamma> \<turnstile>\<^sub>H Exists Ind (Eq Ind (Var 0) (Var 0))"
| UI[intro]: "\<sigma> # \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> T : \<sigma> \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>H Imp (Forall \<sigma> A) (subst0 T A)"
| EG[intro]: "\<sigma> # \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> T : \<sigma> \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>H Imp (subst0 T A) (Exists \<sigma> A)"
| Ref[intro]: "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>H Eq \<sigma> M M"
| LL[intro]: "\<Gamma> \<turnstile> A : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> B : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>H Imp (Eq \<sigma> A B) (Imp (App F A) (App F B))"
| Beta[intro]: "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
    compatible_step beta_contract A B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
| Eta[intro]: "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
    compatible_step eta_contract A B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
| MP[intro]: "\<Gamma> \<turnstile>\<^sub>H A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>H Imp A B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>H B"
| Gen[intro]: "\<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    \<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp (shift P) Q \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>H Imp P (Forall \<sigma> Q)"
| Inst[intro]: "\<sigma> # \<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    \<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp P (shift Q) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>H Imp (Exists \<sigma> P) Q"

lemma H_imp_self:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp A A"
  using assms by (intro H_proves.PC prop_tautology_imp_self)

lemma H_proves_formula:
  assumes "\<Gamma> \<turnstile>\<^sub>H A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: H_proves.induct)
  case (PC \<Gamma> A)
  then show ?case
    by (simp add: prop_tautology_def)
next
  case (IndividualExistence \<Gamma>)
  show ?case
    by (rule has_type.Exists, rule has_type.Eq; simp)
next
  case (UI \<sigma> \<Gamma> A T)
  then have "\<Gamma> \<turnstile> subst0 T A : Prop"
    by (auto intro: subst0_preserves_typing)
  moreover have "\<Gamma> \<turnstile> Forall \<sigma> A : Prop"
    using UI.hyps by auto
  ultimately show ?case
    by auto
next
  case (EG \<sigma> \<Gamma> A T)
  then have "\<Gamma> \<turnstile> subst0 T A : Prop"
    by (auto intro: subst0_preserves_typing)
  moreover have "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using EG.hyps by auto
  ultimately show ?case
    by auto
next
  case (Ref \<Gamma> M \<sigma>)
  then show ?case
    by auto
next
  case (LL \<Gamma> A \<sigma> B F)
  then show ?case
    by auto
next
  case (Beta \<Gamma> A B)
  then show ?case
    by auto
next
  case (Eta \<Gamma> A B)
  then show ?case
    by auto
next
  case (MP \<Gamma> A B)
  then show ?case
    by (auto elim: has_type.cases)
next
  case (Gen \<Gamma> P \<sigma> Q)
  then show ?case
    by auto
next
  case (Inst \<sigma> \<Gamma> P Q)
  then show ?case
    by auto
qed

subsection \<open>Derivability from local assumptions\<close>

inductive H_derivable :: "ctx \<Rightarrow> oterm list \<Rightarrow> oterm \<Rightarrow> bool"
    ("_ ; _ \<turnstile>\<^sub>H _" [50, 50, 50] 50) where
  Assumption[intro]: "A \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
| Theorem[intro]: "\<Gamma> \<turnstile>\<^sub>H A \<Longrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
| Derive_MP[intro]: "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A \<Longrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H Imp A B \<Longrightarrow> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H B"

lemma H_derivable_formula:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: H_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  then show ?case
    by simp
next
  case (Theorem \<Gamma> A \<Delta>)
  then show ?case
    by (rule H_proves_formula)
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  then show ?case
    by (auto elim: has_type.cases)
qed

end
