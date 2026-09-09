theory Bacon_C_PC_Atomic_Evaluation
  imports Bacon_C_Boolean_Constants
begin

section \<open>Structural evaluation from identities for opaque atoms\<close>

text \<open>
  Let At(A) be the opaque atoms of the propositional skeleton of A.
  If each a ∈ At(A) satisfies ⊢C (λv.a) = (λv.ε(w(a))), then
  ⊢C (λv.A) = (λv.ε(⟦A⟧w)), where ε(True) = ⊤₀ and ε(False) = ⊥₀.
  Source use: the Boolean normalization obligation in Bacon--Dorr
  Appendix A.2(i), p.65.

  Isabelle representation.  C_PC_atoms follows exactly prop_eval:
  ¬, ∧, ∨, → are recursive; every other outer constructor is opaque.
  The Boolean evaluation ⟦A⟧w here is prop_eval w A, not a BBK denotation.
  C_boolean_constant represents ε.
  Status.  This is a C-only conditional evaluation theorem.  The atomic
  identities are substantial hypotheses, not consequences of a valuation.
\<close>

fun C_PC_atoms :: "oterm \<Rightarrow> oterm set" where
  "C_PC_atoms (Neg A) = C_PC_atoms A"
| "C_PC_atoms (Conj A B) = C_PC_atoms A \<union> C_PC_atoms B"
| "C_PC_atoms (Disj A B) = C_PC_atoms A \<union> C_PC_atoms B"
| "C_PC_atoms (Imp A B) = C_PC_atoms A \<union> C_PC_atoms B"
| "C_PC_atoms A = {A}"

lemma C_PC_atoms_finite:
  "finite (C_PC_atoms A)"
  by (induction A) simp_all

lemma C_PC_eval_atom_agreement:
  assumes agreement: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow> w a = u a"
  shows "prop_eval w A = prop_eval u A"
  using agreement by (induction A) auto

lemma C_PC_material_normalize_atoms:
  "C_PC_atoms (C_PC_material_normalize A) = C_PC_atoms A"
  by (induction A) simp_all

subsection \<open>Evaluation at each Boolean constructor\<close>

text \<open>
  The induction replaces the already normalized immediate subformulas
  inside their connective contexts, then applies the constant truth table.
  Isabelle representation.  The typing premise is retained at every
  recursive call; the atom set restricts the identity hypotheses precisely
  to the subformula currently being normalized.
  Status.  Quantified formulas and identity formulas are atomic cases,
  not recursive semantic evaluations of quantification or identity.
\<close>

theorem C_PC_evaluate_under_lambda:
  assumes typed: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and atoms: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow>
      \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
        (Lam \<sigma> a) (Lam \<sigma> (C_boolean_constant (w a)))"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> A) (Lam \<sigma> (C_boolean_constant (prop_eval w A)))"
  using typed atoms
proof (induction A)
  case (Neg A)
  have typed: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    using Neg.prems(1) by (auto elim: has_type.cases)
  have atoms: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> a) (Lam \<sigma> (C_boolean_constant (w a)))"
    using Neg.prems(2) by simp
  have IH: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> A) (Lam \<sigma> (C_boolean_constant (prop_eval w A)))"
    by (rule Neg.IH[OF typed atoms])
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Neg A)) (Lam \<sigma> (Neg (C_boolean_constant (prop_eval w A))))"
    by (rule C_boolean_lambda_neg_congruence[OF typed C_boolean_constant_type IH])
  show ?case using C_A1_trans[OF replacement C_boolean_lambda_neg_constant] by simp
next
  case (Conj A B)
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    using Conj.prems(1) by (auto elim: has_type.cases)
  have atoms_A: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> a) (Lam \<sigma> (C_boolean_constant (w a)))"
    by (rule Conj.prems(2)) simp
  have atoms_B: "\<And>a. a \<in> C_PC_atoms B \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> a) (Lam \<sigma> (C_boolean_constant (w a)))"
    by (rule Conj.prems(2)) simp
  have connective: "Conj = Conj \<or> Conj = Disj \<or> Conj = Imp" by simp
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A B))
    (Lam \<sigma> (Conj (C_boolean_constant (prop_eval w A)) (C_boolean_constant (prop_eval w B))))"
    by (rule C_PC_binary_lambda_congruence[OF connective A C_boolean_constant_type
      B C_boolean_constant_type Conj.IH(1)[OF A atoms_A] Conj.IH(2)[OF B atoms_B]])
  show ?case using C_A1_trans[OF replacement C_boolean_lambda_conj_constants] by simp
next
  case (Disj A B)
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    using Disj.prems(1) by (auto elim: has_type.cases)
  have atoms_A: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> a) (Lam \<sigma> (C_boolean_constant (w a)))"
    by (rule Disj.prems(2)) simp
  have atoms_B: "\<And>a. a \<in> C_PC_atoms B \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> a) (Lam \<sigma> (C_boolean_constant (w a)))"
    by (rule Disj.prems(2)) simp
  have connective: "Disj = Conj \<or> Disj = Disj \<or> Disj = Imp" by simp
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A B))
    (Lam \<sigma> (Disj (C_boolean_constant (prop_eval w A)) (C_boolean_constant (prop_eval w B))))"
    by (rule C_PC_binary_lambda_congruence[OF connective A C_boolean_constant_type
      B C_boolean_constant_type Disj.IH(1)[OF A atoms_A] Disj.IH(2)[OF B atoms_B]])
  show ?case using C_A1_trans[OF replacement C_boolean_lambda_disj_constants] by simp
next
  case (Imp A B)
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    using Imp.prems(1) by (auto elim: has_type.cases)
  have atoms_A: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> a) (Lam \<sigma> (C_boolean_constant (w a)))"
    by (rule Imp.prems(2)) simp
  have atoms_B: "\<And>a. a \<in> C_PC_atoms B \<Longrightarrow>
    \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> a) (Lam \<sigma> (C_boolean_constant (w a)))"
    by (rule Imp.prems(2)) simp
  have connective: "Imp = Conj \<or> Imp = Disj \<or> Imp = Imp" by simp
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Imp A B))
    (Lam \<sigma> (Imp (C_boolean_constant (prop_eval w A)) (C_boolean_constant (prop_eval w B))))"
    by (rule C_PC_binary_lambda_congruence[OF connective A C_boolean_constant_type
      B C_boolean_constant_type Imp.IH(1)[OF A atoms_A] Imp.IH(2)[OF B atoms_B]])
  show ?case using C_A1_trans[OF replacement C_boolean_lambda_imp_constants] by simp
next
  case (Var n)
  have member: "Var n \<in> C_PC_atoms (Var n)" by simp
  show ?case using Var.prems(2)[OF member] by simp
next
  case (Const c \<tau>)
  have member: "Const c \<tau> \<in> C_PC_atoms (Const c \<tau>)" by simp
  show ?case using Const.prems(2)[OF member] by simp
next
  case (App A B)
  have member: "App A B \<in> C_PC_atoms (App A B)" by simp
  show ?case using App.prems(2)[OF member] by simp
next
  case (Lam \<tau> A)
  have member: "Lam \<tau> A \<in> C_PC_atoms (Lam \<tau> A)" by simp
  show ?case using Lam.prems(2)[OF member] by simp
next
  case (Eq \<tau> A B)
  have member: "Eq \<tau> A B \<in> C_PC_atoms (Eq \<tau> A B)" by simp
  show ?case using Eq.prems(2)[OF member] by simp
next
  case (Forall \<tau> A)
  have member: "Forall \<tau> A \<in> C_PC_atoms (Forall \<tau> A)" by simp
  show ?case using Forall.prems(2)[OF member] by simp
next
  case (Exists \<tau> A)
  have member: "Exists \<tau> A \<in> C_PC_atoms (Exists \<tau> A)" by simp
  show ?case using Exists.prems(2)[OF member] by simp
qed

subsection \<open>The conditional tautology step and its boundary\<close>

corollary C_PC_tautology_under_atomic_identities:
  assumes tautology: "prop_tautology (\<sigma> # \<Gamma>) A"
    and atoms: "\<And>a. a \<in> C_PC_atoms A \<Longrightarrow>
      \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
        (Lam \<sigma> a) (Lam \<sigma> (C_boolean_constant (w a)))"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> ObjTrue)"
proof -
  have typed: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    using tautology by (simp add: prop_tautology_def)
  have truth: "prop_eval w A"
    using tautology unfolding prop_tautology_def by blast
  show ?thesis using C_PC_evaluate_under_lambda[OF typed atoms]
    by (simp add: truth C_boolean_constant_def)
qed

text \<open>
  For arbitrary A, a chosen valuation w does not supply identities
  (λv.a) = (λv.ε(w(a))).  In particular, v-dependent atoms need not
  be constant predicates.  The unconditional PC case therefore still
  requires a source-faithful Boolean equational argument which removes
  dependence on atomic values for tautologies.  The theorem above proves
  neither a two-valuedness principle for predicates nor that elimination
  step.  The subsequent abstraction-vector argument also remains separate.
\<close>

end
