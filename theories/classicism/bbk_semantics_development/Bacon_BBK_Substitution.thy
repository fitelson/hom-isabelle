theory Bacon_BBK_Substitution
  imports Bacon_BBK_Semantics
begin

section \<open>First semantic renaming and substitution lemmas\<close>

text \<open>
  ⟦M[s]⟧g = ⟦M⟧h, where h(x) = ⟦s(x)⟧g; ⟦M[r]⟧g = ⟦M⟧g∘r. Bacon–Dorr, Definition 3.1,
  pp. 43–44.

  Isabelle representation: The proved substitution and renaming laws in this file
  concern the variable/constant/application fragment. The environment and direct β
  lemmas prepare the later binder argument.

  Status: Fragment and structural results only; full simultaneous substitution is not
  asserted here.
\<close>

fun bbk_applicative_term :: "oterm \<Rightarrow> bool" where
  "bbk_applicative_term (Var n) = True"
| "bbk_applicative_term (Const c \<sigma>) = True"
| "bbk_applicative_term (App F A) =
    (bbk_applicative_term F \<and> bbk_applicative_term A)"
| "bbk_applicative_term M = False"

lemma bbk_signature_rename:
  "bbk_in_signature \<Sigma> (rename r M) = bbk_in_signature \<Sigma> M"
  by (induction M arbitrary: r) auto

lemma bbk_signature_subst_applicative:
  assumes "bbk_applicative_term M" and "bbk_in_signature \<Sigma> M"
    and "\<And>n. bbk_in_signature \<Sigma> (s n)"
  shows "bbk_in_signature \<Sigma> (subst s M)"
  using assms by (induction M) auto

lemma bbk_env_rename:
  assumes env: "bbk_env_typed D \<Delta> g"
    and ren: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      lookup \<Delta> (r n) = Some \<sigma>"
  shows "bbk_env_typed D \<Gamma> (\<lambda>n. g (r n))"
proof (unfold bbk_env_typed_def, intro allI impI)
  fix n \<sigma>
  assume "lookup \<Gamma> n = Some \<sigma>"
  then have "lookup \<Delta> (r n) = Some \<sigma>" by (rule ren)
  with env show "g (r n) \<in> D \<sigma>" by (rule bbk_env_lookup)
qed

context bbk_model
begin

lemma bbk_env_subst:
  assumes env: "bbk_env_typed domain \<Delta> g"
    and typed: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      \<Delta> \<turnstile> s n : \<sigma>"
    and sig: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      bbk_in_signature signature (s n)"
  shows "bbk_env_typed domain \<Gamma> (\<lambda>n. denote g (s n))"
proof (unfold bbk_env_typed_def, intro allI impI)
  fix n \<sigma>
  assume look: "lookup \<Gamma> n = Some \<sigma>"
  show "denote g (s n) \<in> domain \<sigma>"
    using typed[OF look] sig[OF look] env by (rule denote_type)
qed

lemma bbk_denote_rename_applicative:
  assumes fragment: "bbk_applicative_term M"
    and typed: "\<Gamma> \<turnstile> M : \<tau>"
    and sig: "bbk_in_signature signature M"
    and env: "bbk_env_typed domain \<Delta> g"
    and ren: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      lookup \<Delta> (r n) = Some \<sigma>"
  shows "denote g (rename r M) = denote (\<lambda>n. g (r n)) M"
  using fragment typed sig env ren
proof (induction M arbitrary: \<Gamma> \<Delta> \<tau> r g)
  case (Var n)
  have look: "lookup \<Gamma> n = Some \<tau>"
    using Var.prems(2) by simp
  have target: "lookup \<Delta> (r n) = Some \<tau>"
    using Var.prems(5)[OF look] .
  have pulled: "bbk_env_typed domain \<Gamma> (\<lambda>n. g (r n))"
    using Var.prems(4,5) by (rule bbk_env_rename)
  have left: "denote g (Var (r n)) = g (r n)"
    using target Var.prems(4) by (rule denote_var)
  have right: "denote (\<lambda>n. g (r n)) (Var n) = g (r n)"
    using look pulled by (rule denote_var)
  show ?case using left right by simp
next
  case (Const c \<sigma>)
  have name: "c \<in> signature \<sigma>" using Const.prems(3) by simp
  have pulled: "bbk_env_typed domain \<Gamma> (\<lambda>n. g (r n))"
    using Const.prems(4,5) by (rule bbk_env_rename)
  have "denote g (Const c \<sigma>) =
      denote (\<lambda>n. g (r n)) (Const c \<sigma>)"
    using name Const.prems(4) pulled by (rule constant_denotation_independent)
  then show ?case by simp
next
  case (App F A)
  obtain \<sigma> where F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and A: "\<Gamma> \<turnstile> A : \<sigma>"
    using App.prems(2) by (auto elim: has_type.cases)
  have fragF: "bbk_applicative_term F" and fragA: "bbk_applicative_term A"
    using App.prems(1) by auto
  have sigF: "bbk_in_signature signature F" and sigA: "bbk_in_signature signature A"
    using App.prems(3) by auto
  have eqF: "denote g (rename r F) = denote (\<lambda>n. g (r n)) F"
    using App.IH(1)[OF fragF F sigF App.prems(4,5)] .
  have eqA: "denote g (rename r A) = denote (\<lambda>n. g (r n)) A"
    using App.IH(2)[OF fragA A sigA App.prems(4,5)] .
  have rF: "\<Delta> \<turnstile> rename r F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using F App.prems(5) by (rule renaming_preserves_typing)
  have rA: "\<Delta> \<turnstile> rename r A : \<sigma>"
    using A App.prems(5) by (rule renaming_preserves_typing)
  have sig_left: "bbk_in_signature signature (App (rename r F) (rename r A))"
    using sigF sigA by (simp add: bbk_signature_rename)
  have pulled: "bbk_env_typed domain \<Gamma> (\<lambda>n. g (r n))"
    using App.prems(4,5) by (rule bbk_env_rename)
  have "denote g (App (rename r F) (rename r A)) =
      denote (\<lambda>n. g (r n)) (App F A)"
    using rF rA F A sig_left App.prems(3) App.prems(4) pulled eqF eqA
    by (rule denote_application_cong)
  then show ?case by simp
qed auto

lemma bbk_denote_subst_applicative:
  assumes fragment: "bbk_applicative_term M"
    and typed: "\<Gamma> \<turnstile> M : \<tau>"
    and sig: "bbk_in_signature signature M"
    and env: "bbk_env_typed domain \<Delta> g"
    and sub: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      \<Delta> \<turnstile> s n : \<sigma>"
    and sig_sub: "\<And>n. bbk_in_signature signature (s n)"
  shows "denote g (subst s M) = denote (\<lambda>n. denote g (s n)) M"
  using fragment typed sig env sub sig_sub
proof (induction M arbitrary: \<Gamma> \<Delta> \<tau> s g)
  case (Var n)
  have look: "lookup \<Gamma> n = Some \<tau>" using Var.prems(2) by simp
  have pulled: "bbk_env_typed domain \<Gamma> (\<lambda>n. denote g (s n))"
    using Var.prems(4,5,6) by (intro bbk_env_subst) auto
  have "denote (\<lambda>n. denote g (s n)) (Var n) = denote g (s n)"
    using look pulled by (rule denote_var)
  then show ?case by simp
next
  case (Const c \<sigma>)
  have name: "c \<in> signature \<sigma>" using Const.prems(3) by simp
  have pulled: "bbk_env_typed domain \<Gamma> (\<lambda>n. denote g (s n))"
    using Const.prems(4,5,6) by (intro bbk_env_subst) auto
  have "denote g (Const c \<sigma>) =
      denote (\<lambda>n. denote g (s n)) (Const c \<sigma>)"
    using name Const.prems(4) pulled by (rule constant_denotation_independent)
  then show ?case by simp
next
  case (App F A)
  obtain \<sigma> where F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and A: "\<Gamma> \<turnstile> A : \<sigma>"
    using App.prems(2) by (auto elim: has_type.cases)
  have fragF: "bbk_applicative_term F" and fragA: "bbk_applicative_term A"
    using App.prems(1) by auto
  have sigF: "bbk_in_signature signature F" and sigA: "bbk_in_signature signature A"
    using App.prems(3) by auto
  have eqF: "denote g (subst s F) = denote (\<lambda>n. denote g (s n)) F"
    using App.IH(1)[OF fragF F sigF App.prems(4,5,6)] .
  have eqA: "denote g (subst s A) = denote (\<lambda>n. denote g (s n)) A"
    using App.IH(2)[OF fragA A sigA App.prems(4,5,6)] .
  have sF: "\<Delta> \<turnstile> subst s F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using F App.prems(5) by (rule substitution_preserves_typing)
  have sA: "\<Delta> \<turnstile> subst s A : \<sigma>"
    using A App.prems(5) by (rule substitution_preserves_typing)
  have sig_left: "bbk_in_signature signature (App (subst s F) (subst s A))"
    using bbk_signature_subst_applicative[OF fragF sigF App.prems(6)]
      bbk_signature_subst_applicative[OF fragA sigA App.prems(6)] by simp
  have pulled: "bbk_env_typed domain \<Gamma> (\<lambda>n. denote g (s n))"
    using App.prems(4,5,6) by (intro bbk_env_subst) auto
  have "denote g (App (subst s F) (subst s A)) =
      denote (\<lambda>n. denote g (s n)) (App F A)"
    using sF sA F A sig_left App.prems(3) App.prems(4) pulled eqF eqA
    by (rule denote_application_cong)
  then show ?case by simp
qed auto

lemma bbk_denote_beta:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> M : \<tau>"
    and arg: "\<Gamma> \<turnstile> N : \<sigma>"
    and sig_redex: "bbk_in_signature signature (App (Lam \<sigma> M) N)"
    and sig_contract: "bbk_in_signature signature (subst0 N M)"
    and env: "bbk_env_typed domain \<Gamma> g"
  shows "denote g (App (Lam \<sigma> M) N) = denote g (subst0 N M)"
proof -
  have redex: "\<Gamma> \<turnstile> App (Lam \<sigma> M) N : \<tau>"
    using body arg by auto
  have contract: "\<Gamma> \<turnstile> subst0 N M : \<tau>"
    using body arg by (rule subst0_preserves_typing)
  have step: "compatible_step beta_contract (App (Lam \<sigma> M) N) (subst0 N M)"
    by (intro compatible_step.root beta_contract.beta)
  have equiv: "beta_eta_equiv \<Gamma> \<tau> (App (Lam \<sigma> M) N) (subst0 N M)"
    using redex contract step by (rule beta_eta_equiv.Beta)
  show ?thesis
    using equiv sig_redex sig_contract env by (rule denote_beta_eta)
qed

end

section \<open>The exact vector-environment target\<close>

text \<open>
  ⟦(λxₙ … x₀. M) Nₙ … N₀⟧h = ⟦M⟧g when ⟦Nᵢ⟧h = g(xᵢ). Bacon–Dorr, Theorem 3.2, p. 45
  n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: bbk_close_context abstracts slot zero first, so the
  argument list is reversed. bbk_vector_environment_property names the exact
  all-context target.

  Status: An obligation predicate, not an axiom or completed theorem; the
  empty-context case is proved.
\<close>

fun bbk_close_context :: "ctx \<Rightarrow> oterm \<Rightarrow> oterm" where
  "bbk_close_context [] M = M"
| "bbk_close_context (\<sigma> # \<Gamma>) M = bbk_close_context \<Gamma> (Lam \<sigma> M)"

text \<open>
  Closing a context abstracts slot zero first.  Thus for context [sigma,tau]
  the closed term is Lam tau (Lam sigma M), and its arguments are supplied
  in reverse context order.  The property below states the precise semantic
  target needed for the full-language proof: evaluation of that closed
  abstraction on representatives of an assignment reproduces the evaluation
  of M on the assignment.

  This is a definition of an outstanding obligation, not an axiom, locale
  assumption, or proved theorem.  A proof from (ii.a--d) must use finite
  abstraction/application and βη invariance, without identifying
  functions merely because they agree on all arguments.  Together with the
  matching vector β-reduction theorem it would yield full simultaneous
  substitution; the applicative-fragment theorem above does not claim that.
\<close>

context bbk_model
begin

definition bbk_vector_environment_property :: bool where
  "bbk_vector_environment_property \<longleftrightarrow>
    (\<forall>\<Gamma> \<Delta> M \<tau> g h Ns.
      \<Gamma> \<turnstile> M : \<tau> \<longrightarrow> bbk_in_signature signature M \<longrightarrow>
      bbk_env_typed domain \<Gamma> g \<longrightarrow> bbk_env_typed domain \<Delta> h \<longrightarrow>
      length Ns = length \<Gamma> \<longrightarrow>
      (\<forall>n < length \<Gamma>.
        \<Delta> \<turnstile> Ns ! n : \<Gamma> ! n \<and>
        bbk_in_signature signature (Ns ! n) \<and>
        denote h (Ns ! n) = g n) \<longrightarrow>
      denote h (app_vec (bbk_close_context \<Gamma> M) (rev Ns)) = denote g M)"

lemma bbk_vector_environment_empty:
  assumes "[] \<turnstile> M : \<tau>" and "bbk_in_signature signature M"
    and "bbk_fv M = {}"
    and "bbk_env_typed domain [] g" and "bbk_env_typed domain \<Delta> h"
    and "\<Delta> \<turnstile> M : \<tau>"
  shows "denote h (app_vec (bbk_close_context [] M) []) = denote g M"
proof -
  have "denote h M = denote g M"
    using assms(6,1,2,5,4,3) by (rule closed_denotation_independent)
  then show ?thesis by simp
qed

end

end
