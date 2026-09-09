theory Bacon_Beta
  imports Bacon_Substitution
begin

section \<open>Beta contraction\<close>

text \<open>
  The relation \<open>(Lam \<sigma> M) $ N \<rightarrow>\<^sub>\<beta> subst0 N M\<close>, written in standard
  notation as \<open>(\<lambda>x\<^sub>\<sigma>. M) N \<rightarrow>\<^sub>\<beta> M[N/x]\<close>, is one root contraction.
  This file proves subject reduction for that step.  It does not assert
  normalization or confluence.  Contraction inside arbitrary formula contexts
  enters H in \<open>Bacon_Deduction\<close>; the typed reflexive, symmetric, transitive
  beta-eta relation is introduced later in \<open>Bacon_Conversion\<close>.
\<close>

inductive beta_contract :: "oterm \<Rightarrow> oterm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>\<beta>" 50) where
  beta[intro]: "App (Lam \<sigma> M) N \<rightarrow>\<^sub>\<beta> subst0 N M"

lemma beta_contract_preserves_typing:
  assumes "M \<rightarrow>\<^sub>\<beta> N"
    and "\<Gamma> \<turnstile> M : \<tau>"
  shows "\<Gamma> \<turnstile> N : \<tau>"
  using assms
proof cases
  case (beta \<sigma> P Q)
  then obtain \<rho> where
    "\<Gamma> \<turnstile> Lam \<sigma> P : \<rho> \<rightarrow>\<^sub>o \<tau>" and "\<Gamma> \<turnstile> Q : \<rho>"
    using assms(2) by (auto elim: has_type.cases)
  then have "\<rho> = \<sigma>" and "\<sigma> # \<Gamma> \<turnstile> P : \<tau>"
    by (auto elim: has_type.cases dest: typing_unique)
  with \<open>\<Gamma> \<turnstile> Q : \<rho>\<close> show ?thesis
    using beta by (auto intro: subst0_preserves_typing)
qed

lemma typed_beta_example:
  assumes "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> \<turnstile> subst0 N (Var 0) : \<sigma>"
  using assms by (auto intro: subst0_preserves_typing)

end
