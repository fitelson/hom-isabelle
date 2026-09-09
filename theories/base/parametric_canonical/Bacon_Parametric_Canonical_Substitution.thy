theory Bacon_Parametric_Canonical_Substitution
  imports Bacon_Parametric_Canonical_Substitution_Basics
begin

section \<open>Full representative independence without Functionality\<close>

text \<open>
  s(x) ∼ₜ r(x) for each x in Γ ⇒ M[s] ∼ₜ M[r].
  Source: Bacon–Dorr, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: induction is on the finite variable context,
  not the size or cardinality of the signature.  The successor step
  abstracts one variable, uses application congruence, and β-contracts.

  Status: conditional on pH_closed_Henkin.  No Functionality,
  pre-existing named witnesses, or existence of a Henkin theory is assumed.
\<close>

lemma pHcs_app_language:
  assumes f: "pterm_in_language \<Sigma> [] F (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and a: "pterm_in_language \<Sigma> [] A \<sigma>"
  shows "pterm_in_language \<Sigma> [] (PApp F A) \<tau>"
proof -
  have ft: "has_ptype [] F (\<sigma> \<rightarrow>\<^sub>o \<tau>)" using f unfolding pterm_in_language_def by (rule conjunct1)
  have fs: "pterm_in_signature \<Sigma> F" using f unfolding pterm_in_language_def by (rule conjunct2)
  have at: "has_ptype [] A \<sigma>" using a unfolding pterm_in_language_def by (rule conjunct1)
  have sa: "pterm_in_signature \<Sigma> A" using a unfolding pterm_in_language_def by (rule conjunct2)
  have typed: "has_ptype [] (PApp F A) \<tau>" by (rule has_ptype.PApp[OF ft at])
  have sig: "pterm_in_signature \<Sigma> (PApp F A)" using fs sa by simp
  show ?thesis unfolding pterm_in_language_def by (rule conjI[OF typed sig])
qed

context pH_closed_Henkin
begin

lemma pHcs_beta_identity:
  assumes lm: "pterm_in_language signature [] M \<tau>"
    and ln: "pterm_in_language signature [] N \<tau>"
    and step: "pcompatible_step pbeta_contract M N"
  shows "pH_term_eq \<tau> M N"
proof -
  have mt: "has_ptype [] M \<tau>" and ms: "pterm_in_signature signature M"
    using lm unfolding pterm_in_language_def by simp_all
  have nt: "has_ptype [] N \<tau>" and ns: "pterm_in_signature signature N"
    using ln unfolding pterm_in_language_def by simp_all
  have reflexive_type: "has_ptype [] (PEq \<tau> M M) Prop" by (rule has_ptype.PEq[OF mt mt])
  have identity_type: "has_ptype [] (PEq \<tau> M N) Prop" by (rule has_ptype.PEq[OF mt nt])
  have refsig: "pterm_in_signature signature (PEq \<tau> M M)" using ms by simp
  have idsig: "pterm_in_signature signature (PEq \<tau> M N)" using ms ns by simp
  have contextual: "pcompatible_step pbeta_contract (PEq \<tau> M M) (PEq \<tau> M N)"
    by (rule pcompatible_step.Eq_right[OF step])
  have proved: "pH_proves signature [] (PObjIff (PEq \<tau> M M) (PEq \<tau> M N))"
    by (rule pH_proves.Beta[OF reflexive_type identity_type contextual refsig idsig])
  have reference: "PEq \<tau> M M \<in> T" by (rule pH_term_eq_member[OF pH_term_eq_refl[OF lm]])
  have identity: "PEq \<tau> M N \<in> T"
    by (rule iffD1[OF pH_biconditional_membership[OF reflexive_type identity_type refsig idsig proved] reference])
  show ?thesis unfolding pH_term_eq_def by (intro conjI lm ln identity)
qed

lemma pHcs_substitution_beta:
  assumes typed: "has_ptype (\<sigma> # \<Gamma>) M \<tau>" and sig: "pterm_in_signature signature M"
    and sub: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      pterm_in_language signature [] (s n) \<rho>"
  shows "pH_term_eq \<tau>
    (PApp (psubst (\<lambda>n. s (Suc n)) (PLam \<sigma> M)) (s 0)) (psubst s M)"
proof -
  let ?tail = "\<lambda>n. s (Suc n)"
  have head: "pterm_in_language signature [] (s 0) \<sigma>" by (rule sub) simp
  have tail: "pterm_in_language signature [] (?tail n) \<rho>"
    if look: "lookup \<Gamma> n = Some \<rho>" for n \<rho>
    by (rule sub) (simp only: lookup_Cons_Suc look)
  have lam: "has_ptype \<Gamma> (PLam \<sigma> M) (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    by (rule has_ptype.PLam[OF typed])
  have ls: "pterm_in_signature signature (PLam \<sigma> M)" using sig by simp
  have function_lang: "pterm_in_language signature [] (psubst ?tail (PLam \<sigma> M)) (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    by (rule pHcs_subst_language[OF lam ls tail])
  have app_lang: "pterm_in_language signature []
      (PApp (psubst ?tail (PLam \<sigma> M)) (s 0)) \<tau>"
    by (rule pHcs_app_language[OF function_lang head])
  have result_lang: "pterm_in_language signature [] (psubst s M) \<tau>"
    by (rule pHcs_subst_language[OF typed sig sub])
  have root: "pcompatible_step pbeta_contract
      (PApp (PLam \<sigma> (psubst (plift_subst ?tail) M)) (s 0))
      (psubst0 (s 0) (psubst (plift_subst ?tail) M))"
    by (rule pcompatible_step.root[where R=pbeta_contract]; rule pbeta_contract.beta)
  have step: "pcompatible_step pbeta_contract
      (PApp (psubst ?tail (PLam \<sigma> M)) (s 0)) (psubst s M)"
    using root by (simp only: psubst.simps pHcs_head_tail)
  show ?thesis by (rule pHcs_beta_identity[OF app_lang result_lang step])
qed

theorem pHcs_substitution_congruence:
  assumes typed: "has_ptype \<Gamma> M \<tau>" and sig: "pterm_in_signature signature M"
    and agree: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> pH_term_eq \<rho> (s n) (r n)"
  shows "pH_term_eq \<tau> (psubst s M) (psubst r M)"
  using typed sig agree
proof (induction \<Gamma> arbitrary: M \<tau> s r)
  case Nil
  have lang: "pterm_in_language signature [] M \<tau>"
    unfolding pterm_in_language_def by (rule conjI[OF Nil.prems(1,2)])
  have ref: "pH_term_eq \<tau> M M" by (rule pH_term_eq_refl[OF lang])
  show ?case using ref by (simp only: pHcs_closed_subst[OF Nil.prems(1)])
next
  case (Cons \<sigma> \<Gamma>)
  let ?s = "\<lambda>n. s (Suc n)"
  let ?r = "\<lambda>n. r (Suc n)"
  have lam: "has_ptype \<Gamma> (PLam \<sigma> M) (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    by (rule has_ptype.PLam[OF Cons.prems(1)])
  have ls: "pterm_in_signature signature (PLam \<sigma> M)" using Cons.prems(2) by simp
  have tail_eq: "pH_term_eq \<rho> (?s n) (?r n)"
    if look: "lookup \<Gamma> n = Some \<rho>" for n \<rho>
    by (rule Cons.prems(3)) (simp only: lookup_Cons_Suc look)
  have function_eq: "pH_term_eq (\<sigma> \<rightarrow>\<^sub>o \<tau>)
      (psubst ?s (PLam \<sigma> M)) (psubst ?r (PLam \<sigma> M))"
    by (rule Cons.IH[OF lam ls tail_eq])
  have head_eq: "pH_term_eq \<sigma> (s 0) (r 0)" by (rule Cons.prems(3)) simp
  have app_eq: "pH_term_eq \<tau>
      (PApp (psubst ?s (PLam \<sigma> M)) (s 0)) (PApp (psubst ?r (PLam \<sigma> M)) (r 0))"
    by (rule pH_term_eq_app[OF function_eq head_eq])
  have sl: "pterm_in_language signature [] (s n) \<rho>"
    if look: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>" for n \<rho>
    by (rule pH_term_eq_left[OF Cons.prems(3)[OF look]])
  have rl: "pterm_in_language signature [] (r n) \<rho>"
    if look: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>" for n \<rho>
    by (rule pH_term_eq_right[OF Cons.prems(3)[OF look]])
  have left: "pH_term_eq \<tau> (PApp (psubst ?s (PLam \<sigma> M)) (s 0)) (psubst s M)"
    by (rule pHcs_substitution_beta[OF Cons.prems(1,2) sl])
  have right: "pH_term_eq \<tau> (PApp (psubst ?r (PLam \<sigma> M)) (r 0)) (psubst r M)"
    by (rule pHcs_substitution_beta[OF Cons.prems(1,2) rl])
  have first: "pH_term_eq \<tau> (psubst s M) (PApp (psubst ?r (PLam \<sigma> M)) (r 0))"
    by (rule pH_term_eq_trans[OF pH_term_eq_sym[OF left] app_eq])
  show ?case by (rule pH_term_eq_trans[OF first right])
qed

corollary pHcs_representative_independence:
  assumes typed: "has_ptype \<Gamma> M \<tau>" and sig: "pterm_in_signature signature M"
    and agree: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> pH_term_eq \<rho> (s n) (r n)"
  shows "pH_term_class \<tau> (psubst s M) = pH_term_class \<tau> (psubst r M)"
proof -
  have eq: "pH_term_eq \<tau> (psubst s M) (psubst r M)"
    by (rule pHcs_substitution_congruence[OF typed sig agree])
  have left: "pterm_in_language signature [] (psubst s M) \<tau>" by (rule pH_term_eq_left[OF eq])
  have right: "pterm_in_language signature [] (psubst r M) \<tau>" by (rule pH_term_eq_right[OF eq])
  show ?thesis by (rule iffD2[OF pH_term_class_eq_iff[OF left right] eq])
qed

end

end
