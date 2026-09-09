theory Bacon_H_Henkin_Substitution
  imports Bacon_H_Henkin_Substitution_Beta
begin

section \<open>Representative independence by context induction\<close>

text \<open>
  [M[s]]ₜ = [M[r]]ₜ whenever each s(x) and r(x) represent the same assigned class.
  Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: Induction is on the finite typing context, not on pointwise
  behavior of λ-abstractions.

  Status: Representative independence; the canonical model and truth lemma are in the
  subsequent directory.
\<close>

context H_closed_Henkin
begin

subsection \<open>Simultaneous-substitution congruence\<close>

text \<open>
  Γ ⊢ M : τ and ∀x : σ in Γ, s(x) ∼ₜ r(x) ⇒ M[s] ∼ₜ M[r]. Bacon–Dorr, Theorem 3.2, p.
  45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: s and r substitute closed terms. The successor case
  abstracts the first slot, uses the induction hypothesis on that term, and
  β-contracts the two applications.

  Status: Full typed closed-substitution congruence, with no Functionality premise.
\<close>

lemma H_term_eq_substitution_successor:
  assumes typed: "\<sigma> # \<Gamma> \<turnstile> M : \<tau>"
    and s_typed: "term_subst_typed (\<sigma> # \<Gamma>) [] s"
    and r_typed: "term_subst_typed (\<sigma> # \<Gamma>) [] r"
    and head_eq: "H_term_eq \<sigma> (s 0) (r 0)"
    and function_eq: "H_term_eq (\<sigma> \<rightarrow>\<^sub>o \<tau>)
      (subst (\<lambda>n. s (Suc n)) (Lam \<sigma> M))
      (subst (\<lambda>n. r (Suc n)) (Lam \<sigma> M))"
  shows "H_term_eq \<tau> (subst s M) (subst r M)"
proof -
  let ?s = "\<lambda>n. s (Suc n)"
  let ?r = "\<lambda>n. r (Suc n)"
  have app_eq: "H_term_eq \<tau>
      (App (subst ?s (Lam \<sigma> M)) (s 0))
      (App (subst ?r (Lam \<sigma> M)) (r 0))"
    by (rule H_term_eq_app_cong[OF function_eq head_eq])
  have beta_s: "H_term_eq \<tau>
      (App (subst ?s (Lam \<sigma> M)) (s 0)) (subst s M)"
    by (rule H_term_eq_substitution_beta[OF typed s_typed])
  have beta_r: "H_term_eq \<tau>
      (App (subst ?r (Lam \<sigma> M)) (r 0)) (subst r M)"
    by (rule H_term_eq_substitution_beta[OF typed r_typed])
  have first: "H_term_eq \<tau> (subst s M)
      (App (subst ?r (Lam \<sigma> M)) (r 0))"
    by (rule H_term_eq_trans[OF H_term_eq_sym[OF beta_s] app_eq])
  show ?thesis by (rule H_term_eq_trans[OF first beta_r])
qed

text \<open>
  Source role: the next theorem is the representative-independence lemma
  required by Bacon–Dorr's canonical BBK construction (Theorem 3.2,
  p. 45 n. 64) and Bacon's proof of Theorem 15.3.

  Let T be a closed H Henkin theory and write M ∼ₜ N when the
  object-language identity (M =σ N) belongs to T.  In Bacon's notation the
  theorem says:

      M : τ
      s(v) ∼ₜ r(v), for every free variable v:σ of M
      ──────────────────────────────────────────────────
                         M[s] ∼ₜ M[r]

  Here s and r are type-respecting substitutions by closed terms.  They may
  choose different representatives, but must choose from the same T-identity
  class for every free variable.  Isabelle represents those variables by the
  de Bruijn context Γ and writes the instances as \<open>subst s M\<close> and
  \<open>subst r M\<close>.

  Equivalently, the prospective value [M[s]]ₜ does not
  depend on the representative selected for each assigned identity class.

  Proof idea: induct on the length of \<open>Γ\<close>.  At the successor step,
  abstract the first variable, apply the induction hypothesis to that function
  term, use application congruence on the two chosen representatives, and
  β-contract both sides.  This uses Leibniz's Law and β conversion only;
  it does not assume Functionality.

  Status: verified source ingredient, not yet the full BBK interpretation or
  truth lemma.  It is used next to prove that canonical denotation is
  independent of representative choices.
\<close>

theorem H_term_eq_subst_cong:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and s_typed: "term_subst_typed \<Gamma> [] s"
    and r_typed: "term_subst_typed \<Gamma> [] r"
    and pointwise: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      H_term_eq \<sigma> (s n) (r n)"
  shows "H_term_eq \<tau> (subst s M) (subst r M)"
  using typed s_typed r_typed pointwise
proof (induction \<Gamma> arbitrary: M \<tau> s r)
  case Nil
  have eq: "H_term_eq \<tau> M M"
    using Nil.prems(1) by (rule H_term_eq_refl)
  have left: "subst s M = M"
    using Nil.prems(1) by (rule H_closed_substitution_identity)
  have right: "subst r M = M"
    using Nil.prems(1) by (rule H_closed_substitution_identity)
  show ?case using eq left right by simp
next
  case (Cons \<sigma> \<Gamma>)
  let ?s = "\<lambda>n. s (Suc n)"
  let ?r = "\<lambda>n. r (Suc n)"
  have lam_type: "\<Gamma> \<turnstile> Lam \<sigma> M : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using Cons.prems(1) by (rule has_type.Lam)
  have s_tail: "term_subst_typed \<Gamma> [] ?s"
    using Cons.prems(2) by (rule H_closed_substitution_tail_type)
  have r_tail: "term_subst_typed \<Gamma> [] ?r"
    using Cons.prems(3) by (rule H_closed_substitution_tail_type)
  have tail_eq: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow>
      H_term_eq \<rho> (?s n) (?r n)"
    using Cons.prems(4) by (rule H_term_eq_substitution_tail)
  have function_eq: "H_term_eq (\<sigma> \<rightarrow>\<^sub>o \<tau>)
      (subst ?s (Lam \<sigma> M)) (subst ?r (Lam \<sigma> M))"
    by (rule Cons.IH[where M="Lam \<sigma> M" and \<tau>="\<sigma> \<rightarrow>\<^sub>o \<tau>"
          and s="?s" and r="?r", OF lam_type s_tail r_tail tail_eq])
  have head_eq: "H_term_eq \<sigma> (s 0) (r 0)"
    using Cons.prems(4) by (rule H_term_eq_substitution_head)
  show ?case
    by (rule H_term_eq_substitution_successor[
          OF Cons.prems(1,2,3) head_eq function_eq])
qed

corollary H_term_class_subst_cong:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and s_typed: "term_subst_typed \<Gamma> [] s"
    and r_typed: "term_subst_typed \<Gamma> [] r"
    and pointwise: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      H_term_eq \<sigma> (s n) (r n)"
  shows "H_term_class \<tau> (subst s M) = H_term_class \<tau> (subst r M)"
proof -
  have left_type: "[] \<turnstile> subst s M : \<tau>"
    using typed s_typed by (rule term_subst_preserves_typing)
  have right_type: "[] \<turnstile> subst r M : \<tau>"
    using typed r_typed by (rule term_subst_preserves_typing)
  have eq: "H_term_eq \<tau> (subst s M) (subst r M)"
    by (rule H_term_eq_subst_cong[where \<Gamma>=\<Gamma> and M=M and \<tau>=\<tau>
          and s=s and r=r, OF typed s_typed r_typed pointwise])
  show ?thesis
    using H_term_class_eq_iff[OF left_type right_type] eq by blast
qed

end
end
