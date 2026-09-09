theory Bacon_Parametric_Canonical_Substitution_Basics
  imports Bacon_Parametric_Henkin_Theory
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Renaming_Algebra
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Existential_Witness_Theorem
begin

section \<open>Closed substitutions and their finite context support\<close>

text \<open>
  M[s][r] = M[x ↦ s(x)[r]], and s↾Γ = r↾Γ ⇒ M[s] = M[r]
  when Γ ⊢ M : τ.  Source role: Bacon–Dorr, p. 45 n. 64; Bacon,
  Theorem 15.3, pp. 320–321.

  Isabelle representation: the shared renaming algebra supplies the binder
  commutations.  We add composition, agreement, and head/tail decomposition
  for substitutions over arbitrary constant-name carriers.

  Status: syntactic lemmas only.  The following leaf uses them to prove
  identity-class representative independence by context induction.
\<close>

lemma pHcs_lift_comp:
  "(\<lambda>n. psubst (plift_subst s) (plift_subst r n)) =
    plift_subst (\<lambda>n. psubst s (r n))"
proof (rule ext)
  fix n
  show "psubst (plift_subst s) (plift_subst r n) =
      plift_subst (\<lambda>n. psubst s (r n)) n"
    by (cases n) (simp_all add: pproof_psubst_lift_shift[unfolded pshift_def])
qed

lemma pHcs_subst_comp:
  "psubst s (psubst r M) = psubst (\<lambda>n. psubst s (r n)) M"
proof (induction M arbitrary: s r)
  case (PVar n)
  show ?case by (simp only: psubst.simps)
next
  case (PConst c \<sigma>)
  show ?case by (simp only: psubst.simps)
next
  case (PApp M N)
  show ?case by (simp only: psubst.simps PApp.IH)
next
  case (PLam \<sigma> M)
  show ?case by (simp only: psubst.simps PLam.IH pHcs_lift_comp)
next
  case (PEq \<sigma> M N)
  show ?case by (simp only: psubst.simps PEq.IH)
next
  case (PNeg M)
  show ?case by (simp only: psubst.simps PNeg.IH)
next
  case (PConj M N)
  show ?case by (simp only: psubst.simps PConj.IH)
next
  case (PDisj M N)
  show ?case by (simp only: psubst.simps PDisj.IH)
next
  case (PImp M N)
  show ?case by (simp only: psubst.simps PImp.IH)
next
  case (PForall \<sigma> M)
  show ?case by (simp only: psubst.simps PForall.IH pHcs_lift_comp)
next
  case (PExists \<sigma> M)
  show ?case by (simp only: psubst.simps PExists.IH pHcs_lift_comp)
qed

lemma pHcs_subst_ident: "psubst PVar M = M"
proof -
  have lifted: "plift_subst PVar = PVar"
  proof (rule ext)
    fix n :: nat
    show "plift_subst PVar n = PVar n"
      by (cases n) simp_all
  qed
  show ?thesis by (induction M) (simp_all only: psubst.simps lifted)
qed

lemma pHcs_lift_agreement:
  assumes agree: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> s n = r n"
    and look: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  shows "plift_subst s n = plift_subst r n"
proof (cases n)
  case 0
  show ?thesis by (simp only: 0 plift_subst.simps)
next
  case (Suc m)
  have old: "lookup \<Gamma> m = Some \<tau>" using look by (simp only: Suc lookup_Cons_Suc)
  have eq: "s m = r m" by (rule agree[OF old])
  show ?thesis by (simp only: Suc plift_subst.simps eq)
qed

lemma pHcs_subst_agreement:
  assumes typed: "has_ptype \<Gamma> M \<tau>"
    and agree: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> s n = r n"
  shows "psubst s M = psubst r M"
  using typed agree
proof (induction arbitrary: s r rule: has_ptype.induct)
  case (PVar \<Gamma> n \<tau>)
  show ?case by (simp only: psubst.simps PVar.prems[OF PVar.hyps])
next
  case (PConst \<Gamma> c \<tau>)
  show ?case by (simp only: psubst.simps)
next
  case (PApp \<Gamma> M \<sigma> \<tau> N)
  show ?case by (simp only: psubst.simps PApp.IH(1)[OF PApp.prems] PApp.IH(2)[OF PApp.prems])
next
  case (PLam \<sigma> \<Gamma> M \<tau>)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      plift_subst s n = plift_subst r n" by (rule pHcs_lift_agreement[OF PLam.prems])
  show ?case by (simp only: psubst.simps PLam.IH[OF lifted])
next
  case (PEq \<Gamma> M \<sigma> N)
  show ?case by (simp only: psubst.simps PEq.IH(1)[OF PEq.prems] PEq.IH(2)[OF PEq.prems])
next
  case (PNeg \<Gamma> A)
  show ?case by (simp only: psubst.simps PNeg.IH[OF PNeg.prems])
next
  case (PConj \<Gamma> A B)
  show ?case by (simp only: psubst.simps PConj.IH(1)[OF PConj.prems] PConj.IH(2)[OF PConj.prems])
next
  case (PDisj \<Gamma> A B)
  show ?case by (simp only: psubst.simps PDisj.IH(1)[OF PDisj.prems] PDisj.IH(2)[OF PDisj.prems])
next
  case (PImp \<Gamma> A B)
  show ?case by (simp only: psubst.simps PImp.IH(1)[OF PImp.prems] PImp.IH(2)[OF PImp.prems])
next
  case (PForall \<sigma> \<Gamma> A)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      plift_subst s n = plift_subst r n" by (rule pHcs_lift_agreement[OF PForall.prems])
  show ?case by (simp only: psubst.simps PForall.IH[OF lifted])
next
  case (PExists \<sigma> \<Gamma> A)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      plift_subst s n = plift_subst r n" by (rule pHcs_lift_agreement[OF PExists.prems])
  show ?case by (simp only: psubst.simps PExists.IH[OF lifted])
qed

lemma pHcs_closed_subst:
  assumes "has_ptype [] M \<tau>"
  shows "psubst s M = M"
proof -
  have "psubst s M = psubst PVar M"
    by (rule pHcs_subst_agreement[OF assms]) (simp add: lookup_def)
  then show ?thesis by (simp only: pHcs_subst_ident)
qed

lemma pHcs_head_tail:
  "psubst0 (s 0) (psubst (plift_subst (\<lambda>n. s (Suc n))) M) = psubst s M"
proof -
  have maps_eq: "(\<lambda>n. psubst (case_nat (s 0) PVar) (plift_subst (\<lambda>n. s (Suc n)) n)) = s"
  proof (rule ext)
    fix n
    show "psubst (case_nat (s 0) PVar) (plift_subst (\<lambda>n. s (Suc n)) n) = s n"
    proof (cases n)
      case 0
      show ?thesis by (simp add: 0)
    next
      case (Suc m)
      have inverse: "psubst (case_nat (s 0) PVar) (prename Suc (s (Suc m))) = s (Suc m)"
        by (rule psubst_prename_inverse) simp
      show ?thesis by (simp only: Suc plift_subst.simps inverse)
    qed
  qed
  show ?thesis by (simp only: psubst0_def pHcs_subst_comp maps_eq)
qed

lemma pHcs_lift_signature:
  assumes sig: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> pterm_in_signature \<Sigma> (s n)"
    and look: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  shows "pterm_in_signature \<Sigma> (plift_subst s n)"
proof (cases n)
  case 0
  show ?thesis by (simp only: 0 plift_subst.simps pterm_in_signature.simps)
next
  case (Suc m)
  have old: "lookup \<Gamma> m = Some \<tau>" using look by (simp only: Suc lookup_Cons_Suc)
  show ?thesis using sig[OF old] by (simp only: Suc plift_subst.simps prename_signature)
qed

lemma pHcs_subst_signature:
  assumes typed: "has_ptype \<Gamma> M \<tau>" and sig: "pterm_in_signature \<Sigma> M"
    and sub: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> pterm_in_signature \<Sigma> (s n)"
  shows "pterm_in_signature \<Sigma> (psubst s M)"
  using typed sig sub
proof (induction arbitrary: s rule: has_ptype.induct)
  case (PLam \<sigma> \<Gamma> M \<tau>)
  have body: "pterm_in_signature \<Sigma> M" using PLam.prems(1) by simp
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      pterm_in_signature \<Sigma> (plift_subst s n)"
    by (rule pHcs_lift_signature[OF PLam.prems(2)])
  show ?case using PLam.IH[OF body lifted] by simp
next
  case (PForall \<sigma> \<Gamma> A)
  have body: "pterm_in_signature \<Sigma> A" using PForall.prems(1) by simp
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      pterm_in_signature \<Sigma> (plift_subst s n)"
    by (rule pHcs_lift_signature[OF PForall.prems(2)])
  show ?case using PForall.IH[OF body lifted] by simp
next
  case (PExists \<sigma> \<Gamma> A)
  have body: "pterm_in_signature \<Sigma> A" using PExists.prems(1) by simp
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      pterm_in_signature \<Sigma> (plift_subst s n)"
    by (rule pHcs_lift_signature[OF PExists.prems(2)])
  show ?case using PExists.IH[OF body lifted] by simp
qed (simp_all add: psubst.simps)

lemma pHcs_subst_language:
  assumes typed: "has_ptype \<Gamma> M \<tau>" and sig: "pterm_in_signature \<Sigma> M"
    and sub: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> pterm_in_language \<Sigma> [] (s n) \<rho>"
  shows "pterm_in_language \<Sigma> [] (psubst s M) \<tau>"
proof -
  have st: "has_ptype [] (s n) \<rho>" if look: "lookup \<Gamma> n = Some \<rho>" for n \<rho>
    using sub[OF look] unfolding pterm_in_language_def by (rule conjunct1)
  have ss: "pterm_in_signature \<Sigma> (s n)" if look: "lookup \<Gamma> n = Some \<rho>" for n \<rho>
    using sub[OF look] unfolding pterm_in_language_def by (rule conjunct2)
  have mt: "has_ptype [] (psubst s M) \<tau>" by (rule psubst_preserves_typing[OF typed st])
  have ms: "pterm_in_signature \<Sigma> (psubst s M)" by (rule pHcs_subst_signature[OF typed sig ss])
  show ?thesis unfolding pterm_in_language_def by (rule conjI[OF mt ms])
qed

end
