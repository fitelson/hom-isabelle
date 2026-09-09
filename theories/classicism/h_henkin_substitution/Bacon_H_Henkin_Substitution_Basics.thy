theory Bacon_H_Henkin_Substitution_Basics
  imports Bacon_H_Henkin_Equality_Development.Bacon_H_Henkin_Equality
begin

section \<open>Substitution is independent of identity-class representatives\<close>

text \<open>
  s(x) ∼ₜ r(x) for each free x ⇒ M[s] ∼ₜ M[r]. Bacon–Dorr, Theorem 3.2, p. 45 n. 64;
  Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: The auxiliary lemmas separate a typed closed substitution
  into its head and tail and establish ordinary syntactic agreement. The terminal
  substitution theory performs context induction.

  Status: Preparation for representative independence, without Functionality.
\<close>

subsection \<open>Syntactic agreement on the variables in a typing context\<close>

text \<open>
  s↾Γ = r↾Γ ⇒ M[s] = M[r] for Γ ⊢ M : τ. Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon,
  Theorem 15.3, pp. 320–321.

  Isabelle representation: Equality here is syntactic. lift_subst fixes the newest
  bound slot and shifts the older replacements.

  Status: Only the slots recorded in Γ matter; off-context assignments need not agree.
\<close>

lemma H_lift_substitution_agreement:
  assumes agree: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> s n = r n"
    and lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  shows "lift_subst s n = lift_subst r n"
proof (cases n)
  case 0
  then show ?thesis by (simp only: lift_subst.simps)
next
  case (Suc m)
  have tail_lookup: "lookup \<Gamma> m = Some \<tau>"
    using lookup Suc by (simp only: lookup_Cons_Suc)
  have equal: "s m = r m"
    by (rule agree[OF tail_lookup])
  show ?thesis by (simp only: Suc lift_subst.simps equal)
qed

lemma H_substitution_agreement:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and agree: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> s n = r n"
  shows "subst s M = subst r M"
  using typed agree
proof (induction arbitrary: s r rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  have equal: "s n = r n"
    by (rule Var.prems[OF Var.hyps])
  show ?case by (simp only: subst.simps equal)
next
  case (Const \<Gamma> c \<tau>)
  show ?case by (simp only: subst.simps)
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have left: "subst s M = subst r M"
    by (rule App.IH(1)[where s=s and r=r, OF App.prems])
  have right: "subst s N = subst r N"
    by (rule App.IH(2)[where s=s and r=r, OF App.prems])
  show ?case by (simp only: subst.simps left right)
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      lift_subst s n = lift_subst r n"
  proof -
    fix n \<rho>
    assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>"
    show "lift_subst s n = lift_subst r n"
      by (rule H_lift_substitution_agreement[where \<Gamma>=\<Gamma> and \<sigma>=\<sigma>
            and n=n and \<tau>=\<rho> and s=s and r=r, OF Lam.prems lookup])
  qed
  have "subst (lift_subst s) M = subst (lift_subst r) M"
    by (rule Lam.IH[where s="lift_subst s" and r="lift_subst r", OF lifted])
  then show ?case by (simp only: subst.simps)
next
  case (Eq \<Gamma> M \<sigma> N)
  have left: "subst s M = subst r M"
    by (rule Eq.IH(1)[where s=s and r=r, OF Eq.prems])
  have right: "subst s N = subst r N"
    by (rule Eq.IH(2)[where s=s and r=r, OF Eq.prems])
  show ?case by (simp only: subst.simps left right)
next
  case (Neg \<Gamma> A)
  have body: "subst s A = subst r A"
    by (rule Neg.IH[where s=s and r=r, OF Neg.prems])
  show ?case by (simp only: subst.simps body)
next
  case (Conj \<Gamma> A B)
  have left: "subst s A = subst r A"
    by (rule Conj.IH(1)[where s=s and r=r, OF Conj.prems])
  have right: "subst s B = subst r B"
    by (rule Conj.IH(2)[where s=s and r=r, OF Conj.prems])
  show ?case by (simp only: subst.simps left right)
next
  case (Disj \<Gamma> A B)
  have left: "subst s A = subst r A"
    by (rule Disj.IH(1)[where s=s and r=r, OF Disj.prems])
  have right: "subst s B = subst r B"
    by (rule Disj.IH(2)[where s=s and r=r, OF Disj.prems])
  show ?case by (simp only: subst.simps left right)
next
  case (Imp \<Gamma> A B)
  have left: "subst s A = subst r A"
    by (rule Imp.IH(1)[where s=s and r=r, OF Imp.prems])
  have right: "subst s B = subst r B"
    by (rule Imp.IH(2)[where s=s and r=r, OF Imp.prems])
  show ?case by (simp only: subst.simps left right)
next
  case (Forall \<sigma> \<Gamma> A)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      lift_subst s n = lift_subst r n"
  proof -
    fix n \<rho>
    assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>"
    show "lift_subst s n = lift_subst r n"
      by (rule H_lift_substitution_agreement[where \<Gamma>=\<Gamma> and \<sigma>=\<sigma>
            and n=n and \<tau>=\<rho> and s=s and r=r, OF Forall.prems lookup])
  qed
  have "subst (lift_subst s) A = subst (lift_subst r) A"
    by (rule Forall.IH[where s="lift_subst s" and r="lift_subst r", OF lifted])
  then show ?case by (simp only: subst.simps)
next
  case (Exists \<sigma> \<Gamma> A)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      lift_subst s n = lift_subst r n"
  proof -
    fix n \<rho>
    assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>"
    show "lift_subst s n = lift_subst r n"
      by (rule H_lift_substitution_agreement[where \<Gamma>=\<Gamma> and \<sigma>=\<sigma>
            and n=n and \<tau>=\<rho> and s=s and r=r, OF Exists.prems lookup])
  qed
  have "subst (lift_subst s) A = subst (lift_subst r) A"
    by (rule Exists.IH[where s="lift_subst s" and r="lift_subst r", OF lifted])
  then show ?case by (simp only: subst.simps)
qed

lemma H_closed_substitution_identity:
  assumes "[] \<turnstile> M : \<tau>"
  shows "subst s M = M"
proof -
  have agreement: "\<And>n \<sigma>. lookup [] n = Some \<sigma> \<Longrightarrow> s n = Var n"
    by (simp add: lookup_def)
  have "subst s M = subst Var M"
    by (rule H_substitution_agreement[where \<Gamma>="[]" and M=M and \<tau>=\<tau>
          and s=s and r=Var, OF assms agreement])
  then show ?thesis by simp
qed

subsection \<open>Separating the first variable from the remaining variables\<close>

text \<open>
  s = (s₀, s₁, …): the head has type σ and the tail closes Γ when s closes σ :: Γ.
  Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: head and tail are represented by s 0 and λn. s(Suc n), with
  separate typing lemmas.

  Status: Structural ingredients for the next β-decomposition step.
\<close>

lemma H_closed_substitution_head_type:
  assumes s_typed: "term_subst_typed (\<sigma> # \<Gamma>) [] s"
  shows "[] \<turnstile> s 0 : \<sigma>"
proof -
  have lookup: "lookup (\<sigma> # \<Gamma>) 0 = Some \<sigma>" by simp
  show ?thesis by (rule term_subst_typedD[OF s_typed lookup])
qed

lemma H_closed_substitution_tail_type:
  assumes s_typed: "term_subst_typed (\<sigma> # \<Gamma>) [] s"
  shows "term_subst_typed \<Gamma> [] (\<lambda>n. s (Suc n))"
proof (unfold term_subst_typed_def, intro allI impI)
  fix n \<rho>
  assume lookup: "lookup \<Gamma> n = Some \<rho>"
  have extended: "lookup (\<sigma> # \<Gamma>) (Suc n) = Some \<rho>"
    using lookup by simp
  show "[] \<turnstile> s (Suc n) : \<rho>"
    by (rule term_subst_typedD[OF s_typed extended])
qed

lemma H_substitution_head_tail:
  "subst0 (s 0) (subst (lift_subst (\<lambda>n. s (Suc n))) M) = subst s M"
proof -
  have maps: "case_nat (s 0) (\<lambda>n. s (Suc n)) = s"
  proof (rule ext)
    fix n
    show "case_nat (s 0) (\<lambda>n. s (Suc n)) n = s n"
      by (cases n) simp_all
  qed
  have "subst0 (s 0) (subst (lift_subst (\<lambda>n. s (Suc n))) M) =
      subst (case_nat (s 0) (\<lambda>n. s (Suc n))) M"
    by (rule subst0_subst_lift)
  also have "... = subst s M"
    by (simp only: maps)
  finally show ?thesis .
qed


end
