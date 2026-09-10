theory Bacon_Source_Global_Substitution
  imports Bacon_Source_Global_Typing
begin

section \<open>Global typing of capture-avoiding substitution\<close>

text \<open>
  If G ⊢ A:τ and H ⊢ s(v):G(v) for every variable index v, then
  H ⊢ A[s]:τ.  This total-stock condition suffices for capture-avoiding
  substitution in Bacon–Dorr Figure 2, p. 8.

  Isabelle representation: the existing ssubst and slift_subst operations
  are unchanged.  The new lemmas use total stocks G and H, extending both
  by the bound type under a λ.

  Status: source syntax typing only.  Richness is not needed, no H relation
  is defined, and no semantic substitution principle is assumed.
\<close>

lemma sshift_global_type:
  assumes "has_sgtype L G A \<tau>"
  shows "has_sgtype L (sgextend \<sigma> G) (sshift A) \<tau>"
  unfolding sshift_def
proof (rule srename_preserves_global_typing[where H="sgextend \<sigma> G" and r=Suc, OF assms])
  fix n
  show "sgextend \<sigma> G (Suc n) = G n" by (rule sgextend_Suc)
qed

lemma slift_subst_global_type:
  assumes sub: "\<And>n. has_sgtype L H (s n) (G n)"
  shows "has_sgtype L (sgextend \<sigma> H) (slift_subst s n) (sgextend \<sigma> G n)"
proof (cases n)
  case 0
  have typed: "has_sgtype L (sgextend \<sigma> H) (SVar 0) (sgextend \<sigma> H 0)"
    by (rule has_sgtype.Var)
  show ?thesis using typed by (simp only: 0 slift_subst.simps sgextend_zero)
next
  case (Suc m)
  have old: "has_sgtype L H (s m) (G m)" by (rule sub)
  have shifted: "has_sgtype L (sgextend \<sigma> H) (sshift (s m)) (G m)"
    by (rule sshift_global_type[OF old])
  show ?thesis using shifted by (simp only: Suc slift_subst.simps sshift_def sgextend_Suc)
qed

lemma ssubst_preserves_global_typing:
  assumes typed: "has_sgtype L G A \<tau>"
    and sub: "\<And>n. has_sgtype L H (s n) (G n)"
  shows "has_sgtype L H (ssubst s A) \<tau>"
  using typed sub
proof (induction arbitrary: H s rule: has_sgtype.induct)
  case Var
  show ?case unfolding ssubst.simps by (rule Var.prems)
next
  case Const
  show ?case unfolding ssubst.simps by (rule has_sgtype.Const)
next
  case Logical
  show ?case unfolding ssubst.simps by (rule has_sgtype.Logical)
next
  case (App G M \<sigma> \<tau> N)
  have mt: "has_sgtype L H (ssubst s M) (Arr \<sigma> \<tau>)"
    by (rule App.IH(1)[where H=H and s=s, OF App.prems])
  have nt: "has_sgtype L H (ssubst s N) \<sigma>"
    by (rule App.IH(2)[where H=H and s=s, OF App.prems])
  show ?case unfolding ssubst.simps by (rule has_sgtype.App[OF mt nt])
next
  case (Lam \<sigma> G M \<tau>)
  have lifted: "\<And>n. has_sgtype L (sgextend \<sigma> H) (slift_subst s n) (sgextend \<sigma> G n)"
    by (rule slift_subst_global_type[where G=G and H=H and s=s, OF Lam.prems])
  have body: "has_sgtype L (sgextend \<sigma> H) (ssubst (slift_subst s) M) \<tau>"
    by (rule Lam.IH[where H="sgextend \<sigma> H" and s="slift_subst s", OF lifted])
  show ?case unfolding ssubst.simps by (rule has_sgtype.Lam[OF body])
qed

lemma ssubst0_global_type:
  assumes body: "has_sgtype L (sgextend \<sigma> G) A \<tau>"
    and arg: "has_sgtype L G T \<sigma>"
  shows "has_sgtype L G (ssubst0 T A) \<tau>"
  unfolding ssubst0_def
proof (rule ssubst_preserves_global_typing[where H=G and s="case_nat T SVar", OF body])
  fix n
  show "has_sgtype L G (case_nat T SVar n) (sgextend \<sigma> G n)"
  proof (cases n)
    case 0
    show ?thesis using arg by (simp add: 0)
  next
    case (Suc m)
    have typed: "has_sgtype L G (SVar m) (G m)" by (rule has_sgtype.Var)
    show ?thesis using typed by (simp add: Suc)
  qed
qed

section \<open>Opening a variable after closing it\<close>

text \<open>
  Abstract v in A, then substitute that same v for the new bound variable:
  A is recovered.  This is the syntactic closing/opening calculation behind
  the variable convention in Bacon–Dorr Figure 2.

  Isabelle representation: a general inverse-map lemma handles substitution
  after renaming, including every existing binder.  The sclose specialization
  is an equality of raw terms, so it does not require typing or richness.

  Status: de Bruijn algebra, not an object-language β theorem and not yet
  a named-variable/α-equivalence correspondence.
\<close>

lemma slift_subst_rename_inverse:
  assumes inverse: "\<And>n. s (r n) = SVar n"
  shows "slift_subst s (lift_ren r n) = SVar n"
  by (cases n) (simp_all add: inverse)

lemma ssubst_srename_inverse:
  assumes inverse: "\<And>n. s (r n) = SVar n"
  shows "ssubst s (srename r A) = A"
  using inverse
proof (induction A arbitrary: s r)
  case SVar
  show ?case by (simp only: srename.simps ssubst.simps SVar.prems)
next
  case SConst
  show ?case by (simp only: srename.simps ssubst.simps)
next
  case SLogical
  show ?case by (simp only: srename.simps ssubst.simps)
next
  case (SApp M N)
  have m: "ssubst s (srename r M) = M"
    by (rule SApp.IH(1)[where s=s and r=r, OF SApp.prems])
  have n: "ssubst s (srename r N) = N"
    by (rule SApp.IH(2)[where s=s and r=r, OF SApp.prems])
  show ?case by (simp only: srename.simps ssubst.simps m n)
next
  case (SLam \<sigma> M)
  have lifted: "\<And>n. slift_subst s (lift_ren r n) = SVar n"
    by (rule slift_subst_rename_inverse[where s=s and r=r, OF SLam.prems])
  have body: "ssubst (slift_subst s) (srename (lift_ren r) M) = M"
    by (rule SLam.IH[where s="slift_subst s" and r="lift_ren r", OF lifted])
  show ?case by (simp only: srename.simps ssubst.simps body)
qed

lemma ssubst0_sclose:
  "ssubst0 (SVar n) (sclose n A) = A"
  unfolding ssubst0_def sclose_def
proof (rule ssubst_srename_inverse[where s="case_nat (SVar n) SVar"
      and r="\<lambda>k. if k = n then 0 else Suc k"])
  fix k
  show "case_nat (SVar n) SVar (if k = n then 0 else Suc k) = SVar k"
    by (cases "k = n") simp_all
qed

lemma ssubst0_sshift:
  "ssubst0 T (sshift A) = A"
  unfolding ssubst0_def sshift_def
proof (rule ssubst_srename_inverse[where s="case_nat T SVar" and r=Suc])
  fix n
  show "case_nat T SVar (Suc n) = SVar n" by simp
qed

end
