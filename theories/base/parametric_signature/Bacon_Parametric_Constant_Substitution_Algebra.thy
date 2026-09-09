theory Bacon_Parametric_Constant_Substitution_Algebra
  imports Bacon_Parametric_Renaming_Algebra
begin

section \<open>Capture-avoiding constant replacement\<close>

text \<open>
  M[N/c] must shift N when it passes beneath λ, ∀, or ∃.  The equations
  below make its interaction with A[T/x] explicit and turn a fresh witness
  into an eigenvariable.  Sources: Bacon--Dorr p.45 n.64; Bacon,
  Proposition 15.4.  These are syntactic equations, not assumed proof rules.
\<close>

lemma pproof_pconst_prename:
  "prename r (pconst_subst c \<sigma> N M) = pconst_subst c \<sigma> (prename r N) (prename r M)"
proof (induction M arbitrary: r N)
  case (PVar n)
  show ?case by (simp only: prename.simps pconst_subst.simps comp_def)
next
  case (PConst d \<tau>)
  show ?case
  proof (cases "c = d \<and> \<sigma> = \<tau>")
    case True
    show ?thesis by (simp only: prename.simps pconst_subst.simps True if_True simp_thms)
  next
    case False
    show ?thesis by (simp only: prename.simps pconst_subst.simps False if_False)
  qed
next
  case (PApp X Y)
  show ?case by (simp only: prename.simps pconst_subst.simps PApp.IH(1)[where r=r and N=N] PApp.IH(2)[where r=r and N=N])
next
  case (PLam \<tau> X)
  show ?case by (simp only: prename.simps pconst_subst.simps PLam.IH[where r="lift_ren r" and N="pshift N"] pproof_prename_lift_shift)
next
  case (PEq \<tau> X Y)
  show ?case by (simp only: prename.simps pconst_subst.simps PEq.IH(1)[where r=r and N=N] PEq.IH(2)[where r=r and N=N])
next
  case (PNeg X)
  show ?case by (simp only: prename.simps pconst_subst.simps PNeg.IH[where r=r and N=N])
next
  case (PConj X Y)
  show ?case by (simp only: prename.simps pconst_subst.simps PConj.IH(1)[where r=r and N=N] PConj.IH(2)[where r=r and N=N])
next
  case (PDisj X Y)
  show ?case by (simp only: prename.simps pconst_subst.simps PDisj.IH(1)[where r=r and N=N] PDisj.IH(2)[where r=r and N=N])
next
  case (PImp X Y)
  show ?case by (simp only: prename.simps pconst_subst.simps PImp.IH(1)[where r=r and N=N] PImp.IH(2)[where r=r and N=N])
next
  case (PForall \<tau> X)
  show ?case by (simp only: prename.simps pconst_subst.simps PForall.IH[where r="lift_ren r" and N="pshift N"] pproof_prename_lift_shift)
next
  case (PExists \<tau> X)
  show ?case by (simp only: prename.simps pconst_subst.simps PExists.IH[where r="lift_ren r" and N="pshift N"] pproof_prename_lift_shift)
qed

lemma pproof_pconst_shift:
  "pconst_subst c \<sigma> (pshift N) (pshift M) = pshift (pconst_subst c \<sigma> N M)"
  by (simp only: pshift_def pproof_pconst_prename)

lemma pproof_pconst_lift:
  assumes maps: "\<And>n. s' n = pconst_subst c \<sigma> N (s n)"
  shows "plift_subst s' n = pconst_subst c \<sigma> (pshift N) (plift_subst s n)"
proof (cases n)
  case 0
  show ?thesis by (simp only: 0 plift_subst.simps pconst_subst.simps)
next
  case (Suc m)
  have mapped: "s' m = pconst_subst c \<sigma> N (s m)" by (rule maps)
  have renamed: "prename Suc (pconst_subst c \<sigma> N (s m)) =
      pconst_subst c \<sigma> (prename Suc N) (prename Suc (s m))"
    by (rule pproof_pconst_prename)
  show ?thesis by (simp only: Suc plift_subst.simps pshift_def mapped renamed)
qed

lemma pproof_pconst_psubst:
  assumes maps: "\<And>n. s' n = pconst_subst c \<sigma> N (s n)" and replacement: "psubst s' N' = N"
  shows "pconst_subst c \<sigma> N (psubst s A) = psubst s' (pconst_subst c \<sigma> N' A)"
  using maps replacement
proof (induction A arbitrary: s s' N N')
  case (PLam \<rho> A)
  have maps: "\<And>n. plift_subst s' n = pconst_subst c \<sigma> (pshift N) (plift_subst s n)"
    by (rule pproof_pconst_lift[where c=c and \<sigma>=\<sigma> and N=N and s=s and s'=s', OF PLam.prems(1)])
  have repl: "psubst (plift_subst s') (pshift N') = pshift N"
    by (simp only: pproof_psubst_lift_shift PLam.prems(2))
  show ?case using PLam.IH[where s="plift_subst s" and s'="plift_subst s'"
    and N="pshift N" and N'="pshift N'", OF maps repl] by (simp only: pconst_subst.simps psubst.simps)
next
  case (PForall \<rho> A)
  have maps: "\<And>n. plift_subst s' n = pconst_subst c \<sigma> (pshift N) (plift_subst s n)"
    by (rule pproof_pconst_lift[where c=c and \<sigma>=\<sigma> and N=N and s=s and s'=s', OF PForall.prems(1)])
  have repl: "psubst (plift_subst s') (pshift N') = pshift N"
    by (simp only: pproof_psubst_lift_shift PForall.prems(2))
  show ?case using PForall.IH[where s="plift_subst s" and s'="plift_subst s'"
    and N="pshift N" and N'="pshift N'", OF maps repl] by (simp only: pconst_subst.simps psubst.simps)
next
  case (PExists \<rho> A)
  have maps: "\<And>n. plift_subst s' n = pconst_subst c \<sigma> (pshift N) (plift_subst s n)"
    by (rule pproof_pconst_lift[where c=c and \<sigma>=\<sigma> and N=N and s=s and s'=s', OF PExists.prems(1)])
  have repl: "psubst (plift_subst s') (pshift N') = pshift N"
    by (simp only: pproof_psubst_lift_shift PExists.prems(2))
  show ?case using PExists.IH[where s="plift_subst s" and s'="plift_subst s'"
    and N="pshift N" and N'="pshift N'", OF maps repl] by (simp only: pconst_subst.simps psubst.simps)
next
  case (PVar n)
  show ?case by (simp only: pconst_subst.simps psubst.simps PVar.prems(1)[of n])
next
  case (PConst d \<tau>)
  show ?case
  proof (cases "c = d \<and> \<sigma> = \<tau>")
    case True
    show ?thesis by (simp only: pconst_subst.simps psubst.simps True if_True PConst.prems(2) simp_thms)
  next
    case False
    show ?thesis by (simp only: pconst_subst.simps psubst.simps False if_False)
  qed
next
  case (PApp X Y)
  show ?case by (simp only: pconst_subst.simps psubst.simps PApp.IH(1)[where s=s and s'=s' and N=N and N'=N', OF PApp.prems(1,2)] PApp.IH(2)[where s=s and s'=s' and N=N and N'=N', OF PApp.prems(1,2)])
next
  case (PEq \<tau> X Y)
  show ?case by (simp only: pconst_subst.simps psubst.simps PEq.IH(1)[where s=s and s'=s' and N=N and N'=N', OF PEq.prems(1,2)] PEq.IH(2)[where s=s and s'=s' and N=N and N'=N', OF PEq.prems(1,2)])
next
  case (PNeg X)
  show ?case by (simp only: pconst_subst.simps psubst.simps PNeg.IH[where s=s and s'=s' and N=N and N'=N', OF PNeg.prems(1,2)])
next
  case (PConj X Y)
  show ?case by (simp only: pconst_subst.simps psubst.simps PConj.IH(1)[where s=s and s'=s' and N=N and N'=N', OF PConj.prems(1,2)] PConj.IH(2)[where s=s and s'=s' and N=N and N'=N', OF PConj.prems(1,2)])
next
  case (PDisj X Y)
  show ?case by (simp only: pconst_subst.simps psubst.simps PDisj.IH(1)[where s=s and s'=s' and N=N and N'=N', OF PDisj.prems(1,2)] PDisj.IH(2)[where s=s and s'=s' and N=N and N'=N', OF PDisj.prems(1,2)])
next
  case (PImp X Y)
  show ?case by (simp only: pconst_subst.simps psubst.simps PImp.IH(1)[where s=s and s'=s' and N=N and N'=N', OF PImp.prems(1,2)] PImp.IH(2)[where s=s and s'=s' and N=N and N'=N', OF PImp.prems(1,2)])
qed

lemma pproof_pconst_psubst0:
  "pconst_subst c \<sigma> N (psubst0 T A) =
    psubst0 (pconst_subst c \<sigma> N T) (pconst_subst c \<sigma> (pshift N) A)"
proof -
  let ?s = "case_nat T PVar"
  let ?s' = "case_nat (pconst_subst c \<sigma> N T) PVar"
  have maps: "\<And>n. ?s' n = pconst_subst c \<sigma> N (?s n)" by (case_tac n; simp)
  have repl: "psubst ?s' (pshift N) = N" using psubst0_pshift[of "pconst_subst c \<sigma> N T" N]
    by (simp only: psubst0_def)
  show ?thesis unfolding psubst0_def
    by (rule pproof_pconst_psubst[where s="?s" and s'="?s'" and N=N and N'="pshift N" and A=A,
          OF maps repl])
qed

subsection \<open>The fresh witness becomes an eigenvariable\<close>

lemma pproof_abstract_fresh_instance:
  assumes fresh: "c \<notin> phenkin_names A"
  shows "pabstract_const c \<sigma> (psubst0 (PConst c \<sigma>) A) = A"
proof -
  let ?A = "prename (lift_ren Suc) A"
  have fresh_lift: "c \<notin> phenkin_names ?A" using fresh by (simp add: phenkin_names_prename)
  have shifted: "pshift (psubst0 (PConst c \<sigma>) A) = psubst0 (PConst c \<sigma>) ?A"
    by (simp add: pshift_def pproof_prename_psubst0)
  have restore: "psubst0 (PVar 0) ?A = A"
    unfolding psubst0_def by (rule psubst_prename_inverse) (case_tac n; simp)
  show ?thesis
    by (simp only: pabstract_const_def shifted pproof_pconst_psubst0 pconst_subst_same
          pconst_subst_fresh[OF fresh_lift] restore)
qed

lemma pproof_abstract_witness_axiom:
  assumes fresh: "c \<notin> phenkin_names A"
  shows "pabstract_const c \<sigma> (PImp (PExists \<sigma> A) (psubst0 (PConst c \<sigma>) A)) =
    PImp (pshift (PExists \<sigma> A)) A"
proof -
  have distributes: "pabstract_const c \<sigma> (PImp P Q) = PImp (pabstract_const c \<sigma> P) (pabstract_const c \<sigma> Q)" for P Q
    by (simp only: pabstract_const_def pshift_def prename.simps pconst_subst.simps)
  have fresh_exists: "c \<notin> phenkin_names (PExists \<sigma> A)" using fresh by simp
  show ?thesis by (simp only: distributes pabstract_const_fresh[OF fresh_exists] pproof_abstract_fresh_instance[OF fresh])
qed

end
