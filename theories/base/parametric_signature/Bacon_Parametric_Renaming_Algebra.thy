theory Bacon_Parametric_Renaming_Algebra
  imports Bacon_Parametric_Fresh_Constant
begin

section \<open>Renaming variables and replacing constants in H derivations\<close>

text \<open>
  If r respects the types of the free variables, Σ; Γ ⊢H A gives
  Σ; Δ ⊢H A[r].  If N:σ belongs to ℒ(Σ), replacing a constant c:σ
  by N likewise preserves theoremhood and local consequence.  Under a
  binder the substitution must use the shifted replacement term.
  Sources: Bacon--Dorr Figure 2, p.8, and the fresh-constant argument in
  p.45 n.64; Bacon, Chapter 15, Proposition 15.4.

  These lemmas concern arbitrary constant-name types.  They do not use
  countability, a natural-number enumeration of names, or Functionality.
\<close>

lemma pproof_lift_ren_comp:
  "lift_ren r \<circ> lift_ren s = lift_ren (r \<circ> s)"
  by (rule ext) (case_tac x; simp)

lemma pproof_prename_comp:
  "prename r (prename s M) = prename (r \<circ> s) M"
proof (induction M arbitrary: r s)
  case (PVar n)
  show ?case by (simp only: prename.simps comp_def)
next
  case (PConst d \<tau>)
  show ?case by (simp only: prename.simps)
next
  case (PApp X Y)
  show ?case by (simp only: prename.simps PApp.IH(1)[where r=r and s=s] PApp.IH(2)[where r=r and s=s])
next
  case (PLam \<tau> X)
  show ?case by (simp only: prename.simps PLam.IH[where r="lift_ren r" and s="lift_ren s"] pproof_lift_ren_comp)
next
  case (PEq \<tau> X Y)
  show ?case by (simp only: prename.simps PEq.IH(1)[where r=r and s=s] PEq.IH(2)[where r=r and s=s])
next
  case (PNeg X)
  show ?case by (simp only: prename.simps PNeg.IH[where r=r and s=s])
next
  case (PConj X Y)
  show ?case by (simp only: prename.simps PConj.IH(1)[where r=r and s=s] PConj.IH(2)[where r=r and s=s])
next
  case (PDisj X Y)
  show ?case by (simp only: prename.simps PDisj.IH(1)[where r=r and s=s] PDisj.IH(2)[where r=r and s=s])
next
  case (PImp X Y)
  show ?case by (simp only: prename.simps PImp.IH(1)[where r=r and s=s] PImp.IH(2)[where r=r and s=s])
next
  case (PForall \<tau> X)
  show ?case by (simp only: prename.simps PForall.IH[where r="lift_ren r" and s="lift_ren s"] pproof_lift_ren_comp)
next
  case (PExists \<tau> X)
  show ?case by (simp only: prename.simps PExists.IH[where r="lift_ren r" and s="lift_ren s"] pproof_lift_ren_comp)
qed

lemma pproof_prename_lift_shift:
  "prename (lift_ren r) (pshift M) = pshift (prename r M)"
proof -
  have maps: "lift_ren r \<circ> Suc = Suc \<circ> r" by (rule ext) simp
  show ?thesis by (simp only: pshift_def pproof_prename_comp maps)
qed

lemma pproof_psubst_prename:
  fixes s :: "nat \<Rightarrow> 'c pterm" and r :: "nat \<Rightarrow> nat" and M :: "'c pterm"
  shows "psubst s (prename r M) = psubst (s \<circ> r) M"
proof -
  have lifts: "plift_subst u \<circ> lift_ren v = plift_subst (u \<circ> v)"
    for u :: "nat \<Rightarrow> 'c pterm" and v :: "nat \<Rightarrow> nat"
  proof (rule ext)
    fix n :: nat
    show "(plift_subst u \<circ> lift_ren v) n = plift_subst (u \<circ> v) n"
      by (cases n; simp)
  qed
  show ?thesis
  proof (induction M arbitrary: s r)
    case (PVar n)
    show ?case by (simp only: prename.simps psubst.simps comp_def)
  next
    case (PConst d \<tau>)
    show ?case by (simp only: prename.simps psubst.simps)
  next
    case (PApp X Y)
    show ?case by (simp only: prename.simps psubst.simps PApp.IH(1)[where s=s and r=r] PApp.IH(2)[where s=s and r=r])
  next
    case (PLam \<tau> X)
    show ?case by (simp only: prename.simps psubst.simps PLam.IH[where s="plift_subst s" and r="lift_ren r"] lifts)
  next
    case (PEq \<tau> X Y)
    show ?case by (simp only: prename.simps psubst.simps PEq.IH(1)[where s=s and r=r] PEq.IH(2)[where s=s and r=r])
  next
    case (PNeg X)
    show ?case by (simp only: prename.simps psubst.simps PNeg.IH[where s=s and r=r])
  next
    case (PConj X Y)
    show ?case by (simp only: prename.simps psubst.simps PConj.IH(1)[where s=s and r=r] PConj.IH(2)[where s=s and r=r])
  next
    case (PDisj X Y)
    show ?case by (simp only: prename.simps psubst.simps PDisj.IH(1)[where s=s and r=r] PDisj.IH(2)[where s=s and r=r])
  next
    case (PImp X Y)
    show ?case by (simp only: prename.simps psubst.simps PImp.IH(1)[where s=s and r=r] PImp.IH(2)[where s=s and r=r])
  next
    case (PForall \<tau> X)
    show ?case by (simp only: prename.simps psubst.simps PForall.IH[where s="plift_subst s" and r="lift_ren r"] lifts)
  next
    case (PExists \<tau> X)
    show ?case by (simp only: prename.simps psubst.simps PExists.IH[where s="plift_subst s" and r="lift_ren r"] lifts)
  qed
qed

lemma pproof_prename_psubst:
  fixes r :: "nat \<Rightarrow> nat" and s :: "nat \<Rightarrow> 'c pterm" and M :: "'c pterm"
  shows "prename r (psubst s M) = psubst (\<lambda>n. prename r (s n)) M"
proof -
  have lifts: "(\<lambda>n. prename (lift_ren v) (plift_subst u n)) =
      plift_subst (\<lambda>n. prename v (u n))"
    for v :: "nat \<Rightarrow> nat" and u :: "nat \<Rightarrow> 'c pterm"
  proof (rule ext)
    fix n :: nat
    show "prename (lift_ren v) (plift_subst u n) = plift_subst (\<lambda>n. prename v (u n)) n"
      by (cases n; simp add: pproof_prename_lift_shift[unfolded pshift_def])
  qed
  show ?thesis
  proof (induction M arbitrary: r s)
    case (PVar n)
    show ?case by (simp only: prename.simps psubst.simps comp_def)
  next
    case (PConst d \<tau>)
    show ?case by (simp only: prename.simps psubst.simps)
  next
    case (PApp X Y)
    show ?case by (simp only: prename.simps psubst.simps PApp.IH(1)[where r=r and s=s] PApp.IH(2)[where r=r and s=s])
  next
    case (PLam \<tau> X)
    show ?case by (simp only: prename.simps psubst.simps PLam.IH[where r="lift_ren r" and s="plift_subst s"] lifts)
  next
    case (PEq \<tau> X Y)
    show ?case by (simp only: prename.simps psubst.simps PEq.IH(1)[where r=r and s=s] PEq.IH(2)[where r=r and s=s])
  next
    case (PNeg X)
    show ?case by (simp only: prename.simps psubst.simps PNeg.IH[where r=r and s=s])
  next
    case (PConj X Y)
    show ?case by (simp only: prename.simps psubst.simps PConj.IH(1)[where r=r and s=s] PConj.IH(2)[where r=r and s=s])
  next
    case (PDisj X Y)
    show ?case by (simp only: prename.simps psubst.simps PDisj.IH(1)[where r=r and s=s] PDisj.IH(2)[where r=r and s=s])
  next
    case (PImp X Y)
    show ?case by (simp only: prename.simps psubst.simps PImp.IH(1)[where r=r and s=s] PImp.IH(2)[where r=r and s=s])
  next
    case (PForall \<tau> X)
    show ?case by (simp only: prename.simps psubst.simps PForall.IH[where r="lift_ren r" and s="plift_subst s"] lifts)
  next
    case (PExists \<tau> X)
    show ?case by (simp only: prename.simps psubst.simps PExists.IH[where r="lift_ren r" and s="plift_subst s"] lifts)
  qed
qed

lemma pproof_psubst_lift_shift:
  "psubst (plift_subst s) (pshift M) = pshift (psubst s M)"
  by (simp add: pshift_def pproof_psubst_prename pproof_prename_psubst comp_def)

lemma pproof_prename_psubst0:
  "prename r (psubst0 T A) = psubst0 (prename r T) (prename (lift_ren r) A)"
proof -
  have maps: "(\<lambda>n. prename r (case_nat T PVar n)) = case_nat (prename r T) PVar \<circ> lift_ren r"
  proof (rule ext)
    fix n :: nat
    show "prename r (case_nat T PVar n) = (case_nat (prename r T) PVar \<circ> lift_ren r) n"
      by (cases n; simp)
  qed
  show ?thesis by (simp only: psubst0_def pproof_prename_psubst pproof_psubst_prename maps)
qed

end
