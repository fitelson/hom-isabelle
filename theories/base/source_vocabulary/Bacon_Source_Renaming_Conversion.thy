theory Bacon_Source_Renaming_Conversion
  imports Bacon_Source_Conversion
begin

section \<open>Source β and η steps under capture-avoiding renaming\<close>

text \<open>
  Renaming free variables commutes with A[T/v] when the renaming is lifted
  beneath the binder.  Consequently, renaming a contextual β or η step
  yields a step of the same kind.  Source: Bacon–Dorr §1.1 and Figure 2,
  pp.5–8; the same structural convention underlies closing and opening
  an existing source variable.

  Isabelle representation.  Every renaming r fixes the new bound slot
  through lift_ren r.  The β image has body srename(lift_ren r) A and
  argument srename r T.  The η image uses the proved equation
  srename(lift_ren r)(sshift F) = sshift(srename r F).
  No injectivity or typing is needed for these raw syntactic equations
  and step relations.  This does not itself assert source theoremhood,
  proof reflection, or semantic invariance.
\<close>

lemma slift_ren_comp:
  "lift_ren r \<circ> lift_ren s = lift_ren (r \<circ> s)"
  by (rule ext, rename_tac n, case_tac n) (simp_all add: comp_def)

lemma srename_comp:
  "srename r (srename s A) = srename (r \<circ> s) A"
proof (induction A arbitrary: r s)
  case (SVar n)
  show ?case by (simp only: srename.simps comp_def)
next
  case (SConst c \<sigma>)
  show ?case by (simp only: srename.simps)
next
  case (SLogical l)
  show ?case by (simp only: srename.simps)
next
  case (SApp M N)
  show ?case by (simp only: srename.simps SApp.IH)
next
  case (SLam \<sigma> A)
  show ?case by (simp only: srename.simps
    SLam.IH[where r="lift_ren r" and s="lift_ren s"] slift_ren_comp)
qed

lemma srename_lift_shift:
  "srename (lift_ren r) (sshift A) = sshift (srename r A)"
proof -
  have maps: "lift_ren r \<circ> Suc = Suc \<circ> r" by (rule ext) simp
  show ?thesis by (simp only: sshift_def srename_comp maps)
qed

lemma slift_subst_ren_comp:
  "slift_subst s \<circ> lift_ren r = slift_subst (s \<circ> r)"
  by (rule ext, rename_tac n, case_tac n) (simp_all add: comp_def)

lemma ssubst_srename:
  "ssubst s (srename r A) = ssubst (s \<circ> r) A"
proof (induction A arbitrary: s r)
  case (SVar n)
  show ?case by (simp only: srename.simps ssubst.simps comp_def)
next
  case (SConst c \<sigma>)
  show ?case by (simp only: srename.simps ssubst.simps)
next
  case (SLogical l)
  show ?case by (simp only: srename.simps ssubst.simps)
next
  case (SApp M N)
  show ?case by (simp only: srename.simps ssubst.simps SApp.IH)
next
  case (SLam \<sigma> A)
  show ?case by (simp only: srename.simps ssubst.simps
    SLam.IH[where s="slift_subst s" and r="lift_ren r"] slift_subst_ren_comp)
qed

lemma srename_slift_subst:
  "(\<lambda>n. srename (lift_ren r) (slift_subst s n)) = slift_subst (\<lambda>n. srename r (s n))"
  by (rule ext, rename_tac n, case_tac n)
    (simp_all add: srename_lift_shift[unfolded sshift_def])

lemma srename_ssubst:
  "srename r (ssubst s A) = ssubst (\<lambda>n. srename r (s n)) A"
proof (induction A arbitrary: r s)
  case (SVar n)
  show ?case by (simp only: srename.simps ssubst.simps)
next
  case (SConst c \<sigma>)
  show ?case by (simp only: srename.simps ssubst.simps)
next
  case (SLogical l)
  show ?case by (simp only: srename.simps ssubst.simps)
next
  case (SApp M N)
  show ?case by (simp only: srename.simps ssubst.simps SApp.IH)
next
  case (SLam \<sigma> A)
  show ?case by (simp only: srename.simps ssubst.simps
    SLam.IH[where r="lift_ren r" and s="slift_subst s"] srename_slift_subst)
qed

lemma srename_ssubst0:
  "srename r (ssubst0 T A) = ssubst0 (srename r T) (srename (lift_ren r) A)"
proof -
  have maps: "(\<lambda>n. srename r (case_nat T SVar n)) = case_nat (srename r T) SVar \<circ> lift_ren r"
    by (rule ext, rename_tac n, case_tac n) (simp_all add: comp_def)
  show ?thesis by (simp only: ssubst0_def srename_ssubst ssubst_srename maps)
qed

subsection \<open>Root contractions and their compatible contexts\<close>

lemma srename_beta:
  assumes step: "sbeta_contract A B"
  shows "sbeta_contract (srename r A) (srename r B)"
  using step by cases (simp only: srename.simps srename_ssubst0; rule sbeta_contract.beta)

lemma srename_eta:
  assumes step: "seta_contract A B"
  shows "seta_contract (srename r A) (srename r B)"
  using step by cases (simp only: srename.simps lift_ren.simps srename_lift_shift; rule seta_contract.eta)

lemma srename_compatible:
  assumes step: "scompatible_step R A B"
    and roots: "\<And>r X Y. R X Y \<Longrightarrow> R (srename r X) (srename r Y)"
  shows "scompatible_step R (srename r A) (srename r B)"
  using step
proof (induction arbitrary: r rule: scompatible_step.induct)
  case (root X Y)
  have renamed: "R (srename r X) (srename r Y)" by (rule roots[where r=r and X=X and Y=Y, OF root.hyps])
  show ?case by (rule scompatible_step.root[where R=R and M="srename r X" and N="srename r Y", OF renamed])
next
  case (App_left X Y Z)
  show ?case by (simp only: srename.simps)
    (rule scompatible_step.App_left[where R=R and M="srename r X" and M'="srename r Y" and N="srename r Z",
      OF App_left.IH[where r=r]])
next
  case (App_right X Y Z)
  show ?case by (simp only: srename.simps)
    (rule scompatible_step.App_right[where R=R and N="srename r X" and N'="srename r Y" and M="srename r Z",
      OF App_right.IH[where r=r]])
next
  case (Lam_body X Y \<sigma>)
  show ?case by (simp only: srename.simps)
    (rule scompatible_step.Lam_body[where R=R and M="srename (lift_ren r) X"
      and M'="srename (lift_ren r) Y" and \<sigma>=\<sigma>, OF Lam_body.IH[where r="lift_ren r"]])
qed

lemma srename_beta_step:
  "scompatible_step sbeta_contract A B \<Longrightarrow>
    scompatible_step sbeta_contract (srename r A) (srename r B)"
  by (rule srename_compatible[where R=sbeta_contract], assumption, rule srename_beta, assumption)

lemma srename_eta_step:
  "scompatible_step seta_contract A B \<Longrightarrow>
    scompatible_step seta_contract (srename r A) (srename r B)"
  by (rule srename_compatible[where R=seta_contract], assumption, rule srename_eta, assumption)

end
