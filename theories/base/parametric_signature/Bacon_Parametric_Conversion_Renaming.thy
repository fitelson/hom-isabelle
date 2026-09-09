theory Bacon_Parametric_Conversion_Renaming
  imports Bacon_Parametric_Constant_Substitution_Algebra
begin

section \<open>β and η under free-variable renaming\<close>

text \<open>
  A →β B or A →η B remains a conversion after a type-respecting renaming.
  Source: Bacon–Dorr Figure 2, p.8.  Under λ, ∀, and ∃ the variable map
  is lifted to preserve the new bound slot.  Each compatible-context rule
  below fixes its relation, operands, and binder type before application.
\<close>

lemma pproof_beta_prename:
  assumes step: "pbeta_contract A B"
  shows "pbeta_contract (prename r A) (prename r B)"
  using step
proof cases
  case (beta \<rho> M T)
  have redex: "pbeta_contract (PApp (PLam \<rho> (prename (lift_ren r) M)) (prename r T))
      (psubst0 (prename r T) (prename (lift_ren r) M))" by (rule pbeta_contract.beta)
  show ?thesis using beta redex by (simp add: pproof_prename_psubst0)
qed

lemma pproof_eta_prename:
  assumes step: "peta_contract A B"
  shows "peta_contract (prename r A) (prename r B)"
  using step
proof cases
  case (eta \<rho>)
  have redex: "peta_contract (PLam \<rho> (PApp (pshift (prename r B)) (PVar 0))) (prename r B)"
    by (rule peta_contract.eta)
  show ?thesis using eta redex by (simp add: pproof_prename_lift_shift)
qed

lemma pproof_compatible_prename:
  assumes step: "pcompatible_step R A B"
    and roots: "\<And>r X Y. R X Y \<Longrightarrow> R (prename r X) (prename r Y)"
  shows "pcompatible_step R (prename r A) (prename r B)"
  using step
proof (induction arbitrary: r rule: pcompatible_step.induct)
  case (root X Y)
  show ?case by (rule pcompatible_step.root[where R=R and M="prename r X" and N="prename r Y",
    OF roots[where r=r and X=X and Y=Y, OF root.hyps]])
next
  case (App_left X Y Z)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.App_left[where R=R and M="prename r X" and M'="prename r Y" and N="prename r Z",
      OF App_left.IH[where r="r"]])
next
  case (App_right X Y Z)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.App_right[where R=R and N="prename r X" and N'="prename r Y" and M="prename r Z",
      OF App_right.IH[where r="r"]])
next
  case (Lam_body X Y \<tau>)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.Lam_body[where R=R and M="prename (lift_ren r) X" and M'="prename (lift_ren r) Y" and \<sigma>="\<tau>",
      OF Lam_body.IH[where r="lift_ren r"]])
next
  case (Eq_left X Y \<tau> Z)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.Eq_left[where R=R and M="prename r X" and M'="prename r Y" and \<sigma>="\<tau>" and N="prename r Z",
      OF Eq_left.IH[where r="r"]])
next
  case (Eq_right X Y \<tau> Z)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.Eq_right[where R=R and N="prename r X" and N'="prename r Y" and \<sigma>="\<tau>" and M="prename r Z",
      OF Eq_right.IH[where r="r"]])
next
  case (Neg_body X Y)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.Neg_body[where R=R and A="prename r X" and A'="prename r Y",
      OF Neg_body.IH[where r="r"]])
next
  case (Conj_left X Y Z)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.Conj_left[where R=R and A="prename r X" and A'="prename r Y" and B="prename r Z",
      OF Conj_left.IH[where r="r"]])
next
  case (Conj_right X Y Z)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.Conj_right[where R=R and B="prename r X" and B'="prename r Y" and A="prename r Z",
      OF Conj_right.IH[where r="r"]])
next
  case (Disj_left X Y Z)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.Disj_left[where R=R and A="prename r X" and A'="prename r Y" and B="prename r Z",
      OF Disj_left.IH[where r="r"]])
next
  case (Disj_right X Y Z)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.Disj_right[where R=R and B="prename r X" and B'="prename r Y" and A="prename r Z",
      OF Disj_right.IH[where r="r"]])
next
  case (Imp_left X Y Z)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.Imp_left[where R=R and A="prename r X" and A'="prename r Y" and B="prename r Z",
      OF Imp_left.IH[where r="r"]])
next
  case (Imp_right X Y Z)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.Imp_right[where R=R and B="prename r X" and B'="prename r Y" and A="prename r Z",
      OF Imp_right.IH[where r="r"]])
next
  case (Forall_body X Y \<tau>)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.Forall_body[where R=R and A="prename (lift_ren r) X" and A'="prename (lift_ren r) Y" and \<sigma>="\<tau>",
      OF Forall_body.IH[where r="lift_ren r"]])
next
  case (Exists_body X Y \<tau>)
  show ?case by (simp only: prename.simps)
    (rule pcompatible_step.Exists_body[where R=R and A="prename (lift_ren r) X" and A'="prename (lift_ren r) Y" and \<sigma>="\<tau>",
      OF Exists_body.IH[where r="lift_ren r"]])
qed

end
