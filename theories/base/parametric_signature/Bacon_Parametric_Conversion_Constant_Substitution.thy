theory Bacon_Parametric_Conversion_Constant_Substitution
  imports Bacon_Parametric_Conversion_Renaming
begin

section \<open>β and η under constant-to-term substitution\<close>

text \<open>
  Replacing c:σ by N in a conversion replaces N by its shift beneath
  each binder.  Source: Bacon–Dorr Figure 2, p.8; p.45 n.64.
  Each compatible-context rule is fully instantiated, including its
  unchanged surrounding terms.  No Functionality is involved.
\<close>

lemma pproof_beta_pconst:
  assumes step: "pbeta_contract A B"
  shows "pbeta_contract (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B)"
  using step
proof cases
  case (beta \<rho> M T)
  have redex: "pbeta_contract
      (PApp (PLam \<rho> (pconst_subst c \<sigma> (pshift N) M)) (pconst_subst c \<sigma> N T))
      (psubst0 (pconst_subst c \<sigma> N T) (pconst_subst c \<sigma> (pshift N) M))"
    by (rule pbeta_contract.beta)
  show ?thesis using beta redex by (simp add: pproof_pconst_psubst0)
qed

lemma pproof_eta_pconst:
  assumes step: "peta_contract A B"
  shows "peta_contract (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B)"
  using step
proof cases
  case (eta \<rho>)
  have redex: "peta_contract (PLam \<rho> (PApp (pshift (pconst_subst c \<sigma> N B)) (PVar 0)))
      (pconst_subst c \<sigma> N B)" by (rule peta_contract.eta)
  show ?thesis using eta redex by (simp add: pproof_pconst_shift)
qed

lemma pproof_compatible_pconst:
  assumes step: "pcompatible_step R A B"
    and roots: "\<And>N X Y. R X Y \<Longrightarrow> R (pconst_subst c \<sigma> N X) (pconst_subst c \<sigma> N Y)"
  shows "pcompatible_step R (pconst_subst c \<sigma> N A) (pconst_subst c \<sigma> N B)"
  using step
proof (induction arbitrary: N rule: pcompatible_step.induct)
  case (root X Y)
  show ?case by (rule pcompatible_step.root[where R=R and M="pconst_subst c \<sigma> N X"
    and N="pconst_subst c \<sigma> N Y", OF roots[where N=N and X=X and Y=Y, OF root.hyps]])
next
  case (App_left X Y Z)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.App_left[where R=R and M="pconst_subst c \<sigma> N X" and M'="pconst_subst c \<sigma> N Y" and N="pconst_subst c \<sigma> N Z",
      OF App_left.IH[where N="N"]])
next
  case (App_right X Y Z)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.App_right[where R=R and N="pconst_subst c \<sigma> N X" and N'="pconst_subst c \<sigma> N Y" and M="pconst_subst c \<sigma> N Z",
      OF App_right.IH[where N="N"]])
next
  case (Lam_body X Y \<tau>)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.Lam_body[where R=R and M="pconst_subst c \<sigma> (pshift N) X" and M'="pconst_subst c \<sigma> (pshift N) Y" and \<sigma>="\<tau>",
      OF Lam_body.IH[where N="pshift N"]])
next
  case (Eq_left X Y \<tau> Z)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.Eq_left[where R=R and M="pconst_subst c \<sigma> N X" and M'="pconst_subst c \<sigma> N Y" and \<sigma>="\<tau>" and N="pconst_subst c \<sigma> N Z",
      OF Eq_left.IH[where N="N"]])
next
  case (Eq_right X Y \<tau> Z)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.Eq_right[where R=R and N="pconst_subst c \<sigma> N X" and N'="pconst_subst c \<sigma> N Y" and \<sigma>="\<tau>" and M="pconst_subst c \<sigma> N Z",
      OF Eq_right.IH[where N="N"]])
next
  case (Neg_body X Y)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.Neg_body[where R=R and A="pconst_subst c \<sigma> N X" and A'="pconst_subst c \<sigma> N Y",
      OF Neg_body.IH[where N="N"]])
next
  case (Conj_left X Y Z)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.Conj_left[where R=R and A="pconst_subst c \<sigma> N X" and A'="pconst_subst c \<sigma> N Y" and B="pconst_subst c \<sigma> N Z",
      OF Conj_left.IH[where N="N"]])
next
  case (Conj_right X Y Z)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.Conj_right[where R=R and B="pconst_subst c \<sigma> N X" and B'="pconst_subst c \<sigma> N Y" and A="pconst_subst c \<sigma> N Z",
      OF Conj_right.IH[where N="N"]])
next
  case (Disj_left X Y Z)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.Disj_left[where R=R and A="pconst_subst c \<sigma> N X" and A'="pconst_subst c \<sigma> N Y" and B="pconst_subst c \<sigma> N Z",
      OF Disj_left.IH[where N="N"]])
next
  case (Disj_right X Y Z)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.Disj_right[where R=R and B="pconst_subst c \<sigma> N X" and B'="pconst_subst c \<sigma> N Y" and A="pconst_subst c \<sigma> N Z",
      OF Disj_right.IH[where N="N"]])
next
  case (Imp_left X Y Z)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.Imp_left[where R=R and A="pconst_subst c \<sigma> N X" and A'="pconst_subst c \<sigma> N Y" and B="pconst_subst c \<sigma> N Z",
      OF Imp_left.IH[where N="N"]])
next
  case (Imp_right X Y Z)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.Imp_right[where R=R and B="pconst_subst c \<sigma> N X" and B'="pconst_subst c \<sigma> N Y" and A="pconst_subst c \<sigma> N Z",
      OF Imp_right.IH[where N="N"]])
next
  case (Forall_body X Y \<tau>)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.Forall_body[where R=R and A="pconst_subst c \<sigma> (pshift N) X" and A'="pconst_subst c \<sigma> (pshift N) Y" and \<sigma>="\<tau>",
      OF Forall_body.IH[where N="pshift N"]])
next
  case (Exists_body X Y \<tau>)
  show ?case by (simp only: pconst_subst.simps)
    (rule pcompatible_step.Exists_body[where R=R and A="pconst_subst c \<sigma> (pshift N) X" and A'="pconst_subst c \<sigma> (pshift N) Y" and \<sigma>="\<tau>",
      OF Exists_body.IH[where N="pshift N"]])
qed

end
