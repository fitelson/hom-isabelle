theory Bacon_Source_Reverse_Conversion
  imports Bacon_Source_Reverse_Binding
begin

section \<open>Target contraction steps become literal source contraction steps\<close>

text \<open>
  Reverse translation sends (λx.A)B →β A[B/x] and λx.Fx →η F
  to the corresponding source contractions.  It also preserves a single
  contracted occurrence inside every target term constructor.
  Source role: the contextual β and η patterns of Bacon--Dorr Figure 2,
  pp.7–8, in the reverse syntactic translation.

  Isabelle representation.  pterm_to_paper_subst0 and
  pterm_to_paper_shift identify the root patterns exactly.  Target
  logical constructors become application contexts; PForall/PExists
  additionally put the contracted occurrence beneath a source SLam.
  PImp retains the closed paper_imp_const wrapper and changes only
  the selected argument.
  Status.  These are raw directed syntactic steps, with no typing or
  signature premise.  They do not assert a guarded conversion theorem,
  H-proof reflection, or identity of primitive and defined implication.
\<close>

lemma pterm_to_paper_beta_root:
  assumes step: "pbeta_contract A B"
  shows "sbeta_contract (pterm_to_paper A) (pterm_to_paper B)"
  using step
  by (induction rule: pbeta_contract.induct)
    (simp only: pterm_to_paper.simps pterm_to_paper_subst0; rule sbeta_contract.beta)

lemma pterm_to_paper_eta_root:
  assumes step: "peta_contract A B"
  shows "seta_contract (pterm_to_paper A) (pterm_to_paper B)"
  using step
  by (induction rule: peta_contract.induct)
    (simp only: pterm_to_paper.simps pterm_to_paper_shift; rule seta_contract.eta)

lemma pterm_to_paper_compatible:
  fixes R :: "'c pterm \<Rightarrow> 'c pterm \<Rightarrow> bool"
    and Q :: "'c paper_term \<Rightarrow> 'c paper_term \<Rightarrow> bool"
  assumes step: "pcompatible_step R A B"
    and roots: "\<And>M N. R M N \<Longrightarrow> Q (pterm_to_paper M) (pterm_to_paper N)"
  shows "scompatible_step Q (pterm_to_paper A) (pterm_to_paper B)"
  using step
proof (induction rule: pcompatible_step.induct)
  case (root M N)
  show ?case by (rule scompatible_step.root[where R=Q, OF roots[OF root.hyps]])
next
  case App_left
  show ?case unfolding pterm_to_paper.simps by (rule scompatible_step.App_left[OF App_left.IH])
next
  case App_right
  show ?case unfolding pterm_to_paper.simps by (rule scompatible_step.App_right[OF App_right.IH])
next
  case Lam_body
  show ?case unfolding pterm_to_paper.simps by (rule scompatible_step.Lam_body[OF Lam_body.IH])
next
  case Eq_left
  show ?case unfolding pterm_to_paper.simps
    by (rule scompatible_step.App_left[OF scompatible_step.App_right[OF Eq_left.IH]])
next
  case Eq_right
  show ?case unfolding pterm_to_paper.simps by (rule scompatible_step.App_right[OF Eq_right.IH])
next
  case Neg_body
  show ?case unfolding pterm_to_paper.simps paper_not_def
    by (rule scompatible_step.App_right[OF Neg_body.IH])
next
  case Conj_left
  show ?case unfolding pterm_to_paper.simps paper_and_def
    by (rule scompatible_step.App_left[OF scompatible_step.App_right[OF Conj_left.IH]])
next
  case Conj_right
  show ?case unfolding pterm_to_paper.simps paper_and_def
    by (rule scompatible_step.App_right[OF Conj_right.IH])
next
  case Disj_left
  show ?case unfolding pterm_to_paper.simps paper_or_def
    by (rule scompatible_step.App_left[OF scompatible_step.App_right[OF Disj_left.IH]])
next
  case Disj_right
  show ?case unfolding pterm_to_paper.simps paper_or_def
    by (rule scompatible_step.App_right[OF Disj_right.IH])
next
  case Imp_left
  show ?case unfolding pterm_to_paper.simps paper_imp_def
    by (rule scompatible_step.App_left[OF scompatible_step.App_right[OF Imp_left.IH]])
next
  case Imp_right
  show ?case unfolding pterm_to_paper.simps paper_imp_def
    by (rule scompatible_step.App_right[OF Imp_right.IH])
next
  case Forall_body
  show ?case unfolding pterm_to_paper.simps
    by (rule scompatible_step.App_right[OF scompatible_step.Lam_body[OF Forall_body.IH]])
next
  case Exists_body
  show ?case unfolding pterm_to_paper.simps
    by (rule scompatible_step.App_right[OF scompatible_step.Lam_body[OF Exists_body.IH]])
qed

theorem pterm_to_paper_beta_step:
  assumes step: "pcompatible_step pbeta_contract A B"
  shows "scompatible_step sbeta_contract (pterm_to_paper A) (pterm_to_paper B)"
  by (rule pterm_to_paper_compatible[where R=pbeta_contract and Q=sbeta_contract,
    OF step pterm_to_paper_beta_root])

theorem pterm_to_paper_eta_step:
  assumes step: "pcompatible_step peta_contract A B"
  shows "scompatible_step seta_contract (pterm_to_paper A) (pterm_to_paper B)"
  by (rule pterm_to_paper_compatible[where R=peta_contract and Q=seta_contract,
    OF step pterm_to_paper_eta_root])

end
