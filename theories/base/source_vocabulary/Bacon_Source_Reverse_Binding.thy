theory Bacon_Source_Reverse_Binding
  imports Bacon_Source_Reverse_Syntax Bacon_Source_Closing_Structure
begin

section \<open>Reverse translation commutes with capture-avoiding binding\<close>

text \<open>
  Re-expressing a target term in the paper language commutes with variable
  renaming, simultaneous substitution, and substitution for a bound slot.
  Source role: capture-avoiding operations in Bacon–Dorr §1.1 and Figure 2,
  pp.5–8, for the reverse syntactic translation.

  Isabelle representation.  pterm_to_paper expands PImp using the literal
  closed λpq.¬p ∨ q term paper_imp_const.  Substitution preserves that
  wrapper, replacing only the translated arguments.  PForall and PExists
  use first-class quantifier constants applied to SLam bodies; the lifting
  lemma below checks that these new binders capture no substituted slots.

  Status: exact syntax equalities and free-slot correspondence, with no
  typing or model premises.  There is no identity between primitive and
  defined implication, no claimed inverse equation between the two syntax
  translations, and no proof-reflection theorem in this leaf.
\<close>

lemma srename_paper_imp_const:
  "srename r (paper_imp_const :: 'c paper_term) = paper_imp_const"
  by (simp add: paper_imp_const_def paper_or_def paper_not_def)

lemma ssubst_paper_imp_const:
  "ssubst s (paper_imp_const :: 'c paper_term) = paper_imp_const"
  by (simp add: paper_imp_const_def paper_or_def paper_not_def)

lemma ssubst_paper_imp:
  "ssubst s (paper_imp A B) = paper_imp (ssubst s A) (ssubst s B)"
  by (simp only: paper_imp_def ssubst.simps ssubst_paper_imp_const)

lemma pterm_to_paper_rename:
  "pterm_to_paper (prename r A) = srename r (pterm_to_paper A)"
  by (induction A arbitrary: r)
    (simp_all add: paper_not_def paper_and_def paper_or_def srename_paper_imp)

lemma pterm_to_paper_shift:
  "pterm_to_paper (pshift A) = sshift (pterm_to_paper A)"
  by (simp only: pshift_def sshift_def pterm_to_paper_rename)

lemma pterm_to_paper_lift:
  "(\<lambda>n. pterm_to_paper (plift_subst s n)) = slift_subst (\<lambda>n. pterm_to_paper (s n))"
proof (rule ext)
  fix n
  show "pterm_to_paper (plift_subst s n) = slift_subst (\<lambda>n. pterm_to_paper (s n)) n"
    by (cases n) (simp_all only: plift_subst.simps slift_subst.simps
      pterm_to_paper.simps pterm_to_paper_rename)
qed

lemma pterm_to_paper_subst:
  "pterm_to_paper (psubst s A) = ssubst (\<lambda>n. pterm_to_paper (s n)) (pterm_to_paper A)"
proof (induction A arbitrary: s)
  case (PVar n)
  show ?case by (simp only: psubst.simps pterm_to_paper.simps ssubst.simps)
next
  case (PConst c \<sigma>)
  show ?case by (simp only: psubst.simps pterm_to_paper.simps ssubst.simps)
next
  case (PApp F A)
  show ?case by (simp only: psubst.simps pterm_to_paper.simps ssubst.simps PApp.IH)
next
  case (PLam \<sigma> A)
  show ?case by (simp only: psubst.simps pterm_to_paper.simps ssubst.simps
    PLam.IH[where s="plift_subst s"] pterm_to_paper_lift)
next
  case (PEq \<sigma> A B)
  show ?case by (simp only: psubst.simps pterm_to_paper.simps ssubst.simps PEq.IH)
next
  case (PNeg A)
  show ?case by (simp only: psubst.simps pterm_to_paper.simps paper_not_def ssubst.simps PNeg.IH)
next
  case (PConj A B)
  show ?case by (simp only: psubst.simps pterm_to_paper.simps paper_and_def ssubst.simps PConj.IH)
next
  case (PDisj A B)
  show ?case by (simp only: psubst.simps pterm_to_paper.simps paper_or_def ssubst.simps PDisj.IH)
next
  case (PImp A B)
  show ?case by (simp only: psubst.simps pterm_to_paper.simps ssubst_paper_imp PImp.IH)
next
  case (PForall \<sigma> A)
  show ?case by (simp only: psubst.simps pterm_to_paper.simps ssubst.simps
    PForall.IH[where s="plift_subst s"] pterm_to_paper_lift)
next
  case (PExists \<sigma> A)
  show ?case by (simp only: psubst.simps pterm_to_paper.simps ssubst.simps
    PExists.IH[where s="plift_subst s"] pterm_to_paper_lift)
qed

lemma pterm_to_paper_subst0:
  "pterm_to_paper (psubst0 T A) = ssubst0 (pterm_to_paper T) (pterm_to_paper A)"
proof -
  have maps: "(\<lambda>n. pterm_to_paper (case_nat T PVar n)) = case_nat (pterm_to_paper T) SVar"
    by (rule ext, rename_tac n, case_tac n) simp_all
  show ?thesis by (simp only: psubst0_def ssubst0_def pterm_to_paper_subst maps)
qed

lemma pterm_to_paper_close:
  "pterm_to_paper (prename (\<lambda>k. if k = n then 0 else Suc k) A) = sclose n (pterm_to_paper A)"
  by (simp only: sclose_def pterm_to_paper_rename)

subsection \<open>The literal implication wrapper contributes no free variables\<close>

lemma sfv_paper_imp_const:
  "sfv (paper_imp_const :: 'c paper_term) = {}"
  by (auto simp: paper_imp_const_def paper_or_def paper_not_def)

lemma sfv_paper_imp:
  "sfv (paper_imp A B) = sfv A \<union> sfv B"
  by (simp only: paper_imp_def sfv.simps sfv_paper_imp_const Un_empty_left)

theorem pterm_to_paper_fv:
  "sfv (pterm_to_paper A) = pbbk_fv A"
  by (induction A)
    (simp_all add: paper_not_def paper_and_def paper_or_def sfv_paper_imp)

end
