theory Bacon_Parametric_Conversion_Substitution
  imports Bacon_Parametric_Conversion_Constant_Substitution
begin

section \<open>Propositional tautologies under substitution\<close>

text \<open>
  Propositional tautologies remain tautologies after the preceding
  renaming and constant-substitution operations.  Source: Bacon–Dorr
  Figure 2, p.8, PC.  The conversion results are imported from the two
  smaller predecessor theories and re-exported below with their stable names.
\<close>

lemma pproof_prop_eval_prename:
  "pprop_eval v (prename r A) = pprop_eval (\<lambda>B. v (prename r B)) A"
proof (induction A)
  case (PVar n)
  show ?case by (simp only: prename.simps pprop_eval.simps)
next
  case (PConst d \<tau>)
  show ?case by (simp only: prename.simps pprop_eval.simps)
next
  case (PApp X Y)
  show ?case by (simp only: prename.simps pprop_eval.simps)
next
  case (PLam \<tau> X)
  show ?case by (simp only: prename.simps pprop_eval.simps)
next
  case (PEq \<tau> X Y)
  show ?case by (simp only: prename.simps pprop_eval.simps)
next
  case (PNeg X)
  show ?case by (simp only: prename.simps pprop_eval.simps PNeg.IH)
next
  case (PConj X Y)
  show ?case by (simp only: prename.simps pprop_eval.simps PConj.IH)
next
  case (PDisj X Y)
  show ?case by (simp only: prename.simps pprop_eval.simps PDisj.IH)
next
  case (PImp X Y)
  show ?case by (simp only: prename.simps pprop_eval.simps PImp.IH)
next
  case (PForall \<tau> X)
  show ?case by (simp only: prename.simps pprop_eval.simps)
next
  case (PExists \<tau> X)
  show ?case by (simp only: prename.simps pprop_eval.simps)
qed

lemma pproof_prop_eval_pconst:
  "pprop_eval v (pconst_subst c \<sigma> N A) = pprop_eval (\<lambda>B. pprop_eval v (pconst_subst c \<sigma> N B)) A"
proof (induction A)
  case (PVar n)
  show ?case by (simp only: pconst_subst.simps pprop_eval.simps)
next
  case (PConst d \<tau>)
  show ?case by (simp only: pconst_subst.simps pprop_eval.simps)
next
  case (PApp X Y)
  show ?case by (simp only: pconst_subst.simps pprop_eval.simps)
next
  case (PLam \<tau> X)
  show ?case by (simp only: pconst_subst.simps pprop_eval.simps)
next
  case (PEq \<tau> X Y)
  show ?case by (simp only: pconst_subst.simps pprop_eval.simps)
next
  case (PNeg X)
  show ?case by (simp only: pconst_subst.simps pprop_eval.simps PNeg.IH)
next
  case (PConj X Y)
  show ?case by (simp only: pconst_subst.simps pprop_eval.simps PConj.IH)
next
  case (PDisj X Y)
  show ?case by (simp only: pconst_subst.simps pprop_eval.simps PDisj.IH)
next
  case (PImp X Y)
  show ?case by (simp only: pconst_subst.simps pprop_eval.simps PImp.IH)
next
  case (PForall \<tau> X)
  show ?case by (simp only: pconst_subst.simps pprop_eval.simps)
next
  case (PExists \<tau> X)
  show ?case by (simp only: pconst_subst.simps pprop_eval.simps)
qed

lemma pproof_taut_prename:
  assumes taut: "pprop_tautology \<Gamma> A"
    and ren: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>"
  shows "pprop_tautology \<Delta> (prename r A)"
proof -
  have data: "has_ptype \<Gamma> A Prop \<and> (\<forall>v. pprop_eval v A)"
    using taut unfolding pprop_tautology_def .
  have typed: "has_ptype \<Delta> (prename r A) Prop"
    by (rule prename_preserves_typing[OF conjunct1[OF data] ren])
  have all_truth: "\<forall>v. pprop_eval v (prename r A)"
  proof (rule allI)
    fix v
    have original: "pprop_eval (\<lambda>B. v (prename r B)) A"
      by (rule spec[where x="\<lambda>B. v (prename r B)", OF conjunct2[OF data]])
    show "pprop_eval v (prename r A)" by (simp only: pproof_prop_eval_prename original)
  qed
  show ?thesis unfolding pprop_tautology_def by (rule conjI[OF typed all_truth])
qed

lemma pproof_taut_pconst:
  assumes "pprop_tautology \<Gamma> A" and "has_ptype \<Gamma> N \<sigma>"
  shows "pprop_tautology \<Gamma> (pconst_subst c \<sigma> N A)"
proof -
  have data: "has_ptype \<Gamma> A Prop \<and> (\<forall>v. pprop_eval v A)"
    using assms(1) unfolding pprop_tautology_def .
  have typed: "has_ptype \<Gamma> (pconst_subst c \<sigma> N A) Prop"
    by (rule pconst_subst_type[OF conjunct1[OF data] assms(2)])
  have all_truth: "\<forall>v. pprop_eval v (pconst_subst c \<sigma> N A)"
  proof (rule allI)
    fix v
    have original: "pprop_eval (\<lambda>B. pprop_eval v (pconst_subst c \<sigma> N B)) A"
      by (rule spec[where x="\<lambda>B. pprop_eval v (pconst_subst c \<sigma> N B)", OF conjunct2[OF data]])
    have evaluated: "pprop_eval v (pconst_subst c \<sigma> N A) =
        pprop_eval (\<lambda>B. pprop_eval v (pconst_subst c \<sigma> N B)) A"
      by (rule pproof_prop_eval_pconst)
    show "pprop_eval v (pconst_subst c \<sigma> N A)"
      by (rule iffD2[OF evaluated original])
  qed
  show ?thesis unfolding pprop_tautology_def by (rule conjI[OF typed all_truth])
qed

subsection \<open>Stable names for conversion transport\<close>

lemmas pproof_beta_prename = Bacon_Parametric_Conversion_Renaming.pproof_beta_prename
lemmas pproof_eta_prename = Bacon_Parametric_Conversion_Renaming.pproof_eta_prename
lemmas pproof_compatible_prename = Bacon_Parametric_Conversion_Renaming.pproof_compatible_prename
lemmas pproof_beta_pconst = Bacon_Parametric_Conversion_Constant_Substitution.pproof_beta_pconst
lemmas pproof_eta_pconst = Bacon_Parametric_Conversion_Constant_Substitution.pproof_eta_pconst
lemmas pproof_compatible_pconst = Bacon_Parametric_Conversion_Constant_Substitution.pproof_compatible_pconst

end
