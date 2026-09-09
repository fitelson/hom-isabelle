theory Bacon_Source_Named_Alpha_Conversion
  imports Bacon_Source_Named_Binder_Conversion
begin

section \<open>The generated α relation is derivable using only literal βη\<close>

text \<open>
  If y ∉ Vars(A) and G(x) = G(y), then
  A[y/x] ≡βη (x y)·A and λx.A ≡βη λy.(x y)·A.
  Source: Bacon–Dorr Figure 2, pp.7–8; these consequences require no
  additional α rule in the conversion clause of Definition 3.1(ii.d).

  Isabelle representation. The paired induction is staged: an alignment
  for a body yields its binder conversion by the preceding η/β helper.
  When alignment meets λx.C, substitution stops and the required result
  is that binder conversion for the strict subterm C. Other binders use
  alignment below the same binder. Thus the induction does not assume
  the general α-to-βη conclusion that it will establish.

  Status. Arbitrary name and logical-symbol carriers, fixed G, and exact
  typing/signature guards. Richness, representation equality, H proofs,
  and semantic assumptions are not required. This derives α invariance
  from a separately defined conversion relation containing no α rule.
\<close>

lemma named_alpha_conversion_app_parts:
  assumes language: "named_in_language L \<Sigma> G (NApp F A) \<tau>"
  obtains \<sigma> where "named_in_language L \<Sigma> G F (Arr \<sigma> \<tau>)"
    and "named_in_language L \<Sigma> G A \<sigma>"
  using language unfolding named_in_language_def named_app_type_iff
    named_in_signature.simps by blast

lemma named_alpha_conversion_lam_parts:
  assumes language: "named_in_language L \<Sigma> G (NLam n A) \<tau>"
  obtains \<rho> where "\<tau> = Arr (G n) \<rho>" and "named_in_language L \<Sigma> G A \<rho>"
  using language unfolding named_in_language_def named_lam_type_iff
    named_in_signature.simps by blast

theorem named_subst_swap_conversion:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
    and same: "G x = G y" and fresh: "y \<notin> named_vars A"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau>
    (named_subst x (NVar y) A) (named_swap x y A)"
  using language same fresh
proof (induction A arbitrary: x y \<tau>)
  case (NVar n)
  have same_term: "named_subst x (NVar y) (NVar n) = named_swap x y (NVar n)"
    using NVar.prems(3) by (auto simp: named_swap_index_def)
  have swapped: "named_in_language L \<Sigma> G (named_swap x y (NVar n)) \<tau>"
    by (rule named_conversion_swap_language[OF NVar.prems(1,2)])
  show ?case by (simp only: same_term; rule named_beta_eta_in_language.Refl[OF swapped])
next
  case (NConst c \<sigma>)
  show ?case by (simp only: named_subst.simps named_swap.simps;
    rule named_beta_eta_in_language.Refl[OF NConst.prems(1)])
next
  case (NLogical l)
  show ?case by (simp only: named_subst.simps named_swap.simps;
    rule named_beta_eta_in_language.Refl[OF NLogical.prems(1)])
next
  case (NApp F A)
  obtain \<sigma> where fn: "named_in_language L \<Sigma> G F (Arr \<sigma> \<tau>)"
    and arg: "named_in_language L \<Sigma> G A \<sigma>"
    by (rule named_alpha_conversion_app_parts[OF NApp.prems(1)])
  have fresh_F: "y \<notin> named_vars F" and fresh_A: "y \<notin> named_vars A"
    using NApp.prems(3) by simp_all
  have fc: "named_beta_eta_in_language L \<Sigma> G (Arr \<sigma> \<tau>)
    (named_subst x (NVar y) F) (named_swap x y F)"
    by (rule NApp.IH(1)[OF fn NApp.prems(2) fresh_F])
  have ac: "named_beta_eta_in_language L \<Sigma> G \<sigma>
    (named_subst x (NVar y) A) (named_swap x y A)"
    by (rule NApp.IH(2)[OF arg NApp.prems(2) fresh_A])
  show ?case by (simp only: named_subst.simps named_swap.simps;
    rule named_conversion_App[OF fc ac])
next
  case (NLam n A)
  obtain \<rho> where ty: "\<tau> = Arr (G n) \<rho>" and body: "named_in_language L \<Sigma> G A \<rho>"
    by (rule named_alpha_conversion_lam_parts[OF NLam.prems(1)])
  have fresh_body: "y \<notin> named_vars A" and not_y: "n \<noteq> y"
    using NLam.prems(3) by auto
  have aligned: "named_beta_eta_in_language L \<Sigma> G \<rho>
    (named_subst x (NVar y) A) (named_swap x y A)"
    by (rule NLam.IH[OF body NLam.prems(2) fresh_body])
  show ?case
  proof (cases "n = x")
    case True
    have shadow: "named_beta_eta_in_language L \<Sigma> G (Arr (G x) \<rho>)
      (NLam x A) (NLam y (named_swap x y A))"
      by (rule named_binder_conversion_from_alignment[OF body NLam.prems(2) fresh_body aligned])
    show ?thesis using shadow
      by (simp add: ty True)
  next
    case False
    have binder_index: "named_swap_index x y n = n"
      by (simp only: named_swap_index_def False not_y if_False)
    have under_binder: "named_beta_eta_in_language L \<Sigma> G (Arr (G n) \<rho>)
      (NLam n (named_subst x (NVar y) A)) (NLam n (named_swap x y A))"
      by (rule named_conversion_Lam[OF aligned])
    show ?thesis using under_binder
      by (simp only: ty named_subst.simps False if_False named_swap.simps binder_index)
  qed
qed

corollary named_fresh_binder_conversion:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
    and same: "G x = G y" and fresh: "y \<notin> named_vars A"
  shows "named_beta_eta_in_language L \<Sigma> G (Arr (G x) \<tau>)
    (NLam x A) (NLam y (named_swap x y A))"
  by (rule named_binder_conversion_from_alignment[OF language same fresh
    named_subst_swap_conversion[OF language same fresh]])

section \<open>Induction over the independent α generators\<close>

theorem named_alpha_implies_beta_eta:
  assumes alpha: "named_alpha G A B" and language: "named_in_language L \<Sigma> G A \<tau>"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> A B"
  using alpha language
proof (induction arbitrary: \<tau> rule: named_alpha.induct)
  case Refl
  show ?case by (rule named_beta_eta_in_language.Refl[OF Refl.prems])
next
  case (Fresh_Binder x y A)
  obtain \<rho> where ty: "\<tau> = Arr (G x) \<rho>" and body: "named_in_language L \<Sigma> G A \<rho>"
    by (rule named_alpha_conversion_lam_parts[OF Fresh_Binder.prems])
  show ?case unfolding ty
    by (rule named_fresh_binder_conversion[OF body Fresh_Binder.hyps])
next
  case (App F H A B)
  obtain \<sigma> where fn: "named_in_language L \<Sigma> G F (Arr \<sigma> \<tau>)"
    and arg: "named_in_language L \<Sigma> G A \<sigma>"
    by (rule named_alpha_conversion_app_parts[OF App.prems])
  show ?case by (rule named_conversion_App[OF App.IH(1)[OF fn] App.IH(2)[OF arg]])
next
  case (Lam A B n)
  obtain \<rho> where ty: "\<tau> = Arr (G n) \<rho>" and body: "named_in_language L \<Sigma> G A \<rho>"
    by (rule named_alpha_conversion_lam_parts[OF Lam.prems])
  show ?case unfolding ty by (rule named_conversion_Lam[OF Lam.IH[OF body]])
next
  case (Sym A B)
  have left: "named_in_language L \<Sigma> G A \<tau>"
    by (rule iffD2[OF named_alpha_language_iff[OF Sym.hyps] Sym.prems])
  show ?case by (rule named_beta_eta_in_language.Sym[OF Sym.IH[OF left]])
next
  case (Trans A B C)
  have first: "named_beta_eta_in_language L \<Sigma> G \<tau> A B"
    by (rule Trans.IH(1)[OF Trans.prems])
  have middle: "named_in_language L \<Sigma> G B \<tau>"
    by (rule conjunct2[OF named_beta_eta_languages[OF first]])
  have second: "named_beta_eta_in_language L \<Sigma> G \<tau> B C"
    by (rule Trans.IH(2)[OF middle])
  show ?case by (rule named_beta_eta_in_language.Trans[OF first second])
qed

end
