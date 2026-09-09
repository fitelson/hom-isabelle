theory Bacon_Source_Named_Alpha
  imports Bacon_Source_Named_Swapping
begin

section \<open>An explicit fresh-binder α relation on raw named terms\<close>

text \<open>
  A bound name x may be changed to a name y of the same fixed type when
  y is fresh for the entire body: λx.A is related to λy.(x y)·A.
  Close these changes under application, abstraction, symmetry, and
  transitivity.  Source role: named binding in Bacon–Dorr §1.1, p.5,
  with the no-capture proviso of Figure 2, p.8.

  Isabelle representation.  The generator requires G x = G y and
  y ∉ named_vars A, excluding both free and bound occurrences of y.
  The finite swap acts on all variable and binder names in A, so shadowing
  structure is retained even when A contains further binders named x.
  Constants and first-class logical symbols are untouched.

  Status.  This is an independently generated relation, not equality of
  de Bruijn encodings and not a quotient definition.  The fresh-all-names
  guard is stronger than the usual free-name freshness formulation.
  Its characterization as the full conventional α relation, and equality
  or invariance of encodings, remain separate obligations.  No named
  substitution correspondence, source proof rule, or model equivalence
  is asserted here.  Richness is unnecessary for the invariance results;
  it will matter when fresh names must be constructed uniformly.
\<close>

inductive named_alpha ::
  "sgcontext \<Rightarrow> ('c, 'l) named_term \<Rightarrow> ('c, 'l) named_term \<Rightarrow> bool"
  for G :: sgcontext where
  Refl: "named_alpha G A A"
| Fresh_Binder: "G x = G y \<Longrightarrow> y \<notin> named_vars A \<Longrightarrow>
    named_alpha G (NLam x A) (NLam y (named_swap x y A))"
| App: "named_alpha G F H \<Longrightarrow> named_alpha G A B \<Longrightarrow>
    named_alpha G (NApp F A) (NApp H B)"
| Lam: "named_alpha G A B \<Longrightarrow> named_alpha G (NLam n A) (NLam n B)"
| Sym: "named_alpha G A B \<Longrightarrow> named_alpha G B A"
| Trans: "named_alpha G A B \<Longrightarrow> named_alpha G B C \<Longrightarrow> named_alpha G A C"

lemma named_alpha_equivp: "equivp (named_alpha G)"
  by (rule equivpI)
    ((rule reflpI, rule named_alpha.Refl),
      (rule sympI, rule named_alpha.Sym, assumption),
      (rule transpI, rule named_alpha.Trans, assumption, assumption))

theorem named_alpha_type_iff:
  assumes alpha: "named_alpha G A B"
  shows "has_ntype L G A \<tau> \<longleftrightarrow> has_ntype L G B \<tau>"
  using alpha
proof (induction arbitrary: \<tau> rule: named_alpha.induct)
  case Refl
  show ?case by (rule refl)
next
  case (Fresh_Binder x y A)
  show ?case by (rule named_fresh_binder_type_iff[OF Fresh_Binder.hyps(1)])
next
  case App
  show ?case by (simp only: named_app_type_iff App.IH)
next
  case Lam
  show ?case by (simp only: named_lam_type_iff Lam.IH)
next
  case Sym
  show ?case by (rule sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule trans[OF Trans.IH])
qed

corollary named_alpha_preserves_typing:
  "named_alpha G A B \<Longrightarrow> has_ntype L G A \<tau> \<Longrightarrow> has_ntype L G B \<tau>"
  by (rule iffD1[OF named_alpha_type_iff], assumption, assumption)

theorem named_alpha_signature:
  assumes alpha: "named_alpha G A B"
  shows "named_in_signature \<Sigma> A = named_in_signature \<Sigma> B"
  using alpha
proof (induction rule: named_alpha.induct)
  case Refl
  show ?case by (rule refl)
next
  case Fresh_Binder
  show ?case by (simp only: named_in_signature.simps named_swap_signature)
next
  case App
  show ?case by (simp only: named_in_signature.simps App.IH)
next
  case Lam
  show ?case by (simp only: named_in_signature.simps Lam.IH)
next
  case Sym
  show ?case by (rule sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule trans[OF Trans.IH])
qed

theorem named_alpha_fv:
  assumes alpha: "named_alpha G A B"
  shows "named_fv A = named_fv B"
  using alpha
proof (induction rule: named_alpha.induct)
  case Refl
  show ?case by (rule refl)
next
  case (Fresh_Binder x y A)
  show ?case by (rule named_fresh_binder_fv[OF Fresh_Binder.hyps(2)])
next
  case App
  show ?case by (simp only: named_fv.simps App.IH)
next
  case Lam
  show ?case by (simp only: named_fv.simps Lam.IH)
next
  case Sym
  show ?case by (rule sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule trans[OF Trans.IH])
qed

corollary named_alpha_language_iff:
  assumes alpha: "named_alpha G A B"
  shows "named_in_language L \<Sigma> G A \<tau> \<longleftrightarrow> named_in_language L \<Sigma> G B \<tau>"
  by (simp only: named_in_language_def named_alpha_type_iff[OF alpha] named_alpha_signature[OF alpha])

lemma named_alpha_identity_binders:
  assumes same_type: "G x = G y"
  shows "named_alpha G (NLam x (NVar x)) (NLam y (NVar y))"
proof (cases "x = y")
  case True
  show ?thesis unfolding True by (rule named_alpha.Refl)
next
  case False
  have fresh: "y \<notin> named_vars (NVar x)" using False by simp
  have step: "named_alpha G (NLam x (NVar x)) (NLam y (named_swap x y (NVar x)))"
    by (rule named_alpha.Fresh_Binder[OF same_type fresh])
  show ?thesis using step by (simp only: named_swap.simps named_swap_index_left)
qed

lemma named_alpha_variable_same:
  "named_alpha G (NVar x) (NVar y) \<Longrightarrow> x = y"
  using named_alpha_fv[where A="NVar x" and B="NVar y"] by simp

end
