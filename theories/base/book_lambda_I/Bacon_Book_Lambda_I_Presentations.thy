theory Bacon_Book_Lambda_I_Presentations
  imports Bacon_Book_Lambda_I_Conversion
begin

section \<open>The two presentations of Gen, and regressions\<close>

text \<open>
  Definition 9.8 (p.197) states Gen with the quantifier constant: from
  A → F x infer A → ∀σ F, x fresh for A and F. The main calculus uses the
  binder form with the extra occurrence guard. Both presentations derive
  each other: binder Gen then η gives the constant form; the constant form
  applied to λx.B, after a β-expansion of B to (λx.B)x (exact-capture β,
  self-substitution), gives the binder form. The regressions record that
  α-renaming of a binder is internally derivable (the case that defeated
  the general-language design) and that vacuous abstraction is excluded
  together with everything reducing to it.
\<close>

lemma named_free_for_self_variable: "named_free_for (NVar x) x A"
  by (induction A) auto

subsection \<open>The constant-form calculus\<close>

inductive book_lambda_I_derivable_c ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Assumption: "A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_derivable_c \<Sigma> G S A"
| PC1: "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G B \<Longrightarrow>
    book_lambda_I_derivable_c \<Sigma> G S (book_imp A (book_imp B A))"
| PC2: "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G B \<Longrightarrow>
    book_lambda_I_formula \<Sigma> G C \<Longrightarrow> book_lambda_I_derivable_c \<Sigma> G S
      (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)))"
| PC3: "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G B \<Longrightarrow>
    book_lambda_I_derivable_c \<Sigma> G S (book_imp (book_imp (book_not G A) (book_not G B)) (book_imp B A))"
| UI: "F \<in> book_LI \<Sigma> G (Arr \<sigma> Prop) \<Longrightarrow> a \<in> book_LI \<Sigma> G \<sigma> \<Longrightarrow>
    book_lambda_I_derivable_c \<Sigma> G S (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
| Beta: "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G B \<Longrightarrow>
    (named_compatible_step named_beta_contract A B \<or> named_compatible_step named_beta_contract B A) \<Longrightarrow>
    book_lambda_I_derivable_c \<Sigma> G S (book_imp A B)"
| Eta: "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G B \<Longrightarrow>
    (named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A) \<Longrightarrow>
    book_lambda_I_derivable_c \<Sigma> G S (book_imp A B)"
| MP: "book_lambda_I_derivable_c \<Sigma> G S A \<Longrightarrow> book_lambda_I_derivable_c \<Sigma> G S (book_imp A B) \<Longrightarrow>
    book_lambda_I_formula \<Sigma> G B \<Longrightarrow> book_lambda_I_derivable_c \<Sigma> G S B"
| Gen_c: "book_lambda_I_derivable_c \<Sigma> G S (book_imp A (NApp F (NVar x))) \<Longrightarrow>
    book_lambda_I_formula \<Sigma> G A \<Longrightarrow> F \<in> book_LI \<Sigma> G (Arr (G x) Prop) \<Longrightarrow>
    x \<notin> named_fv A \<Longrightarrow> x \<notin> named_fv F \<Longrightarrow>
    book_lambda_I_derivable_c \<Sigma> G S (book_imp A (NApp (NLogical (SBAll (G x))) F))"

lemma book_lambda_I_imp_trans_c:
  assumes ab: "book_lambda_I_derivable_c \<Sigma> G S (book_imp A B)"
    and bc: "book_lambda_I_derivable_c \<Sigma> G S (book_imp B C)"
    and al: "book_lambda_I_formula \<Sigma> G A" and bl: "book_lambda_I_formula \<Sigma> G B"
    and cl: "book_lambda_I_formula \<Sigma> G C"
  shows "book_lambda_I_derivable_c \<Sigma> G S (book_imp A C)"
proof -
  have lift: "book_lambda_I_derivable_c \<Sigma> G S (book_imp (book_imp B C) (book_imp A (book_imp B C)))"
    by (rule book_lambda_I_derivable_c.PC1) (simp_all add: book_lambda_I_imp_formula bl cl al)
  have nested: "book_lambda_I_derivable_c \<Sigma> G S (book_imp A (book_imp B C))"
    by (rule book_lambda_I_derivable_c.MP[OF bc lift]) (simp add: book_lambda_I_imp_formula al bl cl)
  have distribute: "book_lambda_I_derivable_c \<Sigma> G S
    (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)))"
    by (rule book_lambda_I_derivable_c.PC2[OF al bl cl])
  have partial: "book_lambda_I_derivable_c \<Sigma> G S (book_imp (book_imp A B) (book_imp A C))"
    by (rule book_lambda_I_derivable_c.MP[OF nested distribute]) (simp add: book_lambda_I_imp_formula al bl cl)
  show ?thesis by (rule book_lambda_I_derivable_c.MP[OF ab partial]) (simp add: book_lambda_I_imp_formula al cl)
qed

subsection \<open>The constant form is derivable in the binder calculus\<close>

lemma book_LI_all_operator:
  "NLogical (SBAll \<sigma>) \<in> book_LI \<Sigma> G (Arr (Arr \<sigma> Prop) Prop)"
  by (rule book_LI_I[OF book_all_operator_language]) simp

theorem book_lambda_I_Gen_constant:
  assumes premise: "book_lambda_I_derivable \<Sigma> G S (book_imp A (NApp F (NVar x)))"
    and al: "book_lambda_I_formula \<Sigma> G A" and fm: "F \<in> book_LI \<Sigma> G (Arr (G x) Prop)"
    and fresh_A: "x \<notin> named_fv A" and fresh_F: "x \<notin> named_fv F"
  shows "book_lambda_I_derivable \<Sigma> G S (book_imp A (NApp (NLogical (SBAll (G x))) F))"
proof -
  let ?B = "NApp F (NVar x)"
  let ?E = "NLam x ?B"
  have bm: "?B \<in> book_LI \<Sigma> G Prop" by (rule book_LI_App[OF fm book_LI_Var])
  have bl: "book_lambda_I_formula \<Sigma> G ?B" using bm by (simp only: book_lambda_I_formula_terms)
  have occurs: "x \<in> named_fv ?B" by simp
  have generalized: "book_lambda_I_derivable \<Sigma> G S (book_imp A (book_all G x ?B))"
    by (rule book_lambda_I_derivable.Gen[OF premise al bl fresh_A occurs])
  have em: "?E \<in> book_LI \<Sigma> G (Arr (G x) Prop)" by (rule book_LI_Lam[OF bm occurs])
  have expanded: "NApp (NLogical (SBAll (G x))) ?E \<in> book_LI \<Sigma> G Prop"
    by (rule book_LI_App[OF book_LI_all_operator em])
  have contracted: "NApp (NLogical (SBAll (G x))) F \<in> book_LI \<Sigma> G Prop"
    by (rule book_LI_App[OF book_LI_all_operator fm])
  have eta_root: "named_eta_contract ?E F" by (rule named_eta_contract.eta[OF fresh_F])
  have eta_step: "named_compatible_step named_eta_contract (NApp (NLogical (SBAll (G x))) ?E) (NApp (NLogical (SBAll (G x))) F)"
    by (rule named_compatible_step.App_right[OF named_compatible_step.root[where R=named_eta_contract and M="?E" and N=F, OF eta_root]])
  have eta: "book_lambda_I_derivable \<Sigma> G S (book_imp (NApp (NLogical (SBAll (G x))) ?E) (NApp (NLogical (SBAll (G x))) F))"
    by (rule book_lambda_I_derivable.Eta[OF _ _ disjI1[OF eta_step]])
      (simp_all only: book_lambda_I_formula_terms expanded contracted)
  show ?thesis
    using book_lambda_I_imp_trans[OF generalized[unfolded book_all_def] eta al _ _]
      expanded contracted by (simp only: book_lambda_I_formula_terms)
qed

subsection \<open>Mutual embedding of the two presentations\<close>

theorem book_lambda_I_derivable_c_to_binder:
  assumes derivation: "book_lambda_I_derivable_c \<Sigma> G S A"
  shows "book_lambda_I_derivable \<Sigma> G S A"
  using derivation
proof (induction rule: book_lambda_I_derivable_c.induct)
  case Assumption
  show ?case by (rule book_lambda_I_derivable.Assumption[OF Assumption.hyps])
next
  case PC1
  show ?case by (rule book_lambda_I_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_lambda_I_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_lambda_I_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_lambda_I_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_lambda_I_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_lambda_I_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_lambda_I_derivable.MP[OF MP.IH MP.hyps(3)])
next
  case Gen_c
  show ?case by (rule book_lambda_I_Gen_constant[OF Gen_c.IH Gen_c.hyps(2-5)])
qed

theorem book_lambda_I_derivable_binder_to_c:
  assumes derivation: "book_lambda_I_derivable \<Sigma> G S A"
  shows "book_lambda_I_derivable_c \<Sigma> G S A"
  using derivation
proof (induction rule: book_lambda_I_derivable.induct)
  case Assumption
  show ?case by (rule book_lambda_I_derivable_c.Assumption[OF Assumption.hyps])
next
  case PC1
  show ?case by (rule book_lambda_I_derivable_c.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_lambda_I_derivable_c.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_lambda_I_derivable_c.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_lambda_I_derivable_c.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_lambda_I_derivable_c.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_lambda_I_derivable_c.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_lambda_I_derivable_c.MP[OF MP.IH MP.hyps(3)])
next
  case (Gen S A B n)
  let ?F = "NLam n B"
  let ?R = "NApp ?F (NVar n)"
  have bm: "B \<in> book_LI \<Sigma> G Prop" using Gen.hyps(3) by (simp only: book_lambda_I_formula_terms)
  have fm: "?F \<in> book_LI \<Sigma> G (Arr (G n) Prop)" by (rule book_LI_Lam[OF bm Gen.hyps(5)])
  have rm: "?R \<in> book_LI \<Sigma> G Prop" by (rule book_LI_App[OF fm book_LI_Var])
  have rl: "book_lambda_I_formula \<Sigma> G ?R" using rm by (simp only: book_lambda_I_formula_terms)
  have beta_root: "named_beta_contract ?R B"
    using named_beta_contract.beta[OF named_free_for_self_variable[of n B]] by (simp only: named_subst_same_variable)
  have beta_step: "named_compatible_step named_beta_contract ?R B"
    by (rule named_compatible_step.root[where R=named_beta_contract and M="?R" and N=B, OF beta_root])
  have expand: "book_lambda_I_derivable_c \<Sigma> G S (book_imp B ?R)"
    by (rule book_lambda_I_derivable_c.Beta[OF Gen.hyps(3) rl disjI2[OF beta_step]])
  have premise: "book_lambda_I_derivable_c \<Sigma> G S (book_imp A ?R)"
    by (rule book_lambda_I_imp_trans_c[OF Gen.IH expand Gen.hyps(2) Gen.hyps(3) rl])
  have fresh_F: "n \<notin> named_fv ?F" by simp
  show ?case unfolding book_all_def
    by (rule book_lambda_I_derivable_c.Gen_c[OF premise Gen.hyps(2) fm Gen.hyps(4) fresh_F])
qed

theorem book_lambda_I_presentations_iff:
  "book_lambda_I_derivable \<Sigma> G S A \<longleftrightarrow> book_lambda_I_derivable_c \<Sigma> G S A"
  by (rule iffI[OF book_lambda_I_derivable_binder_to_c book_lambda_I_derivable_c_to_binder])

subsection \<open>Regressions\<close>

theorem book_lambda_I_alpha_regression:
  assumes declared: "R \<in> \<Sigma> (Arr (Arr Prop Prop) Prop)" and n: "G n = Prop" and m: "G m = Prop"
  shows "book_lambda_I_derivable \<Sigma> G S
      (book_imp (NApp (NConst R (Arr (Arr Prop Prop) Prop)) (NLam n (NVar n)))
        (NApp (NConst R (Arr (Arr Prop Prop) Prop)) (NLam m (NVar m)))) \<and>
    book_lambda_I_derivable \<Sigma> G S
      (book_imp (NApp (NConst R (Arr (Arr Prop Prop) Prop)) (NLam m (NVar m)))
        (NApp (NConst R (Arr (Arr Prop Prop) Prop)) (NLam n (NVar n))))"
proof -
  let ?R = "NConst R (Arr (Arr Prop Prop) Prop)"
  let ?I = "NLam n (NVar n)"
  let ?J = "NLam m (NVar m)"
  have rm: "?R \<in> book_LI \<Sigma> G (Arr (Arr Prop Prop) Prop)"
    by (rule book_LI_I) (simp_all add: book_language_const_iff declared)
  have im: "?I \<in> book_LI \<Sigma> G (Arr Prop Prop)"
    using book_LI_Lam[OF book_LI_Var[of n \<Sigma> G], of n] by (simp add: n)
  have member: "NApp ?R ?I \<in> book_LI \<Sigma> G Prop" by (rule book_LI_App[OF rm im])
  have alpha: "named_alpha G (NApp ?R ?I) (NApp ?R ?J)"
    by (rule named_alpha.App[OF named_alpha.Refl named_alpha_identity_binders]) (simp add: n m)
  show ?thesis by (rule book_lambda_I_conv_derivable_pair[OF book_lambda_I_alpha_conv[OF alpha member]])
qed

theorem book_lambda_I_omission_regression_vacuous:
  assumes distinct: "x \<noteq> p"
  shows "\<not> book_lambda_I (NLam x (NVar p))"
  using distinct by simp

theorem book_lambda_I_omission_regression_beta:
  assumes distinct: "x \<noteq> p" and step: "named_compatible_step named_beta_contract A (NLam x (NVar p))"
  shows "\<not> book_lambda_I A"
  using conjunct1[OF book_lambda_I_beta_step[OF step]] distinct by auto

theorem book_lambda_I_omission_regression_eta:
  assumes distinct: "x \<noteq> p" and step: "named_compatible_step named_eta_contract A (NLam x (NVar p))"
  shows "\<not> book_lambda_I A"
  using conjunct1[OF book_lambda_I_eta_step[OF step]] distinct by auto

text \<open>
  The vacuous abstraction λx.p (x ≠ p, both of the same type) is not a λI
  term, and no λI term reaches it by an immediate β or η step, so it is a
  genuine omission of the fragment rather than an artefact of normal forms.
  The α-regression proves both implications between the applications of a
  declared predicate to two α-variants of the propositional identity; in a
  proper sublanguage lacking the η-expansion intermediate this fails, which
  is why the general-language design was rejected.
\<close>

end
