theory Bacon_Book_Lambda_I_Theory_Constant_Renaming
  imports Bacon_Book_Environment_Development.Bacon_Book_Constant_Renaming Bacon_Book_Lambda_I_Theory_Closure
begin

section \<open>Forward theory transport under a change of constant names\<close>

text \<open>
  If S ⊢Σ A and f[Σ(τ)] ⊆ Ω(τ) for every type τ, then
  f[S] ⊢Ω f(A). Source: the nine theory constructors of Bacon,
  Definition 5.1, pp.97–98; this supplies forward language enlargement
  for the fresh signatures in Proposition 15.4, p.319. The λI rules used
  here are those of Definition 9.8, p.197, restricted to λI formulas,
  i.e. the same schemas as Definition 5.1 (see Bacon_Book_Lambda_I_Calculus).

  Representation. Only nonlogical constant names change. The variable
  stock G, binder names, logical symbols, and the Gen side condition
  are preserved. Every premise is renamed along with the conclusion.
  Neither injectivity nor richness is required for this forward rule.
  This is an induction over the existing calculus, not a new rule
  constructor, and it does not assert reflection or conservativity.
\<close>

text \<open>
  λI variant. Constant renaming leaves free variable names unchanged, so
  it preserves and reflects the λI property.
\<close>

lemma book_lambda_I_constant_rename_iff:
  "book_lambda_I (book_constant_rename f A) \<longleftrightarrow> book_lambda_I A"
  by (induction A) (simp_all add: book_constant_rename_fv)

lemma book_lambda_I_constant_rename_formula:
  assumes language: "book_lambda_I_formula \<Sigma> G A"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> f c \<in> \<Omega> \<tau>"
  shows "book_lambda_I_formula \<Omega> G (book_constant_rename f A)"
  by (rule conjI[OF book_constant_rename_language[OF conjunct1[OF language] maps]];
    simp only: book_lambda_I_constant_rename_iff conjunct2[OF language])

lemma book_lambda_I_constant_rename_terms:
  assumes member: "A \<in> book_lambda_I_terms L \<Lambda> \<Sigma> G \<tau>"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> f c \<in> \<Omega> \<tau>"
  shows "book_constant_rename f A \<in> book_lambda_I_terms L \<Lambda> \<Omega> G \<tau>"
proof -
  have language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>" and lambda_I: "book_lambda_I A"
    using member unfolding book_lambda_I_terms_def by blast+
  show ?thesis unfolding book_lambda_I_terms_def
    by (simp add: book_constant_rename_language[OF language maps] book_lambda_I_constant_rename_iff lambda_I)
qed

theorem book_lambda_I_constant_rename:
  assumes derivation: "book_lambda_I_derivable \<Sigma> G S A"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> f c \<in> \<Omega> \<tau>"
  shows "book_lambda_I_derivable \<Omega> G (image (book_constant_rename f) S)
    (book_constant_rename f A)"
  using derivation
proof (induction rule: book_lambda_I_derivable.induct)
  case (Assumption A S)
  have member: "book_constant_rename f A \<in> image (book_constant_rename f) S"
    by (rule imageI[OF Assumption.hyps(1)])
  have language: "book_lambda_I_formula \<Omega> G (book_constant_rename f A)"
    by (rule book_lambda_I_constant_rename_formula[OF Assumption.hyps(2) maps])
  show ?case by (rule book_lambda_I_derivable.Assumption[OF member language])
next
  case PC1
  show ?case by (simp only: book_constant_rename_imp;
    rule book_lambda_I_derivable.PC1[OF book_lambda_I_constant_rename_formula[OF PC1.hyps(1) maps]
      book_lambda_I_constant_rename_formula[OF PC1.hyps(2) maps]])
next
  case PC2
  show ?case by (simp only: book_constant_rename_imp;
    rule book_lambda_I_derivable.PC2[OF book_lambda_I_constant_rename_formula[OF PC2.hyps(1) maps]
      book_lambda_I_constant_rename_formula[OF PC2.hyps(2) maps]
      book_lambda_I_constant_rename_formula[OF PC2.hyps(3) maps]])
next
  case PC3
  show ?case by (simp only: book_constant_rename_imp book_constant_rename_not;
    rule book_lambda_I_derivable.PC3[OF book_lambda_I_constant_rename_formula[OF PC3.hyps(1) maps]
      book_lambda_I_constant_rename_formula[OF PC3.hyps(2) maps]])
next
  case UI
  show ?case by (simp only: book_constant_rename_imp book_constant_rename_simps;
    rule book_lambda_I_derivable.UI[OF book_lambda_I_constant_rename_terms[OF UI.hyps(1) maps]
      book_lambda_I_constant_rename_terms[OF UI.hyps(2) maps]])
next
  case (Beta A B S)
  have steps: "named_compatible_step named_beta_contract
      (book_constant_rename f A) (book_constant_rename f B) \<or>
    named_compatible_step named_beta_contract
      (book_constant_rename f B) (book_constant_rename f A)"
  proof (rule disjE[OF Beta.hyps(3)])
    assume step: "named_compatible_step named_beta_contract A B"
    show ?thesis by (rule disjI1; rule book_constant_rename_beta_step[OF step])
  next
    assume step: "named_compatible_step named_beta_contract B A"
    show ?thesis by (rule disjI2; rule book_constant_rename_beta_step[OF step])
  qed
  show ?case by (simp only: book_constant_rename_imp;
    rule book_lambda_I_derivable.Beta[OF book_lambda_I_constant_rename_formula[OF Beta.hyps(1) maps]
      book_lambda_I_constant_rename_formula[OF Beta.hyps(2) maps] steps])
next
  case (Eta A B S)
  have steps: "named_compatible_step named_eta_contract
      (book_constant_rename f A) (book_constant_rename f B) \<or>
    named_compatible_step named_eta_contract
      (book_constant_rename f B) (book_constant_rename f A)"
  proof (rule disjE[OF Eta.hyps(3)])
    assume step: "named_compatible_step named_eta_contract A B"
    show ?thesis by (rule disjI1; rule book_constant_rename_eta_step[OF step])
  next
    assume step: "named_compatible_step named_eta_contract B A"
    show ?thesis by (rule disjI2; rule book_constant_rename_eta_step[OF step])
  qed
  show ?case by (simp only: book_constant_rename_imp;
    rule book_lambda_I_derivable.Eta[OF book_lambda_I_constant_rename_formula[OF Eta.hyps(1) maps]
      book_lambda_I_constant_rename_formula[OF Eta.hyps(2) maps] steps])
next
  case (MP S A B)
  have implication: "book_lambda_I_derivable \<Omega> G (image (book_constant_rename f) S)
    (book_imp (book_constant_rename f A) (book_constant_rename f B))"
    using MP.IH(2) by (simp only: book_constant_rename_imp)
  show ?case by (rule book_lambda_I_derivable.MP[OF MP.IH(1) implication
    book_lambda_I_constant_rename_formula[OF MP.hyps(3) maps]])
next
  case (Gen S A B n)
  have implication: "book_lambda_I_derivable \<Omega> G (image (book_constant_rename f) S)
    (book_imp (book_constant_rename f A) (book_constant_rename f B))"
    using Gen.IH by (simp only: book_constant_rename_imp)
  have fresh: "n \<notin> named_fv (book_constant_rename f A)"
    by (simp only: book_constant_rename_fv; rule Gen.hyps(4))
  have occurs: "n \<in> named_fv (book_constant_rename f B)"
    by (simp only: book_constant_rename_fv; rule Gen.hyps(5))
  show ?case by (simp only: book_constant_rename_imp book_constant_rename_all;
    rule book_lambda_I_derivable.Gen[OF implication
      book_lambda_I_constant_rename_formula[OF Gen.hyps(2) maps]
      book_lambda_I_constant_rename_formula[OF Gen.hyps(3) maps] fresh occurs])
qed

corollary book_lambda_I_constant_rename_image:
  assumes derivation: "book_lambda_I_derivable \<Sigma> G S A"
  shows "book_lambda_I_derivable (\<lambda>\<tau>. image f (\<Sigma> \<tau>)) G
    (image (book_constant_rename f) S) (book_constant_rename f A)"
  by (rule book_lambda_I_constant_rename[OF derivation]; rule imageI; assumption)

corollary book_lambda_I_constant_rename_empty:
  assumes derivation: "book_lambda_I_derivable \<Sigma> G {} A"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> f c \<in> \<Omega> \<tau>"
  shows "book_lambda_I_derivable \<Omega> G {} (book_constant_rename f A)"
  using book_lambda_I_constant_rename[OF derivation maps] by (simp only: image_empty)

end
