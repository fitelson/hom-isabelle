theory Bacon_Book_Theory_Constant_Renaming
  imports Bacon_Book_Constant_Renaming Bacon_Book_Theory_Derivation
begin

section \<open>Forward theory transport under a change of constant names\<close>

text \<open>
  If S ⊢Σ A and f[Σ(τ)] ⊆ Ω(τ) for every type τ, then
  f[S] ⊢Ω f(A). Source: the nine theory constructors of Bacon,
  Definition 5.1, pp.97–98; this supplies forward language enlargement
  for the fresh signatures in Proposition 15.4, p.319.

  Representation. Only nonlogical constant names change. The variable
  stock G, binder names, logical symbols, and the Gen side condition
  are preserved. Every premise is renamed along with the conclusion.
  Neither injectivity nor richness is required for this forward rule.
  This is an induction over the existing calculus, not a new rule
  constructor, and it does not assert reflection or conservativity.
\<close>

theorem book_theory_constant_rename:
  assumes derivation: "book_theory_derivable \<Sigma> G S A"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> f c \<in> \<Omega> \<tau>"
  shows "book_theory_derivable \<Omega> G (image (book_constant_rename f) S)
    (book_constant_rename f A)"
  using derivation
proof (induction rule: book_theory_derivable.induct)
  case (Assumption A S)
  have member: "book_constant_rename f A \<in> image (book_constant_rename f) S"
    by (rule imageI[OF Assumption.hyps(1)])
  have language: "book_theory_formula \<Omega> G (book_constant_rename f A)"
    by (rule book_constant_rename_language[OF Assumption.hyps(2) maps])
  show ?case by (rule book_theory_derivable.Assumption[OF member language])
next
  case PC1
  show ?case by (simp only: book_constant_rename_imp;
    rule book_theory_derivable.PC1[OF book_constant_rename_language[OF PC1.hyps(1) maps]
      book_constant_rename_language[OF PC1.hyps(2) maps]])
next
  case PC2
  show ?case by (simp only: book_constant_rename_imp;
    rule book_theory_derivable.PC2[OF book_constant_rename_language[OF PC2.hyps(1) maps]
      book_constant_rename_language[OF PC2.hyps(2) maps]
      book_constant_rename_language[OF PC2.hyps(3) maps]])
next
  case PC3
  show ?case by (simp only: book_constant_rename_imp book_constant_rename_not;
    rule book_theory_derivable.PC3[OF book_constant_rename_language[OF PC3.hyps(1) maps]
      book_constant_rename_language[OF PC3.hyps(2) maps]])
next
  case UI
  show ?case by (simp only: book_constant_rename_imp book_constant_rename_simps;
    rule book_theory_derivable.UI[OF book_constant_rename_language[OF UI.hyps(1) maps]
      book_constant_rename_language[OF UI.hyps(2) maps]])
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
    rule book_theory_derivable.Beta[OF book_constant_rename_language[OF Beta.hyps(1) maps]
      book_constant_rename_language[OF Beta.hyps(2) maps] steps])
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
    rule book_theory_derivable.Eta[OF book_constant_rename_language[OF Eta.hyps(1) maps]
      book_constant_rename_language[OF Eta.hyps(2) maps] steps])
next
  case (MP S A B)
  have implication: "book_theory_derivable \<Omega> G (image (book_constant_rename f) S)
    (book_imp (book_constant_rename f A) (book_constant_rename f B))"
    using MP.IH(2) by (simp only: book_constant_rename_imp)
  show ?case by (rule book_theory_derivable.MP[OF MP.IH(1) implication
    book_constant_rename_language[OF MP.hyps(3) maps]])
next
  case (Gen S A B n)
  have implication: "book_theory_derivable \<Omega> G (image (book_constant_rename f) S)
    (book_imp (book_constant_rename f A) (book_constant_rename f B))"
    using Gen.IH by (simp only: book_constant_rename_imp)
  have fresh: "n \<notin> named_fv (book_constant_rename f A)"
    by (simp only: book_constant_rename_fv; rule Gen.hyps(4))
  show ?case by (simp only: book_constant_rename_imp book_constant_rename_all;
    rule book_theory_derivable.Gen[OF implication
      book_constant_rename_language[OF Gen.hyps(2) maps]
      book_constant_rename_language[OF Gen.hyps(3) maps] fresh])
qed

corollary book_theory_constant_rename_image:
  assumes derivation: "book_theory_derivable \<Sigma> G S A"
  shows "book_theory_derivable (\<lambda>\<tau>. image f (\<Sigma> \<tau>)) G
    (image (book_constant_rename f) S) (book_constant_rename f A)"
  by (rule book_theory_constant_rename[OF derivation]; rule imageI; assumption)

corollary book_theory_constant_rename_empty:
  assumes derivation: "book_theory_derivable \<Sigma> G {} A"
    and maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> f c \<in> \<Omega> \<tau>"
  shows "book_theory_derivable \<Omega> G {} (book_constant_rename f A)"
  using book_theory_constant_rename[OF derivation maps] by (simp only: image_empty)

end
