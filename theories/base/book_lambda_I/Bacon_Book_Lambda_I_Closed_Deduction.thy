theory Bacon_Book_Lambda_I_Closed_Deduction
  imports Bacon_Book_Lambda_I_Conjunction_Currying Bacon_Book_Lambda_I_Conversion
begin

section \<open>Deduction when the discharged assumption is closed\<close>

text \<open>
  If C is a closed formula, then S∪{C} ⊢ B iff S ⊢ C→B.
  Neither S nor B must be closed. This is an explicitly qualified
  deduction theorem: the unrestricted open-assumption version displayed
  on p.318 is not asserted. The unrestricted open-discharge
  counterexample (book_unrestricted_open_deduction_counterexample, stated
  for the full calculus book_theory_derivable) is not ported to this
  session; unrestricted open discharge is simply not asserted for
  book_lambda_I_derivable.

  The forward induction uses every original theory constructor. In the
  Gen case, combine C and the original antecedent A as D=¬(C→¬A).
  Uncurrying gives D→B. Since FV(C) is empty and the original rule requires
  n∉FV(A), also n∉FV(D); the SAME Gen rule yields D→∀n.B.
  Currying back gives C→(A→∀n.B). All propositional conversions are
  previously derived certificates, not semantic tautology assumptions.
\<close>

lemma book_lambda_I_weaken_theorem:
  assumes rich: "sg_rich G" and theorem_A: "book_lambda_I_derivable \<Sigma> G {} A"
    and cl: "book_lambda_I_formula \<Sigma> G C"
  shows "book_lambda_I_derivable \<Sigma> G S (book_imp C A)"
proof -
  have al: "book_lambda_I_formula \<Sigma> G A"
    by (rule book_lambda_I_derivable_language[OF theorem_A rich])
  have lifted: "book_lambda_I_derivable \<Sigma> G S A"
    by (rule book_lambda_I_derivable_mono[OF theorem_A empty_subsetI])
  show ?thesis by (rule book_lambda_I_imp_weaken[OF lifted cl al])
qed

lemma book_lambda_I_closed_deduction_aux:
  assumes rich: "sg_rich G" and cl: "book_lambda_I_formula \<Sigma> G C"
    and closed: "named_fv C = {}"
    and derivation: "book_lambda_I_derivable \<Sigma> G T B"
    and insertion: "T = insert C S"
  shows "book_lambda_I_derivable \<Sigma> G S (book_imp C B)"
  using derivation insertion
proof (induction arbitrary: S rule: book_lambda_I_derivable.induct)
  case (Assumption A T)
  show ?case
  proof (cases "A = C")
    case True
    show ?thesis by (simp only: True; rule book_lambda_I_imp_refl[OF cl])
  next
    case False
    have member: "A \<in> S" using Assumption.hyps(1) Assumption.prems False by auto
    have local_fact: "book_lambda_I_derivable \<Sigma> G S A"
      by (rule book_lambda_I_derivable.Assumption[OF member Assumption.hyps(2)])
    show ?thesis by (rule book_lambda_I_imp_weaken[OF local_fact cl Assumption.hyps(2)])
  qed
next
  case PC1
  show ?case by (rule book_lambda_I_weaken_theorem[OF rich _ cl], rule book_lambda_I_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_lambda_I_weaken_theorem[OF rich _ cl], rule book_lambda_I_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_lambda_I_weaken_theorem[OF rich _ cl], rule book_lambda_I_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_lambda_I_weaken_theorem[OF rich _ cl], rule book_lambda_I_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_lambda_I_weaken_theorem[OF rich _ cl], rule book_lambda_I_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_lambda_I_weaken_theorem[OF rich _ cl], rule book_lambda_I_derivable.Eta[OF Eta.hyps])
next
  case (MP T A B)
  have ca: "book_lambda_I_derivable \<Sigma> G S (book_imp C A)"
    by (rule MP.IH(1)[OF MP.prems])
  have cab: "book_lambda_I_derivable \<Sigma> G S (book_imp C (book_imp A B))"
    by (rule MP.IH(2)[OF MP.prems])
  have al: "book_lambda_I_formula \<Sigma> G A"
    by (rule book_lambda_I_derivable_language[OF MP.hyps(1) rich])
  have cbl: "book_lambda_I_formula \<Sigma> G (book_imp C B)"
    by (rule book_lambda_I_imp_language[OF cl MP.hyps(3)])
  have tail_language: "book_lambda_I_formula \<Sigma> G (book_imp (book_imp C A) (book_imp C B))"
    by (rule book_lambda_I_imp_language[OF book_lambda_I_imp_language[OF cl al] cbl])
  have schema: "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_imp C (book_imp A B)) (book_imp (book_imp C A) (book_imp C B)))"
    by (rule book_lambda_I_derivable.PC2[OF cl al MP.hyps(3)])
  have implication: "book_lambda_I_derivable \<Sigma> G S (book_imp (book_imp C A) (book_imp C B))"
    by (rule book_lambda_I_derivable.MP[OF cab schema tail_language])
  show ?case by (rule book_lambda_I_derivable.MP[OF ca implication cbl])
next
  case (Gen T A B n)
  let ?D = "book_not G (book_imp C (book_not G A))"
  have original: "book_lambda_I_derivable \<Sigma> G S (book_imp C (book_imp A B))"
    by (rule Gen.IH[OF Gen.prems])
  have uncurried: "book_lambda_I_derivable \<Sigma> G S (book_imp ?D B)"
    by (rule book_lambda_I_conj_uncurry[OF rich cl Gen.hyps(2,3) original])
  have dl: "book_lambda_I_formula \<Sigma> G ?D"
    by (rule book_lambda_I_not_language[OF rich book_lambda_I_imp_language[OF cl book_lambda_I_not_language[OF rich Gen.hyps(2)]]])
  have fresh: "n \<notin> named_fv ?D"
    using Gen.hyps(4) by (simp add: book_not_fv book_imp_fv closed)
  have generalized: "book_lambda_I_derivable \<Sigma> G S (book_imp ?D (book_all G n B))"
    by (rule book_lambda_I_derivable.Gen[OF uncurried dl Gen.hyps(3) fresh Gen.hyps(5)])
  have all_language: "book_lambda_I_formula \<Sigma> G (book_all G n B)"
    by (rule book_lambda_I_all_language[OF Gen.hyps(3) Gen.hyps(5)])
  show ?case by (rule book_lambda_I_conj_curry[OF rich cl Gen.hyps(2) all_language generalized])
qed

theorem book_lambda_I_closed_deduction:
  assumes rich: "sg_rich G" and cl: "book_lambda_I_formula \<Sigma> G C"
    and closed: "named_fv C = {}"
    and derivation: "book_lambda_I_derivable \<Sigma> G (insert C S) B"
  shows "book_lambda_I_derivable \<Sigma> G S (book_imp C B)"
  by (rule book_lambda_I_closed_deduction_aux[OF rich cl closed derivation refl])

theorem book_lambda_I_closed_deduction_iff:
  assumes rich: "sg_rich G" and cl: "book_lambda_I_formula \<Sigma> G C"
    and closed: "named_fv C = {}"
  shows "book_lambda_I_derivable \<Sigma> G (insert C S) B \<longleftrightarrow>
    book_lambda_I_derivable \<Sigma> G S (book_imp C B)"
proof
  assume derivation: "book_lambda_I_derivable \<Sigma> G (insert C S) B"
  show "book_lambda_I_derivable \<Sigma> G S (book_imp C B)"
    by (rule book_lambda_I_closed_deduction[OF rich cl closed derivation])
next
  assume implication: "book_lambda_I_derivable \<Sigma> G S (book_imp C B)"
  have bl: "book_lambda_I_formula \<Sigma> G B"
    by (rule conjunct2[OF book_lambda_I_imp_operands[OF book_lambda_I_derivable_language[OF implication rich]]])
  have lifted: "book_lambda_I_derivable \<Sigma> G (insert C S) (book_imp C B)"
    by (rule book_lambda_I_derivable_mono[OF implication subset_insertI])
  have assumption: "book_lambda_I_derivable \<Sigma> G (insert C S) C"
    by (rule book_lambda_I_derivable.Assumption[OF insertI1 cl])
  show "book_lambda_I_derivable \<Sigma> G (insert C S) B"
    by (rule book_lambda_I_derivable.MP[OF assumption lifted bl])
qed

end
