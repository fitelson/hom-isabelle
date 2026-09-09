theory Bacon_Book_Primitive_Disjunction_Theory_Derivation
  imports Bacon_Book_Disjunction_Formula_Syntax Bacon_Book_Source_Reduction
begin

section \<open>The independent calculus with primitive conjunction and disjunction\<close>

text \<open>
  Retain the nine printed Chapter 5 constructors and the three native
  conjunction schemas. Add the disjunction schemas of §5.2, p.104:
  (A→C)→((B→C)→((A∨B)→C)), A→(A∨B), and B→(A∨B).
  OrE, OrI1 and OrI2 below name these AXIOM schemas, not new rules
  for reasoning by cases or introducing a premise.

  This judgment is independently inductive over the cumulative vocabulary.
  Primitive ∧ is book_disj_conj; primitive ∨ is book_disj_apply.
  β uses the printed free-for test; η retains its freshness guard.
  Gen retains antecedent freshness, without a freshness condition on S.
  There is no α constructor, encoding-based rule, old-theorem leaf,
  model premise, or rule replacing either primitive connective.
  Language and premise monotonicity are proved by native fifteen-case
  inductions. No encoding or semantic correspondence is assumed.
\<close>

inductive book_disj_theory_derivable ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_disj_term set \<Rightarrow> 'c book_disj_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Assumption: "A \<in> S \<Longrightarrow> book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_theory_derivable \<Sigma> G S A"
| PC1: "book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_formula \<Sigma> G B \<Longrightarrow>
    book_disj_theory_derivable \<Sigma> G S (book_disj_imp A (book_disj_imp B A))"
| PC2: "book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_formula \<Sigma> G B \<Longrightarrow>
    book_disj_formula \<Sigma> G C \<Longrightarrow> book_disj_theory_derivable \<Sigma> G S
      (book_disj_imp (book_disj_imp A (book_disj_imp B C))
        (book_disj_imp (book_disj_imp A B) (book_disj_imp A C)))"
| PC3: "book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_formula \<Sigma> G B \<Longrightarrow>
    book_disj_theory_derivable \<Sigma> G S
      (book_disj_imp (book_disj_imp (book_disj_not G A) (book_disj_not G B)) (book_disj_imp B A))"
| UI: "book_in_language book_disj_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop) \<Longrightarrow>
    book_in_language book_disj_logical_type UNIV \<Sigma> G a \<sigma> \<Longrightarrow>
    book_disj_theory_derivable \<Sigma> G S
      (book_disj_imp (NApp (NLogical (BDConjunction (BCMinimal (SBAll \<sigma>)))) F) (NApp F a))"
| Beta: "book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_formula \<Sigma> G B \<Longrightarrow>
    (named_compatible_step book_printed_beta_contract A B \<or> named_compatible_step book_printed_beta_contract B A) \<Longrightarrow>
    book_disj_theory_derivable \<Sigma> G S (book_disj_imp A B)"
| Eta: "book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_formula \<Sigma> G B \<Longrightarrow>
    (named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A) \<Longrightarrow>
    book_disj_theory_derivable \<Sigma> G S (book_disj_imp A B)"
| MP: "book_disj_theory_derivable \<Sigma> G S A \<Longrightarrow>
    book_disj_theory_derivable \<Sigma> G S (book_disj_imp A B) \<Longrightarrow>
    book_disj_formula \<Sigma> G B \<Longrightarrow> book_disj_theory_derivable \<Sigma> G S B"
| Gen: "book_disj_theory_derivable \<Sigma> G S (book_disj_imp A B) \<Longrightarrow>
    book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_formula \<Sigma> G B \<Longrightarrow>
    n \<notin> named_fv A \<Longrightarrow> book_disj_theory_derivable \<Sigma> G S (book_disj_imp A (book_disj_all G n B))"
| AndI: "book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_formula \<Sigma> G B \<Longrightarrow>
    book_disj_theory_derivable \<Sigma> G S (book_disj_imp A (book_disj_imp B (book_disj_conj A B)))"
| AndE1: "book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_formula \<Sigma> G B \<Longrightarrow>
    book_disj_theory_derivable \<Sigma> G S (book_disj_imp (book_disj_conj A B) A)"
| AndE2: "book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_formula \<Sigma> G B \<Longrightarrow>
    book_disj_theory_derivable \<Sigma> G S (book_disj_imp (book_disj_conj A B) B)"
| OrE: "book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_formula \<Sigma> G B \<Longrightarrow>
    book_disj_formula \<Sigma> G C \<Longrightarrow> book_disj_theory_derivable \<Sigma> G S
      (book_disj_imp (book_disj_imp A C)
        (book_disj_imp (book_disj_imp B C) (book_disj_imp (book_disj_apply A B) C)))"
| OrI1: "book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_formula \<Sigma> G B \<Longrightarrow>
    book_disj_theory_derivable \<Sigma> G S (book_disj_imp A (book_disj_apply A B))"
| OrI2: "book_disj_formula \<Sigma> G A \<Longrightarrow> book_disj_formula \<Sigma> G B \<Longrightarrow>
    book_disj_theory_derivable \<Sigma> G S (book_disj_imp B (book_disj_apply A B))"

lemma book_disj_theory_UI_language:
  assumes predicate: "book_in_language book_disj_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and argument: "book_in_language book_disj_logical_type UNIV \<Sigma> G a \<sigma>"
  shows "book_disj_formula \<Sigma> G
    (book_disj_imp (NApp (NLogical (BDConjunction (BCMinimal (SBAll \<sigma>)))) F) (NApp F a))"
  by (rule book_disj_imp_language[OF book_language_App[OF book_disj_all_operator_language predicate]
    book_language_App[OF predicate argument]])

theorem book_disj_theory_derivable_language:
  assumes derivation: "book_disj_theory_derivable \<Sigma> G S A" and rich: "sg_rich G"
  shows "book_disj_formula \<Sigma> G A"
  using derivation
proof (induction rule: book_disj_theory_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.hyps(2))
next
  case PC1
  show ?case by (intro book_disj_imp_language; rule PC1.hyps)
next
  case PC2
  show ?case by (intro book_disj_imp_language; rule PC2.hyps)
next
  case PC3
  show ?case by (intro book_disj_imp_language)
    (rule book_disj_not_language[OF rich PC3.hyps(1)], rule book_disj_not_language[OF rich PC3.hyps(2)],
      rule PC3.hyps(2), rule PC3.hyps(1))
next
  case UI
  show ?case by (rule book_disj_theory_UI_language[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_disj_imp_language[OF Beta.hyps(1,2)])
next
  case Eta
  show ?case by (rule book_disj_imp_language[OF Eta.hyps(1,2)])
next
  case MP
  show ?case by (rule MP.hyps(3))
next
  case Gen
  show ?case by (rule book_disj_imp_language[OF Gen.hyps(2) book_disj_all_language[OF Gen.hyps(3)]])
next
  case AndI
  show ?case by (rule book_disj_imp_language[OF AndI.hyps(1)
    book_disj_imp_language[OF AndI.hyps(2) book_disj_conj_language[OF AndI.hyps]]])
next
  case AndE1
  show ?case by (rule book_disj_imp_language[OF book_disj_conj_language[OF AndE1.hyps] AndE1.hyps(1)])
next
  case AndE2
  show ?case by (rule book_disj_imp_language[OF book_disj_conj_language[OF AndE2.hyps] AndE2.hyps(2)])
next
  case (OrE A B C S)
  have ac: "book_disj_formula \<Sigma> G (book_disj_imp A C)"
    by (rule book_disj_imp_language[OF OrE.hyps(1,3)])
  have bc: "book_disj_formula \<Sigma> G (book_disj_imp B C)"
    by (rule book_disj_imp_language[OF OrE.hyps(2,3)])
  have disjunction: "book_disj_formula \<Sigma> G (book_disj_apply A B)"
    by (rule book_disj_apply_language[OF OrE.hyps(1,2)])
  have result: "book_disj_formula \<Sigma> G (book_disj_imp (book_disj_apply A B) C)"
    by (rule book_disj_imp_language[OF disjunction OrE.hyps(3)])
  show ?case by (rule book_disj_imp_language[OF ac book_disj_imp_language[OF bc result]])
next
  case OrI1
  show ?case by (rule book_disj_imp_language[OF OrI1.hyps(1) book_disj_apply_language[OF OrI1.hyps]])
next
  case OrI2
  show ?case by (rule book_disj_imp_language[OF OrI2.hyps(2) book_disj_apply_language[OF OrI2.hyps]])
qed

lemma book_disj_theory_derivable_mono:
  assumes derivation: "book_disj_theory_derivable \<Sigma> G S A" and inclusion: "S \<subseteq> T"
  shows "book_disj_theory_derivable \<Sigma> G T A"
  using derivation inclusion
proof (induction arbitrary: T rule: book_disj_theory_derivable.induct)
  case Assumption
  show ?case by (rule book_disj_theory_derivable.Assumption[
    OF subsetD[OF Assumption.prems Assumption.hyps(1)] Assumption.hyps(2)])
next
  case PC1
  show ?case by (rule book_disj_theory_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_disj_theory_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_disj_theory_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_disj_theory_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_disj_theory_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_disj_theory_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_disj_theory_derivable.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_disj_theory_derivable.Gen[OF Gen.IH[OF Gen.prems] Gen.hyps(2,3,4)])
next
  case AndI
  show ?case by (rule book_disj_theory_derivable.AndI[OF AndI.hyps])
next
  case AndE1
  show ?case by (rule book_disj_theory_derivable.AndE1[OF AndE1.hyps])
next
  case AndE2
  show ?case by (rule book_disj_theory_derivable.AndE2[OF AndE2.hyps])
next
  case OrE
  show ?case by (rule book_disj_theory_derivable.OrE[OF OrE.hyps])
next
  case OrI1
  show ?case by (rule book_disj_theory_derivable.OrI1[OF OrI1.hyps])
next
  case OrI2
  show ?case by (rule book_disj_theory_derivable.OrI2[OF OrI2.hyps])
qed

end

