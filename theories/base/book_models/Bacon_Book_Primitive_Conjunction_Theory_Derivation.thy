theory Bacon_Book_Primitive_Conjunction_Theory_Derivation
  imports Bacon_Book_Primitive_Conjunction_Formula_Syntax Bacon_Book_Source_Reduction
begin

section \<open>The printed calculus with three primitive-conjunction schemas\<close>

text \<open>
  Add A→(B→(A∧B)), (A∧B)→A and (A∧B)→B to the minimal
  printed calculus. Source: Bacon, §5.2, p.104, together with the
  Chapter 5 rules on pp.97–98. AndI, AndE1 and AndE2 below name
  these AXIOM schemas, not additional inference rules.

  The judgment is independently inductive over the richer named terms.
  It has the nine printed constructors plus those three schemas. β uses
  the printed free-for test; η uses its existing freshness guard. Gen
  retains antecedent freshness without a new condition on all premises.
  There is no encoding-based rule, old-theorem leaf, α rule, semantic
  premise, or rule substituting for the primitive conjunction symbol.
  No equivalence with the fixed-background encoding or model completeness
  is claimed by this declaration.
\<close>

inductive book_conj_theory_derivable ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_conj_term set \<Rightarrow> 'c book_conj_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Assumption: "A \<in> S \<Longrightarrow> book_conj_formula \<Sigma> G A \<Longrightarrow> book_conj_theory_derivable \<Sigma> G S A"
| PC1: "book_conj_formula \<Sigma> G A \<Longrightarrow> book_conj_formula \<Sigma> G B \<Longrightarrow>
    book_conj_theory_derivable \<Sigma> G S (book_conj_imp A (book_conj_imp B A))"
| PC2: "book_conj_formula \<Sigma> G A \<Longrightarrow> book_conj_formula \<Sigma> G B \<Longrightarrow>
    book_conj_formula \<Sigma> G C \<Longrightarrow> book_conj_theory_derivable \<Sigma> G S
      (book_conj_imp (book_conj_imp A (book_conj_imp B C))
        (book_conj_imp (book_conj_imp A B) (book_conj_imp A C)))"
| PC3: "book_conj_formula \<Sigma> G A \<Longrightarrow> book_conj_formula \<Sigma> G B \<Longrightarrow>
    book_conj_theory_derivable \<Sigma> G S
      (book_conj_imp (book_conj_imp (book_conj_not G A) (book_conj_not G B)) (book_conj_imp B A))"
| UI: "book_in_language book_conj_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop) \<Longrightarrow>
    book_in_language book_conj_logical_type UNIV \<Sigma> G a \<sigma> \<Longrightarrow>
    book_conj_theory_derivable \<Sigma> G S
      (book_conj_imp (NApp (NLogical (BCMinimal (SBAll \<sigma>))) F) (NApp F a))"
| Beta: "book_conj_formula \<Sigma> G A \<Longrightarrow> book_conj_formula \<Sigma> G B \<Longrightarrow>
    (named_compatible_step book_printed_beta_contract A B \<or> named_compatible_step book_printed_beta_contract B A) \<Longrightarrow>
    book_conj_theory_derivable \<Sigma> G S (book_conj_imp A B)"
| Eta: "book_conj_formula \<Sigma> G A \<Longrightarrow> book_conj_formula \<Sigma> G B \<Longrightarrow>
    (named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A) \<Longrightarrow>
    book_conj_theory_derivable \<Sigma> G S (book_conj_imp A B)"
| MP: "book_conj_theory_derivable \<Sigma> G S A \<Longrightarrow>
    book_conj_theory_derivable \<Sigma> G S (book_conj_imp A B) \<Longrightarrow>
    book_conj_formula \<Sigma> G B \<Longrightarrow> book_conj_theory_derivable \<Sigma> G S B"
| Gen: "book_conj_theory_derivable \<Sigma> G S (book_conj_imp A B) \<Longrightarrow>
    book_conj_formula \<Sigma> G A \<Longrightarrow> book_conj_formula \<Sigma> G B \<Longrightarrow>
    n \<notin> named_fv A \<Longrightarrow> book_conj_theory_derivable \<Sigma> G S (book_conj_imp A (book_conj_all G n B))"
| AndI: "book_conj_formula \<Sigma> G A \<Longrightarrow> book_conj_formula \<Sigma> G B \<Longrightarrow>
    book_conj_theory_derivable \<Sigma> G S (book_conj_imp A (book_conj_imp B (book_conj_apply A B)))"
| AndE1: "book_conj_formula \<Sigma> G A \<Longrightarrow> book_conj_formula \<Sigma> G B \<Longrightarrow>
    book_conj_theory_derivable \<Sigma> G S (book_conj_imp (book_conj_apply A B) A)"
| AndE2: "book_conj_formula \<Sigma> G A \<Longrightarrow> book_conj_formula \<Sigma> G B \<Longrightarrow>
    book_conj_theory_derivable \<Sigma> G S (book_conj_imp (book_conj_apply A B) B)"

lemma book_conj_theory_UI_language:
  assumes predicate: "book_in_language book_conj_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and argument: "book_in_language book_conj_logical_type UNIV \<Sigma> G a \<sigma>"
  shows "book_conj_formula \<Sigma> G
    (book_conj_imp (NApp (NLogical (BCMinimal (SBAll \<sigma>))) F) (NApp F a))"
  by (rule book_conj_imp_language[OF book_language_App[OF book_conj_all_operator_language predicate]
    book_language_App[OF predicate argument]])

theorem book_conj_theory_derivable_language:
  assumes derivation: "book_conj_theory_derivable \<Sigma> G S A" and rich: "sg_rich G"
  shows "book_conj_formula \<Sigma> G A"
  using derivation
proof (induction rule: book_conj_theory_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.hyps(2))
next
  case PC1
  show ?case by (intro book_conj_imp_language; rule PC1.hyps)
next
  case PC2
  show ?case by (intro book_conj_imp_language; rule PC2.hyps)
next
  case PC3
  show ?case by (intro book_conj_imp_language)
    (rule book_conj_not_language[OF rich PC3.hyps(1)], rule book_conj_not_language[OF rich PC3.hyps(2)],
      rule PC3.hyps(2), rule PC3.hyps(1))
next
  case UI
  show ?case by (rule book_conj_theory_UI_language[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_conj_imp_language[OF Beta.hyps(1,2)])
next
  case Eta
  show ?case by (rule book_conj_imp_language[OF Eta.hyps(1,2)])
next
  case MP
  show ?case by (rule MP.hyps(3))
next
  case Gen
  show ?case by (rule book_conj_imp_language[OF Gen.hyps(2) book_conj_all_language[OF Gen.hyps(3)]])
next
  case AndI
  show ?case by (rule book_conj_imp_language[OF AndI.hyps(1)
    book_conj_imp_language[OF AndI.hyps(2) book_conj_apply_language[OF AndI.hyps]]])
next
  case AndE1
  show ?case by (rule book_conj_imp_language[OF book_conj_apply_language[OF AndE1.hyps] AndE1.hyps(1)])
next
  case AndE2
  show ?case by (rule book_conj_imp_language[OF book_conj_apply_language[OF AndE2.hyps] AndE2.hyps(2)])
qed

lemma book_conj_theory_derivable_mono:
  assumes derivation: "book_conj_theory_derivable \<Sigma> G S A" and inclusion: "S \<subseteq> T"
  shows "book_conj_theory_derivable \<Sigma> G T A"
  using derivation inclusion
proof (induction arbitrary: T rule: book_conj_theory_derivable.induct)
  case Assumption
  show ?case by (rule book_conj_theory_derivable.Assumption[
    OF subsetD[OF Assumption.prems Assumption.hyps(1)] Assumption.hyps(2)])
next
  case PC1
  show ?case by (rule book_conj_theory_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_conj_theory_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_conj_theory_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_conj_theory_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_conj_theory_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_conj_theory_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_conj_theory_derivable.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_conj_theory_derivable.Gen[OF Gen.IH[OF Gen.prems] Gen.hyps(2,3,4)])
next
  case AndI
  show ?case by (rule book_conj_theory_derivable.AndI[OF AndI.hyps])
next
  case AndE1
  show ?case by (rule book_conj_theory_derivable.AndE1[OF AndE1.hyps])
next
  case AndE2
  show ?case by (rule book_conj_theory_derivable.AndE2[OF AndE2.hyps])
qed

end
