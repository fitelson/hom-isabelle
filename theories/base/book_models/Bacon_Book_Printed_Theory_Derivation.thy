theory Bacon_Book_Printed_Theory_Derivation
  imports Bacon_Book_Minimal_Formula_Syntax Bacon_Book_Source_Reduction
begin

section \<open>The printed Chapter 5 theory rules\<close>

text \<open>
  S ⊢ₚ A is the closure of S under PC1, PC2, PC3, UI, printed β,
  η, MP and Gen (Bacon, Definition 5.1, pp.97–98). The β axiom
  uses the recursive free-for test printed in Definition 3.7, p.70,
  in an immediate contextual contraction in either direction.
  The η axiom also uses one immediate contextual contraction.

  This is a new independent judgment. It has no α constructor, no
  arbitrary-tautology constructor, and no leaf citing an old theory
  theorem. No source-reduction chain is an axiom. Generalization keeps
  the printed antecedent freshness condition and does not require
  freshness against all assumptions. Logical substitution, equivalence
  with another calculus, and model soundness are not assumed here.

  The formula abbreviation is only minimal-basis/UNIV language membership;
  no old derivability predicate is used to define it.
\<close>

abbreviation book_printed_theory_formula :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> bool" where
  "book_printed_theory_formula \<Sigma> G A \<equiv> book_in_language book_minimal_logical_type UNIV \<Sigma> G A Prop"

inductive book_printed_theory_derivable ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Assumption: "A \<in> S \<Longrightarrow> book_printed_theory_formula \<Sigma> G A \<Longrightarrow> book_printed_theory_derivable \<Sigma> G S A"
| PC1: "book_printed_theory_formula \<Sigma> G A \<Longrightarrow> book_printed_theory_formula \<Sigma> G B \<Longrightarrow>
    book_printed_theory_derivable \<Sigma> G S (book_imp A (book_imp B A))"
| PC2: "book_printed_theory_formula \<Sigma> G A \<Longrightarrow> book_printed_theory_formula \<Sigma> G B \<Longrightarrow>
    book_printed_theory_formula \<Sigma> G C \<Longrightarrow> book_printed_theory_derivable \<Sigma> G S
      (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)))"
| PC3: "book_printed_theory_formula \<Sigma> G A \<Longrightarrow> book_printed_theory_formula \<Sigma> G B \<Longrightarrow>
    book_printed_theory_derivable \<Sigma> G S (book_imp (book_imp (book_not G A) (book_not G B)) (book_imp B A))"
| UI: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop) \<Longrightarrow>
    book_in_language book_minimal_logical_type UNIV \<Sigma> G a \<sigma> \<Longrightarrow>
    book_printed_theory_derivable \<Sigma> G S (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
| Beta: "book_printed_theory_formula \<Sigma> G A \<Longrightarrow> book_printed_theory_formula \<Sigma> G B \<Longrightarrow>
    (named_compatible_step book_printed_beta_contract A B \<or> named_compatible_step book_printed_beta_contract B A) \<Longrightarrow>
    book_printed_theory_derivable \<Sigma> G S (book_imp A B)"
| Eta: "book_printed_theory_formula \<Sigma> G A \<Longrightarrow> book_printed_theory_formula \<Sigma> G B \<Longrightarrow>
    (named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A) \<Longrightarrow>
    book_printed_theory_derivable \<Sigma> G S (book_imp A B)"
| MP: "book_printed_theory_derivable \<Sigma> G S A \<Longrightarrow> book_printed_theory_derivable \<Sigma> G S (book_imp A B) \<Longrightarrow>
    book_printed_theory_formula \<Sigma> G B \<Longrightarrow> book_printed_theory_derivable \<Sigma> G S B"
| Gen: "book_printed_theory_derivable \<Sigma> G S (book_imp A B) \<Longrightarrow>
    book_printed_theory_formula \<Sigma> G A \<Longrightarrow> book_printed_theory_formula \<Sigma> G B \<Longrightarrow>
    n \<notin> named_fv A \<Longrightarrow> book_printed_theory_derivable \<Sigma> G S (book_imp A (book_all G n B))"

lemma book_printed_theory_UI_language:
  assumes predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and argument: "book_in_language book_minimal_logical_type UNIV \<Sigma> G a \<sigma>"
  shows "book_printed_theory_formula \<Sigma> G (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
proof -
  have quantifier: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NLogical (SBAll \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
    by (rule book_all_operator_language)
  show ?thesis by (rule book_imp_language[OF book_language_App[OF quantifier predicate]
    book_language_App[OF predicate argument]])
qed

theorem book_printed_theory_derivable_language:
  assumes derivation: "book_printed_theory_derivable \<Sigma> G S A" and rich: "sg_rich G"
  shows "book_printed_theory_formula \<Sigma> G A"
  using derivation
proof (induction rule: book_printed_theory_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.hyps(2))
next
  case PC1
  show ?case by (intro book_imp_language; rule PC1.hyps)
next
  case PC2
  show ?case by (intro book_imp_language; rule PC2.hyps)
next
  case PC3
  show ?case by (intro book_imp_language)
    (rule book_not_language[OF rich PC3.hyps(1)], rule book_not_language[OF rich PC3.hyps(2)],
      rule PC3.hyps(2), rule PC3.hyps(1))
next
  case UI
  show ?case by (rule book_printed_theory_UI_language[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_imp_language[OF Beta.hyps(1,2)])
next
  case Eta
  show ?case by (rule book_imp_language[OF Eta.hyps(1,2)])
next
  case MP
  show ?case by (rule MP.hyps(3))
next
  case Gen
  show ?case by (rule book_imp_language[OF Gen.hyps(2) book_all_language[OF Gen.hyps(3)]])
qed

section \<open>Monotonicity and replacement of derivable assumptions\<close>

lemma book_printed_theory_derivable_mono:
  assumes derivation: "book_printed_theory_derivable \<Sigma> G S A" and inclusion: "S \<subseteq> T"
  shows "book_printed_theory_derivable \<Sigma> G T A"
  using derivation inclusion
proof (induction rule: book_printed_theory_derivable.induct)
  case Assumption
  show ?case by (rule book_printed_theory_derivable.Assumption[OF subsetD[OF Assumption.prems Assumption.hyps(1)]
    Assumption.hyps(2)])
next
  case PC1
  show ?case by (rule book_printed_theory_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_printed_theory_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_printed_theory_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_printed_theory_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_printed_theory_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_printed_theory_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_printed_theory_derivable.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_printed_theory_derivable.Gen[OF Gen.IH[OF Gen.prems] Gen.hyps(2,3,4)])
qed

lemma book_printed_theory_derivable_cut:
  assumes derivation: "book_printed_theory_derivable \<Sigma> G T A"
    and replacements: "\<And>B. B \<in> T \<Longrightarrow> book_printed_theory_derivable \<Sigma> G S B"
  shows "book_printed_theory_derivable \<Sigma> G S A"
  using derivation replacements
proof (induction rule: book_printed_theory_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case PC1
  show ?case by (rule book_printed_theory_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_printed_theory_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_printed_theory_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_printed_theory_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_printed_theory_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_printed_theory_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_printed_theory_derivable.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_printed_theory_derivable.Gen[OF Gen.IH[OF Gen.prems] Gen.hyps(2,3,4)])
qed

end

