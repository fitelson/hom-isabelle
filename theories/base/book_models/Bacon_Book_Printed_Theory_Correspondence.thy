theory Bacon_Book_Printed_Theory_Correspondence
  imports Bacon_Book_Printed_Theory_Conversion Bacon_Book_Printed_Conversion_Correspondence
    Bacon_Book_Logic
begin

section \<open>The printed calculus embeds in the exact-capture presentation\<close>

text \<open>
  A printed-free-for β step is also an exact-capture β step.
  Induction on the independent printed derivation therefore preserves
  all nine constructors in the earlier presentation. S is unchanged,
  including any unused malformed premises; no global guard on S is
  needed. No model or completeness theorem is used.
\<close>

theorem book_printed_theory_to_theory:
  assumes derivation: "book_printed_theory_derivable \<Sigma> G S A"
  shows "book_theory_derivable \<Sigma> G S A"
  using derivation
proof (induction rule: book_printed_theory_derivable.induct)
  case Assumption
  show ?case by (rule book_theory_derivable.Assumption[OF Assumption.hyps])
next
  case PC1
  show ?case by (rule book_theory_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_theory_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_theory_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_theory_derivable.UI[OF UI.hyps])
next
  case (Beta A B S)
  have steps: "named_compatible_step named_beta_contract A B \<or>
    named_compatible_step named_beta_contract B A"
    using Beta.hyps(3) by (blast intro: book_printed_beta_step_named)
  show ?case by (rule book_theory_derivable.Beta[OF Beta.hyps(1,2) steps])
next
  case Eta
  show ?case by (rule book_theory_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_theory_derivable.MP[OF MP.IH MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_theory_derivable.Gen[OF Gen.IH Gen.hyps(2,3,4)])
qed

section \<open>Exact-capture derivations are reconstructed using printed steps\<close>

text \<open>
  Conversely, in a rich stock each exact-capture β step has an actual
  printed conversion in the declared language. The new calculus derives
  both formula implications for such a conversion by its own PC and
  immediate conversion rules. This handles the only changed axiom case.

  No source-reduction or whole-conversion AXIOM is added to the new
  judgment. Its β and η constructors still concern immediate contextual
  contractions. The rich-stock simulation is a proved metatheorem, not
  an old-theory theorem leaf or an α constructor.
\<close>

theorem book_theory_to_printed:
  assumes rich: "sg_rich G" and derivation: "book_theory_derivable \<Sigma> G S A"
  shows "book_printed_theory_derivable \<Sigma> G S A"
  using derivation
proof (induction rule: book_theory_derivable.induct)
  case Assumption
  show ?case by (rule book_printed_theory_derivable.Assumption[OF Assumption.hyps])
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
  case (Beta A B S)
  have conversion: "book_printed_conversion book_minimal_logical_type UNIV \<Sigma> G Prop A B"
  proof (rule disjE[OF Beta.hyps(3)])
    assume forward: "named_compatible_step named_beta_contract A B"
    show ?thesis by (rule book_exact_beta_step_printed_conversion[OF rich forward Beta.hyps(1)])
  next
    assume backward: "named_compatible_step named_beta_contract B A"
    have reversed: "book_printed_conversion book_minimal_logical_type UNIV \<Sigma> G Prop B A"
      by (rule book_exact_beta_step_printed_conversion[OF rich backward Beta.hyps(2)])
    show ?thesis by (rule book_printed_conversion.Sym[OF reversed])
  qed
  show ?case by (rule conjunct1[OF book_printed_theory_conversion_pair[OF conversion refl]])
next
  case Eta
  show ?case by (rule book_printed_theory_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_printed_theory_derivable.MP[OF MP.IH MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_printed_theory_derivable.Gen[OF Gen.IH Gen.hyps(2,3,4)])
qed

theorem book_theory_iff_printed:
  assumes rich: "sg_rich G"
  shows "book_theory_derivable \<Sigma> G S A \<longleftrightarrow> book_printed_theory_derivable \<Sigma> G S A"
  by (rule iffI, rule book_theory_to_printed[OF rich], assumption,
    rule book_printed_theory_to_theory, assumption)

corollary book_H_iff_printed:
  assumes rich: "sg_rich G"
  shows "book_H \<Sigma> G A \<longleftrightarrow> book_printed_theory_derivable \<Sigma> G {} A"
  by (simp only: book_H_iff_theory[OF rich] book_theory_iff_printed[OF rich])

end
