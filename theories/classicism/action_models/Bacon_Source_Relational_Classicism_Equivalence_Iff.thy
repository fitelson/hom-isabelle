theory Bacon_Source_Relational_Classicism_Equivalence_Iff
  imports Bacon_Source_Relational_Classicism_A3
begin

section \<open>The p.12 definition and p.14 Equivalence-rule presentation coincide\<close>

text \<open>
  The earlier inclusion sent source-defined C into the independent
  Equivalence-rule presentation. For the converse, induct over that
  presentation: preserve H, MP, Gen and Inst by the p.12 constructors,
  and use the independently proved A.3 closure theorem for Equivalence.

  Source: p.14 and Appendix A, pp.65–67. Both judgments retain the
  same R signature, variable stock, literal connectives and typed
  partial-prefix conventions. The finite Boolean and Classicist
  identities of Figures 3–4 are not silently identified with either
  judgment by this theorem; their correspondence remains separate.
\<close>

theorem paper_R_equivalence_into_classicism:
  assumes rich: "paper_R_rich G" and derivation: "paper_R_equivalence_proves \<Sigma> G A"
  shows "paper_R_classicism_proves \<Sigma> G A"
  using derivation
proof (induction rule: paper_R_equivalence_proves.induct)
  case H
  show ?case by (rule paper_R_classicism_proves.H[OF H.hyps])
next
  case MP
  show ?case by (rule paper_R_classicism_proves.MP[OF MP.IH MP.hyps(3)])
next
  case Gen
  show ?case by (rule paper_R_classicism_proves.Gen[OF Gen.IH Gen.hyps(2,3,4)])
next
  case Inst
  show ?case by (rule paper_R_classicism_proves.Inst[OF Inst.IH Inst.hyps(2,3,4)])
next
  case Equivalence
  show ?case by (rule paper_R_classicism_A3[OF rich Equivalence.IH Equivalence.hyps(2,3,4)])
qed

theorem paper_R_classicism_equivalence_iff:
  assumes rich: "paper_R_rich G"
  shows "paper_R_classicism_proves \<Sigma> G A \<longleftrightarrow> paper_R_equivalence_proves \<Sigma> G A"
  by (rule iffI; (rule paper_R_classicism_into_equivalence | rule paper_R_equivalence_into_classicism[OF rich]); assumption)

end
