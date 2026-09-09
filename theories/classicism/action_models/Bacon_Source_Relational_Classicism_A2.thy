theory Bacon_Source_Relational_Classicism_A2
  imports Bacon_Source_Relational_Classicism_A2_Inst Bacon_Source_Relational_Classicism_A2_LE
    Bacon_Source_Relational_Language_Inversion
begin

section \<open>The A.2 abstraction-to-truth theorem for source-defined C\<close>

text \<open>
  If ⊢C P, then ⊢C(λv⃗.P)=(λv⃗.⊤) for every R prefix v⃗.
  We induct over the five constructors of the native p.12 presentation:
  H, H-certified Logical Equivalence, MP, Gen and Inst. Each induction
  hypothesis is uniform over prefixes, permitting the proved temporary
  closing-prefix arguments. Both quantifier eigenvariable guards are
  retained, and the needed R binder type is recovered from the rule's
  explicit conclusion-language premise.

  This establishes the property of Appendix A.2, pp.65–67, for the
  independently defined p.12 C. The separate Figures 3–4 presentation
  still requires its own correspondence proof. The general recursive
  Equivalence judgment, model validity and semantic completeness are
  not premises of this theorem.
\<close>

theorem paper_R_classicism_A2:
  assumes rich: "paper_R_rich G" and derivation: "paper_R_classicism_proves \<Sigma> G P"
    and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns P) (named_lam_vec ns (paper_R_named_top G)))"
  using derivation binders
proof (induction arbitrary: ns rule: paper_R_classicism_proves.induct)
  case (H P)
  show ?case by (rule paper_R_classicism_A2_H[OF rich H.hyps H.prems])
next
  case (Logical_Equivalence P Q vs)
  show ?case by (rule paper_R_classicism_A2_LE[OF rich Logical_Equivalence.hyps Logical_Equivalence.prems])
next
  case (MP Q P)
  have ql: "paper_R_in_language \<Sigma> G Q Prop"
    by (rule paper_R_classicism_proves_language[OF MP.hyps(1)])
  show ?case by (rule paper_R_classicism_A2_MP[OF rich MP.hyps(3) ql MP.prems MP.IH(1) MP.IH(2)])
next
  case (Gen P Q u \<sigma>)
  have operands: "paper_R_in_language \<Sigma> G P Prop \<and> paper_R_in_language \<Sigma> G Q Prop"
    by (rule paper_R_imp_language_operands[OF rich paper_R_classicism_proves_language[OF Gen.hyps(1)]])
  have quantified: "paper_R_in_language \<Sigma> G (named_paper_all \<sigma> (NLam u Q)) Prop"
    by (rule conjunct2[OF paper_R_imp_language_operands[OF rich Gen.hyps(4)]])
  have predicate: "paper_R_in_language \<Sigma> G (NLam u Q) (Arr \<sigma> Prop)"
    by (rule paper_R_all_language_operand[OF quantified])
  have rt: "paper_R_type \<sigma>"
    by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  show ?case by (rule paper_R_classicism_A2_Gen[OF rich conjunct1[OF operands] conjunct2[OF operands]
    Gen.hyps(2) rt Gen.hyps(3) Gen.prems Gen.IH])
next
  case (Inst P Q u \<sigma>)
  have operands: "paper_R_in_language \<Sigma> G P Prop \<and> paper_R_in_language \<Sigma> G Q Prop"
    by (rule paper_R_imp_language_operands[OF rich paper_R_classicism_proves_language[OF Inst.hyps(1)]])
  have quantified: "paper_R_in_language \<Sigma> G (named_paper_ex \<sigma> (NLam u P)) Prop"
    by (rule conjunct1[OF paper_R_imp_language_operands[OF rich Inst.hyps(4)]])
  have predicate: "paper_R_in_language \<Sigma> G (NLam u P) (Arr \<sigma> Prop)"
    by (rule paper_R_ex_language_operand[OF quantified])
  have rt: "paper_R_type \<sigma>"
    by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  show ?case by (rule paper_R_classicism_A2_Inst[OF rich conjunct1[OF operands] conjunct2[OF operands]
    Inst.hyps(2) rt Inst.hyps(3) Inst.prems Inst.IH])
qed

end
