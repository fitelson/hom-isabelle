theory Bacon_Source_Relational_H_Soundness
  imports Bacon_Source_Relational_Propositional_Truth
    Bacon_Source_Relational_Basic_Axiom_Validity
    Bacon_Source_Relational_Conversion_Truth Bacon_Source_Relational_Validity_Rules
begin

section \<open>Soundness of the independent R presentation of H\<close>

text \<open>
  If ⊢Hᴿ A, then M⊨A for every independent R BBK model M.
  Source: Theorem 3.2, pp.44–45, with Figure 2, p.8, and the
  default type system R of §1.1. The proof follows exactly the
  ten constructors of the independently defined calculus.

  Each semantic axiom/rule was proved over R carriers and typed
  partial assignments. MP uses an R-supported extension; Gen and
  Inst use typed binder updates. No F model extension, full-F
  soundness theorem, proof conservativity, C judgment or model
  existence premise is invoked. This is soundness only: R model
  existence for arbitrary consistent theories and completeness
  remain separate obligations.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_named_H_soundness:
  assumes derivation: "paper_R_named_H signature stock A"
  shows "paper_R_valid A"
  using derivation
proof (induction rule: paper_R_named_H.induct)
  case PC
  show ?case
    by (rule paper_R_validI[OF paper_R_named_PC_language[OF PC.hyps]],
      rule paper_R_named_PC_truth[OF PC.hyps]; assumption)
next
  case UI
  show ?case by (rule paper_R_UI_valid[OF UI.hyps])
next
  case EG
  show ?case by (rule paper_R_EG_valid[OF EG.hyps])
next
  case Ref
  show ?case by (rule paper_R_Ref_valid[OF Ref.hyps])
next
  case LL
  show ?case by (rule paper_R_LL_valid[OF LL.hyps])
next
  case (Beta A B)
  have at: "paper_R_has_type stock A Prop"
    using Beta.hyps(1) unfolding paper_R_in_language_def by (rule conjunct1)
  have bt: "paper_R_has_type stock B Prop"
    using Beta.hyps(2) unfolding paper_R_in_language_def by (rule conjunct1)
  have conversion: "paper_R_raw_beta_eta stock Prop A B"
    by (rule paper_R_raw_beta_eta.Beta[OF at bt Beta.hyps(3)])
  show ?case by (rule paper_R_conversion_biconditional_valid[OF conversion Beta.hyps(1,2)])
next
  case (Eta A B)
  have at: "paper_R_has_type stock A Prop"
    using Eta.hyps(1) unfolding paper_R_in_language_def by (rule conjunct1)
  have bt: "paper_R_has_type stock B Prop"
    using Eta.hyps(2) unfolding paper_R_in_language_def by (rule conjunct1)
  have conversion: "paper_R_raw_beta_eta stock Prop A B"
    by (rule paper_R_raw_beta_eta.Eta[OF at bt Eta.hyps(3)])
  show ?case by (rule paper_R_conversion_biconditional_valid[OF conversion Eta.hyps(1,2)])
next
  case MP
  show ?case by (rule paper_R_valid_MP[
    OF paper_R_valid_language[OF MP.IH(1)] MP.hyps(3) MP.IH(1,2)])
next
  case (Gen P Q n \<sigma>)
  have operands: "paper_R_in_language signature stock P Prop \<and>
    paper_R_in_language signature stock Q Prop"
    by (rule paper_R_imp_language_operands[OF stock_rich paper_R_valid_language[OF Gen.IH]])
  have quantifier: "paper_R_in_language signature stock (named_paper_all \<sigma> (NLam n Q)) Prop"
    by (rule conjunct2[OF paper_R_imp_language_operands[OF stock_rich Gen.hyps(4)]])
  have predicate: "paper_R_in_language signature stock (NLam n Q) (Arr \<sigma> Prop)"
    by (rule paper_R_all_language_operand[OF quantifier])
  have rt: "paper_R_type \<sigma>"
    by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  show ?case by (rule paper_R_valid_Gen[
    OF conjunct1[OF operands] conjunct2[OF operands] Gen.hyps(2) rt Gen.hyps(3) Gen.IH])
next
  case (Inst P Q n \<sigma>)
  have operands: "paper_R_in_language signature stock P Prop \<and>
    paper_R_in_language signature stock Q Prop"
    by (rule paper_R_imp_language_operands[OF stock_rich paper_R_valid_language[OF Inst.IH]])
  have quantifier: "paper_R_in_language signature stock (named_paper_ex \<sigma> (NLam n P)) Prop"
    by (rule conjunct1[OF paper_R_imp_language_operands[OF stock_rich Inst.hyps(4)]])
  have predicate: "paper_R_in_language signature stock (NLam n P) (Arr \<sigma> Prop)"
    by (rule paper_R_ex_language_operand[OF quantifier])
  have rt: "paper_R_type \<sigma>"
    by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  show ?case by (rule paper_R_valid_Inst[
    OF conjunct1[OF operands] conjunct2[OF operands] Inst.hyps(2) rt Inst.hyps(3) Inst.IH])
qed

end

end
