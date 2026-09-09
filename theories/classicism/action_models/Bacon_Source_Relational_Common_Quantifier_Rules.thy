theory Bacon_Source_Relational_Common_Quantifier_Rules
  imports Bacon_Source_Relational_Common_H
begin

section \<open>The common R theory is closed under Gen and Inst\<close>

text \<open>
  Common truth of P→Q implies common truth of P→∀n.Q when
  n∉FV(P), and of ∃n.P→Q when n∉FV(Q). Source: Figure 2,
  p.8, and the common-theory convention of Definition 3.1, p.44.
  Along with H inclusion and MP, these supply the H-theory closure
  required by the Equivalence-rule presentation on p.14.

  Each object is an independent R model. No arrows or intensionality
  condition is needed for these two rules. The whole conclusion's
  language guard is retained even for an empty object collection;
  no richness of G is inferred from a vacuous model-set hypothesis.
  These are all-assignment common-theory rules, not local rules on
  arbitrary assumptions at one fixed assignment.
\<close>

theorem paper_R_common_Gen:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_R_bbk_data_valid \<Sigma> G M"
    and premise: "named_paper_imp G P Q \<in> paper_R_common_theory \<Sigma> G Obj"
    and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv P"
    and language: "paper_R_in_language \<Sigma> G
      (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))) Prop"
  shows "named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)) \<in> paper_R_common_theory \<Sigma> G Obj"
proof (rule paper_R_common_theoryI[OF language])
  fix M g
  assume object: "M \<in> Obj" and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)))"
  interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
    "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF models[OF object]])
  have implication_language: "paper_R_in_language \<Sigma> G (named_paper_imp G P Q) Prop"
    by (rule paper_R_common_theory_language[OF premise])
  have parts: "paper_R_in_language \<Sigma> G P Prop \<and> paper_R_in_language \<Sigma> G Q Prop"
    by (rule paper_R_imp_language_operands[OF Model.stock_rich implication_language])
  have pl: "paper_R_in_language \<Sigma> G P Prop" by (rule conjunct1[OF parts])
  have ql: "paper_R_in_language \<Sigma> G Q Prop" by (rule conjunct2[OF parts])
  have conclusion_parts: "paper_R_in_language \<Sigma> G P Prop \<and>
      paper_R_in_language \<Sigma> G (named_paper_all \<sigma> (NLam n Q)) Prop"
    by (rule paper_R_imp_language_operands[OF Model.stock_rich language])
  have predicate: "paper_R_in_language \<Sigma> G (NLam n Q) (Arr \<sigma> Prop)"
    by (rule paper_R_all_language_operand[OF conjunct2[OF conclusion_parts]])
  have rt: "paper_R_type \<sigma>"
    by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have local_premise: "Model.paper_R_valid (named_paper_imp G P Q)"
  proof (rule Model.paper_R_validI[OF implication_language])
    fix k
    assume kt: "named_env_typed (paper_bbk_domain M) G k" and ka: "named_adequate k (named_paper_imp G P Q)"
    show "paper_bbk_valuation M (paper_bbk_denote M k (named_paper_imp G P Q))"
      by (rule paper_R_common_theory_truth[OF premise object kt ka])
  qed
  have conclusion: "Model.paper_R_valid (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)))"
    by (rule Model.paper_R_valid_Gen[OF pl ql nt rt fresh local_premise])
  show "paper_bbk_valuation M (paper_bbk_denote M g
      (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))))"
    by (rule Model.paper_R_validE[OF conclusion typed adequate])
qed

theorem paper_R_common_Inst:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_R_bbk_data_valid \<Sigma> G M"
    and premise: "named_paper_imp G P Q \<in> paper_R_common_theory \<Sigma> G Obj"
    and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv Q"
    and language: "paper_R_in_language \<Sigma> G
      (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop"
  shows "named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q \<in> paper_R_common_theory \<Sigma> G Obj"
proof (rule paper_R_common_theoryI[OF language])
  fix M g
  assume object: "M \<in> Obj" and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q)"
  interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
    "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF models[OF object]])
  have implication_language: "paper_R_in_language \<Sigma> G (named_paper_imp G P Q) Prop"
    by (rule paper_R_common_theory_language[OF premise])
  have parts: "paper_R_in_language \<Sigma> G P Prop \<and> paper_R_in_language \<Sigma> G Q Prop"
    by (rule paper_R_imp_language_operands[OF Model.stock_rich implication_language])
  have pl: "paper_R_in_language \<Sigma> G P Prop" by (rule conjunct1[OF parts])
  have ql: "paper_R_in_language \<Sigma> G Q Prop" by (rule conjunct2[OF parts])
  have conclusion_parts: "paper_R_in_language \<Sigma> G (named_paper_ex \<sigma> (NLam n P)) Prop \<and>
      paper_R_in_language \<Sigma> G Q Prop"
    by (rule paper_R_imp_language_operands[OF Model.stock_rich language])
  have predicate: "paper_R_in_language \<Sigma> G (NLam n P) (Arr \<sigma> Prop)"
    by (rule paper_R_ex_language_operand[OF conjunct1[OF conclusion_parts]])
  have rt: "paper_R_type \<sigma>"
    by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have local_premise: "Model.paper_R_valid (named_paper_imp G P Q)"
  proof (rule Model.paper_R_validI[OF implication_language])
    fix k
    assume kt: "named_env_typed (paper_bbk_domain M) G k" and ka: "named_adequate k (named_paper_imp G P Q)"
    show "paper_bbk_valuation M (paper_bbk_denote M k (named_paper_imp G P Q))"
      by (rule paper_R_common_theory_truth[OF premise object kt ka])
  qed
  have conclusion: "Model.paper_R_valid (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q)"
    by (rule Model.paper_R_valid_Inst[OF pl ql nt rt fresh local_premise])
  show "paper_bbk_valuation M (paper_bbk_denote M g
      (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q))"
    by (rule Model.paper_R_validE[OF conclusion typed adequate])
qed

end
