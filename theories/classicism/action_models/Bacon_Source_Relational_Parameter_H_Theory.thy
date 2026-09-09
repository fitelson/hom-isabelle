theory Bacon_Source_Relational_Parameter_H_Theory
  imports Bacon_Source_Relational_Parameter_Conversion_Axioms
begin

section \<open>All ten native H constructors preserve membership in T↑\<close>

theorem paper_R_parameter_theory_H:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and derivation: "paper_R_named_H (paper_R_naming_signature \<Sigma> D) G A"
  shows "A \<in> paper_R_parameter_theory \<Sigma> G D T"
  using derivation
proof (induction rule: paper_R_named_H.induct)
  case PC
  show ?case by (rule paper_R_parameter_theory_PC[OF rich theory_h PC.hyps])
next
  case UI
  show ?case by (rule paper_R_parameter_theory_UI[OF rich theory_h UI.hyps])
next
  case EG
  show ?case by (rule paper_R_parameter_theory_EG[OF rich theory_h EG.hyps])
next
  case Ref
  show ?case by (rule paper_R_parameter_theory_Ref[OF rich theory_h Ref.hyps])
next
  case LL
  show ?case by (rule paper_R_parameter_theory_LL[OF rich theory_h LL.hyps])
next
  case Beta
  show ?case by (rule paper_R_parameter_theory_Beta[OF rich theory_h Beta.hyps])
next
  case Eta
  show ?case by (rule paper_R_parameter_theory_Eta[OF rich theory_h Eta.hyps])
next
  case MP
  show ?case by (rule paper_R_parameter_theory_MP[OF rich theory_h MP.IH MP.hyps(3)])
next
  case Gen
  show ?case by (rule paper_R_parameter_theory_Gen[OF rich theory_h Gen.IH Gen.hyps(2-4)])
next
  case Inst
  show ?case by (rule paper_R_parameter_theory_Inst[OF rich theory_h Inst.IH Inst.hyps(2-4)])
qed

theorem paper_R_H_theory_parameter:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
  shows "paper_R_H_theory (paper_R_naming_signature \<Sigma> D) G (paper_R_parameter_theory \<Sigma> G D T)"
proof (rule paper_R_H_theoryI)
  fix A
  assume member: "A \<in> paper_R_parameter_theory \<Sigma> G D T"
  show "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    by (rule paper_R_parameter_theory_language[OF member])
next
  fix A
  assume derivation: "paper_R_named_H (paper_R_naming_signature \<Sigma> D) G A"
  show "A \<in> paper_R_parameter_theory \<Sigma> G D T"
    by (rule paper_R_parameter_theory_H[OF rich theory_h derivation])
next
  fix A B
  assume antecedent: "A \<in> paper_R_parameter_theory \<Sigma> G D T"
    and implication: "named_paper_imp G A B \<in> paper_R_parameter_theory \<Sigma> G D T"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G B Prop"
  show "B \<in> paper_R_parameter_theory \<Sigma> G D T"
    by (rule paper_R_parameter_theory_MP[OF rich theory_h antecedent implication language])
next
  fix P Q n \<sigma>
  assume premise: "named_paper_imp G P Q \<in> paper_R_parameter_theory \<Sigma> G D T"
    and variable: "G n = \<sigma>" and fresh: "n \<notin> named_fv P"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G
      (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))) Prop"
  show "named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)) \<in> paper_R_parameter_theory \<Sigma> G D T"
    by (rule paper_R_parameter_theory_Gen[OF rich theory_h premise variable fresh language])
next
  fix P Q n \<sigma>
  assume premise: "named_paper_imp G P Q \<in> paper_R_parameter_theory \<Sigma> G D T"
    and variable: "G n = \<sigma>" and fresh: "n \<notin> named_fv Q"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G
      (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop"
  show "named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q \<in> paper_R_parameter_theory \<Sigma> G D T"
    by (rule paper_R_parameter_theory_Inst[OF rich theory_h premise variable fresh language])
qed

text \<open>
  The parameter extension is now proved to be an H-theory in the
  expanded signature. H inclusion is obtained by the independent
  ten-constructor induction, not assumed during axiom transport.
  The separately proved PE closure still requires PE closure of T.
  No model, diagram, consistency, C or additional substitution
  invariant of old constants is a premise. Source: Figure 2 and n.73.
\<close>

end
