theory Bacon_Source_Relational_Classicism_Theory_Minimality
  imports Bacon_Source_Relational_Global_Abstraction_Identity
    Bacon_Source_Relational_Classicism_Presentation
    Bacon_Source_Relational_Modalized_Functionality
begin

section \<open>H, PE and guarded ζ supply each Logical Equivalence instance\<close>

lemma paper_R_H_PE_zeta_logical_equivalence:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T" and zeta: "paper_R_zeta_closed \<Sigma> G T"
    and certificate: "paper_R_named_H \<Sigma> G (named_paper_iff G P Q)"
    and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
  shows "named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q) \<in> T"
proof -
  have equivalence: "named_paper_iff G P Q \<in> T"
    by (rule paper_R_H_theory_H[OF theory_h certificate])
  have identity: "named_paper_eq Prop P Q \<in> T"
    by (rule paper_R_PE_closedD[OF pe pl ql equivalence])
  have result: "Prop \<noteq> Ind" by simp
  show ?thesis by (rule paper_R_H_zeta_lam_vec_identity[
    OF rich theory_h zeta pl ql binders result identity])
qed

section \<open>Every H-theory closed under PE and ζ contains native C\<close>

theorem paper_R_classicism_in_H_PE_zeta:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T" and zeta: "paper_R_zeta_closed \<Sigma> G T"
    and derivation: "paper_R_classicism_proves \<Sigma> G A"
  shows "A \<in> T"
  using derivation
proof (induction rule: paper_R_classicism_proves.induct)
  case H
  show ?case by (rule paper_R_H_theory_H[OF theory_h H.hyps])
next
  case Logical_Equivalence
  show ?case by (rule paper_R_H_PE_zeta_logical_equivalence[
    OF rich theory_h pe zeta Logical_Equivalence.hyps])
next
  case MP
  show ?case by (rule paper_R_H_theory_MP[OF theory_h MP.IH MP.hyps(3)])
next
  case Gen
  show ?case by (rule paper_R_H_theory_Gen[OF theory_h Gen.IH Gen.hyps(2-4)])
next
  case Inst
  show ?case by (rule paper_R_H_theory_Inst[OF theory_h Inst.IH Inst.hyps(2-4)])
qed

corollary paper_R_H_PE_zeta_modalized_functionality:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T" and zeta: "paper_R_zeta_closed \<Sigma> G T"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and variable: "G z = \<sigma>"
    and fresh_F: "z \<notin> named_fv F" and fresh_H: "z \<notin> named_fv H"
  shows "named_paper_imp G
      (paper_R_named_box G
        (named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp F (NVar z)) (NApp H (NVar z))))))
      (named_paper_eq (Arr \<sigma> \<tau>) F H) \<in> T"
  by (rule paper_R_classicism_in_H_PE_zeta[OF rich theory_h pe zeta
    paper_R_classicism_modalized_functionality[OF rich fl hl variable fresh_F fresh_H]])

text \<open>
  This is the source p.12 least-H-theory definition of C, contained
  in every supplied H-theory with PE and the precisely guarded ζ
  closure of pp.14–16. The proof follows the five native C
  constructors. In particular, Logical Equivalence is obtained from
  an H certificate before global abstraction closure is applied.

  Modalized Functionality is then inherited from its independent
  native C proof, giving the generic-theory instance used in p.52
  n.73. No semantic model, completeness, F-type extension, local
  ζ rule, or substitution invariance of old constants is assumed.
\<close>

end
