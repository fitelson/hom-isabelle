theory Bacon_Source_Relational_Distribution_PC
  imports Bacon_Source_Relational_Quantifier_PC
begin

section \<open>Explicit native PC steps for quantified disjunction\<close>

lemma paper_R_named_H_ternary_PC:
  fixes P :: "nat sprop_template"
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and cl: "paper_R_in_language \<Sigma> G C Prop"
    and tautology: "sprop_tautology P"
  shows "paper_R_named_H \<Sigma> G (named_paper_prop_instance G (\<lambda>i. if i=0 then A else if i=1 then B else C) P)"
  by (rule paper_R_named_H_PC_template[OF rich tautology]; use al bl cl in auto)

lemma paper_R_named_H_or_cases:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and cl: "paper_R_in_language \<Sigma> G C Prop"
    and first: "paper_R_named_H \<Sigma> G (named_paper_imp G A C)"
    and second: "paper_R_named_H \<Sigma> G (named_paper_imp G B C)"
  shows "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_or A B) C)"
proof -
  have tautology: "sprop_tautology (SPImp (SPImp (SPAtom (0::nat)) (SPAtom 2))
    (SPImp (SPImp (SPAtom 1) (SPAtom 2)) (SPImp (SPOr (SPAtom 0) (SPAtom 1)) (SPAtom 2))))"
    by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_imp G A C)
    (named_paper_imp G (named_paper_imp G B C) (named_paper_imp G (named_paper_or A B) C)))"
    using paper_R_named_H_ternary_PC[OF rich al bl cl tautology] by simp
  show ?thesis by (rule paper_R_named_H_MP2[OF rich first second schema
    paper_R_named_paper_imp_language[OF rich paper_R_named_or_language[OF al bl] cl]])
qed

lemma paper_R_named_H_or_negative_antecedent:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and premise: "paper_R_named_H \<Sigma> G (named_paper_imp G A (named_paper_or B P))"
  shows "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_and A (named_paper_not P)) B)"
proof -
  have tautology: "sprop_tautology (SPImp (SPImp (SPAtom (0::nat)) (SPOr (SPAtom 1) (SPAtom 2)))
    (SPImp (SPAnd (SPAtom 0) (SPNot (SPAtom 2))) (SPAtom 1)))"
    by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_imp G A (named_paper_or B P))
    (named_paper_imp G (named_paper_and A (named_paper_not P)) B))"
    using paper_R_named_H_ternary_PC[OF rich al bl pl tautology] by simp
  show ?thesis by (rule paper_R_named_H.MP[OF premise schema paper_R_named_paper_imp_language[
    OF rich paper_R_named_and_language[OF al paper_R_named_not_language[OF pl]] bl]])
qed

lemma paper_R_named_H_or_restore:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and premise: "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_and A (named_paper_not P)) B)"
  shows "paper_R_named_H \<Sigma> G (named_paper_imp G A (named_paper_or B P))"
proof -
  have tautology: "sprop_tautology (SPImp (SPImp (SPAnd (SPAtom (0::nat)) (SPNot (SPAtom 2))) (SPAtom 1))
    (SPImp (SPAtom 0) (SPOr (SPAtom 1) (SPAtom 2))))"
    by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_imp G (named_paper_and A (named_paper_not P)) B)
    (named_paper_imp G A (named_paper_or B P)))"
    using paper_R_named_H_ternary_PC[OF rich al bl pl tautology] by simp
  show ?thesis by (rule paper_R_named_H.MP[OF premise schema
    paper_R_named_paper_imp_language[OF rich al paper_R_named_or_language[OF bl pl]]])
qed

lemma paper_R_named_H_iff_intro:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
    and first: "paper_R_named_H \<Sigma> G (named_paper_imp G A B)"
    and second: "paper_R_named_H \<Sigma> G (named_paper_imp G B A)"
  shows "paper_R_named_H \<Sigma> G (named_paper_iff G A B)"
proof -
  have tautology: "sprop_tautology (SPImp (SPImp (SPAtom (0::nat)) (SPAtom 1))
    (SPImp (SPImp (SPAtom 1) (SPAtom 0)) (SPIff (SPAtom 0) (SPAtom 1))))"
    by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_imp G A B)
    (named_paper_imp G (named_paper_imp G B A) (named_paper_iff G A B)))"
    using paper_R_named_H_binary_PC[OF rich al bl tautology] by simp
  show ?thesis by (rule paper_R_named_H_MP2[OF rich first second schema paper_R_named_paper_iff_language[OF rich al bl]])
qed

end
