theory Bacon_Source_Relational_Quantifier_PC
  imports Bacon_Source_Relational_Boolean_PC
begin

section \<open>Native PC consequences for the quantifier-duality proof\<close>

lemma paper_R_named_H_MP2:
  assumes rich: "paper_R_rich G" and first: "paper_R_named_H \<Omega> G A"
    and second: "paper_R_named_H \<Omega> G B"
    and conditional: "paper_R_named_H \<Omega> G (named_paper_imp G A (named_paper_imp G B C))"
    and conclusion: "paper_R_in_language \<Omega> G C Prop"
  shows "paper_R_named_H \<Omega> G C"
proof -
  have bl: "paper_R_in_language \<Omega> G B Prop" by (rule paper_R_named_H_language[OF second])
  have intermediate: "paper_R_named_H \<Omega> G (named_paper_imp G B C)"
    by (rule paper_R_named_H.MP[OF first conditional paper_R_named_paper_imp_language[OF rich bl conclusion]])
  show ?thesis by (rule paper_R_named_H.MP[OF second intermediate conclusion])
qed

lemma paper_R_named_H_imp_trans:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Omega> G A Prop"
    and bl: "paper_R_in_language \<Omega> G B Prop" and cl: "paper_R_in_language \<Omega> G C Prop"
    and first: "paper_R_named_H \<Omega> G (named_paper_imp G A B)"
    and second: "paper_R_named_H \<Omega> G (named_paper_imp G B C)"
  shows "paper_R_named_H \<Omega> G (named_paper_imp G A C)"
proof -
  let ?P = "SPImp (SPImp (SPAtom (0::nat)) (SPAtom 1))
    (SPImp (SPImp (SPAtom 1) (SPAtom 2)) (SPImp (SPAtom 0) (SPAtom 2)))"
  let ?v = "\<lambda>i. if i=0 then A else if i=1 then B else C"
  have tautology: "sprop_tautology ?P" by (auto simp: sprop_tautology_def)
  have instance_proof: "paper_R_named_H \<Omega> G (named_paper_prop_instance G ?v ?P)"
    by (rule paper_R_named_H_PC_template[OF rich tautology]; use al bl cl in auto)
  have schema: "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_imp G A B)
    (named_paper_imp G (named_paper_imp G B C) (named_paper_imp G A C)))"
    using instance_proof by simp
  show ?thesis by (rule paper_R_named_H_MP2[
    OF rich first second schema paper_R_named_paper_imp_language[OF rich al cl]])
qed

lemma paper_R_named_H_contraposition:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Omega> G A Prop"
    and bl: "paper_R_in_language \<Omega> G B Prop"
    and premise: "paper_R_named_H \<Omega> G (named_paper_imp G A B)"
  shows "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_not B) (named_paper_not A))"
proof -
  have tautology: "sprop_tautology (SPImp (SPImp (SPAtom (0::nat)) (SPAtom 1))
    (SPImp (SPNot (SPAtom 1)) (SPNot (SPAtom 0))))" by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_imp G A B)
    (named_paper_imp G (named_paper_not B) (named_paper_not A)))"
    using paper_R_named_H_binary_PC[OF rich al bl tautology] by simp
  show ?thesis by (rule paper_R_named_H.MP[OF premise schema paper_R_named_paper_imp_language[
    OF rich paper_R_named_not_language[OF bl] paper_R_named_not_language[OF al]]])
qed

lemma paper_R_named_H_negative_contraposition:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Omega> G A Prop"
    and bl: "paper_R_in_language \<Omega> G B Prop"
    and premise: "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_not A) B)"
  shows "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_not B) A)"
proof -
  have tautology: "sprop_tautology (SPImp (SPImp (SPNot (SPAtom (0::nat))) (SPAtom 1))
    (SPImp (SPNot (SPAtom 1)) (SPAtom 0)))" by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_imp G (named_paper_not A) B)
    (named_paper_imp G (named_paper_not B) A))"
    using paper_R_named_H_binary_PC[OF rich al bl tautology] by simp
  show ?thesis by (rule paper_R_named_H.MP[OF premise schema paper_R_named_paper_imp_language[
    OF rich paper_R_named_not_language[OF bl] al]])
qed

lemma paper_R_named_H_duality_from_implications:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Omega> G A Prop"
    and xl: "paper_R_in_language \<Omega> G X Prop"
    and first: "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_not X) A)"
    and second: "paper_R_named_H \<Omega> G (named_paper_imp G X (named_paper_not A))"
  shows "paper_R_named_H \<Omega> G (named_paper_iff G (named_paper_not A) X)"
proof -
  have tautology: "sprop_tautology (SPImp (SPImp (SPNot (SPAtom (1::nat))) (SPAtom 0))
    (SPImp (SPImp (SPAtom 1) (SPNot (SPAtom 0))) (SPIff (SPNot (SPAtom 0)) (SPAtom 1))))"
    by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_imp G (named_paper_not X) A)
    (named_paper_imp G (named_paper_imp G X (named_paper_not A)) (named_paper_iff G (named_paper_not A) X)))"
    using paper_R_named_H_binary_PC[OF rich al xl tautology] by simp
  show ?thesis by (rule paper_R_named_H_MP2[OF rich first second schema
    paper_R_named_paper_iff_language[OF rich paper_R_named_not_language[OF al] xl]])
qed

end
