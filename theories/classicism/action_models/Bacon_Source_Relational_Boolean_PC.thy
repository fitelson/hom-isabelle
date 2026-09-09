theory Bacon_Source_Relational_Boolean_PC
  imports Bacon_Source_Relational_Deduction
begin

section \<open>Typed native PC templates, without a semantic model\<close>

lemma paper_R_named_prop_instance_language:
  assumes rich: "paper_R_rich G"
    and atoms: "\<And>i. i \<in> sprop_atoms P \<Longrightarrow> paper_R_in_language \<Omega> G (v i) Prop"
  shows "paper_R_in_language \<Omega> G (named_paper_prop_instance G v P) Prop"
  using atoms
  by (induction P)
    (auto intro: paper_R_named_not_language paper_R_named_and_language paper_R_named_or_language
      paper_R_named_paper_imp_language[OF rich] paper_R_named_paper_iff_language[OF rich])

lemma paper_R_named_H_PC_template:
  fixes P :: "nat sprop_template"
  assumes rich: "paper_R_rich G" and tautology: "sprop_tautology P"
    and atoms: "\<And>i. i \<in> sprop_atoms P \<Longrightarrow> paper_R_in_language \<Omega> G (v i) Prop"
  shows "paper_R_named_H \<Omega> G (named_paper_prop_instance G v P)"
  by (rule paper_R_named_H_PC_instance[
    OF paper_R_named_prop_instance_language[OF rich atoms] tautology refl])

lemma paper_R_named_H_binary_PC:
  fixes P :: "nat sprop_template"
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Omega> G A Prop"
    and bl: "paper_R_in_language \<Omega> G B Prop" and tautology: "sprop_tautology P"
  shows "paper_R_named_H \<Omega> G (named_paper_prop_instance G (\<lambda>i. if i=0 then A else B) P)"
  by (rule paper_R_named_H_PC_template[OF rich tautology]; use al bl in auto)

section \<open>The explicit Boolean certificates used by membership proofs\<close>

text \<open>
  Each result below is an instance of native R-PC with its displayed
  Boolean template. The object connectives remain literal named terms.
  Source: Figure 2, p.8; the propositional step in the valuation
  construction of Theorem 3.2, footnote 64, p.45.
  No semantic R-BBK truth law or identity-from-equivalence rule is used.
\<close>

lemma paper_R_named_H_and_intro:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Omega> G A Prop"
    and bl: "paper_R_in_language \<Omega> G B Prop"
  shows "paper_R_named_H \<Omega> G (named_paper_imp G A (named_paper_imp G B (named_paper_and A B)))"
proof -
  have tautology: "sprop_tautology (SPImp (SPAtom (0::nat)) (SPImp (SPAtom 1) (SPAnd (SPAtom 0) (SPAtom 1))))"
    by (simp add: sprop_tautology_def)
  show ?thesis using paper_R_named_H_binary_PC[OF rich al bl tautology] by simp
qed

lemma paper_R_named_H_and_left:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Omega> G A Prop"
    and bl: "paper_R_in_language \<Omega> G B Prop"
  shows "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_and A B) A)"
proof -
  have tautology: "sprop_tautology (SPImp (SPAnd (SPAtom (0::nat)) (SPAtom 1)) (SPAtom 0))"
    by (simp add: sprop_tautology_def)
  show ?thesis using paper_R_named_H_binary_PC[OF rich al bl tautology] by simp
qed

lemma paper_R_named_H_and_right:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Omega> G A Prop"
    and bl: "paper_R_in_language \<Omega> G B Prop"
  shows "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_and A B) B)"
proof -
  have tautology: "sprop_tautology (SPImp (SPAnd (SPAtom (0::nat)) (SPAtom 1)) (SPAtom 1))"
    by (simp add: sprop_tautology_def)
  show ?thesis using paper_R_named_H_binary_PC[OF rich al bl tautology] by simp
qed

lemma paper_R_named_H_or_left:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Omega> G A Prop"
    and bl: "paper_R_in_language \<Omega> G B Prop"
  shows "paper_R_named_H \<Omega> G (named_paper_imp G A (named_paper_or A B))"
proof -
  have tautology: "sprop_tautology (SPImp (SPAtom (0::nat)) (SPOr (SPAtom 0) (SPAtom 1)))"
    by (simp add: sprop_tautology_def)
  show ?thesis using paper_R_named_H_binary_PC[OF rich al bl tautology] by simp
qed

lemma paper_R_named_H_or_right:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Omega> G A Prop"
    and bl: "paper_R_in_language \<Omega> G B Prop"
  shows "paper_R_named_H \<Omega> G (named_paper_imp G B (named_paper_or A B))"
proof -
  have tautology: "sprop_tautology (SPImp (SPAtom (1::nat)) (SPOr (SPAtom 0) (SPAtom 1)))"
    by (simp add: sprop_tautology_def)
  show ?thesis using paper_R_named_H_binary_PC[OF rich al bl tautology] by simp
qed

lemma paper_R_named_H_or_resolve:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Omega> G A Prop"
    and bl: "paper_R_in_language \<Omega> G B Prop"
  shows "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_or A B) (named_paper_imp G (named_paper_not A) B))"
proof -
  have tautology: "sprop_tautology (SPImp (SPOr (SPAtom (0::nat)) (SPAtom 1)) (SPImp (SPNot (SPAtom 0)) (SPAtom 1)))"
    by (auto simp: sprop_tautology_def)
  show ?thesis using paper_R_named_H_binary_PC[OF rich al bl tautology] by simp
qed

end
