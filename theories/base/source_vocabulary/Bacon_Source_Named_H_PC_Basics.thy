theory Bacon_Source_Named_H_PC_Basics
  imports Bacon_Source_Named_H Bacon_Source_Named_Logical_Language
begin

section \<open>Native propositional instances and biconditional proof schemata\<close>

text \<open>
  PC gives A↔A, (A↔B)→(B↔A),
  (A↔B)→((B↔C)→(A↔C)), and (A↔B)→(A→B).
  Source: Bacon–Dorr Figure 2, p.8, with the literal → and ↔ operators
  of Figure 1, p.6. Every displayed constituent is a formula in ℒ(Σ).

  Representation. Boolean tautology is checked on a finite template,
  instantiated directly by native named formulas. The induction below
  constructs its language guard from just the occurring atom guards.
  No source-H translation, model, or β simplification is used.
\<close>

lemma named_paper_prop_instance_language:
  assumes rich: "sg_rich G"
    and atoms: "\<And>a. a \<in> sprop_atoms P \<Longrightarrow> named_in_language paper_logical_type \<Sigma> G (v a) Prop"
  shows "named_in_language paper_logical_type \<Sigma> G (named_paper_prop_instance G v P) Prop"
  using atoms
proof (induction P)
  case (SPAtom a)
  show ?case by (simp only: named_paper_prop_instance.simps; rule SPAtom.prems) simp
next
  case (SPNot P)
  have body: "named_in_language paper_logical_type \<Sigma> G (named_paper_prop_instance G v P) Prop"
    by (rule SPNot.IH) (use SPNot.prems in auto)
  show ?case by (simp only: named_paper_prop_instance.simps; rule named_paper_not_language[OF body])
next
  case (SPAnd P Q)
  have left: "named_in_language paper_logical_type \<Sigma> G (named_paper_prop_instance G v P) Prop"
    by (rule SPAnd.IH(1)) (use SPAnd.prems in auto)
  have right: "named_in_language paper_logical_type \<Sigma> G (named_paper_prop_instance G v Q) Prop"
    by (rule SPAnd.IH(2)) (use SPAnd.prems in auto)
  show ?case by (simp only: named_paper_prop_instance.simps; rule named_paper_and_language[OF left right])
next
  case (SPOr P Q)
  have left: "named_in_language paper_logical_type \<Sigma> G (named_paper_prop_instance G v P) Prop"
    by (rule SPOr.IH(1)) (use SPOr.prems in auto)
  have right: "named_in_language paper_logical_type \<Sigma> G (named_paper_prop_instance G v Q) Prop"
    by (rule SPOr.IH(2)) (use SPOr.prems in auto)
  show ?case by (simp only: named_paper_prop_instance.simps; rule named_paper_or_language[OF left right])
next
  case (SPImp P Q)
  have left: "named_in_language paper_logical_type \<Sigma> G (named_paper_prop_instance G v P) Prop"
    by (rule SPImp.IH(1)) (use SPImp.prems in auto)
  have right: "named_in_language paper_logical_type \<Sigma> G (named_paper_prop_instance G v Q) Prop"
    by (rule SPImp.IH(2)) (use SPImp.prems in auto)
  show ?case by (simp only: named_paper_prop_instance.simps; rule named_paper_imp_language[OF rich left right])
next
  case (SPIff P Q)
  have left: "named_in_language paper_logical_type \<Sigma> G (named_paper_prop_instance G v P) Prop"
    by (rule SPIff.IH(1)) (use SPIff.prems in auto)
  have right: "named_in_language paper_logical_type \<Sigma> G (named_paper_prop_instance G v Q) Prop"
    by (rule SPIff.IH(2)) (use SPIff.prems in auto)
  show ?case by (simp only: named_paper_prop_instance.simps; rule named_paper_iff_language[OF rich left right])
qed

lemma paper_named_H_PC_instance:
  fixes P :: "nat sprop_template"
  assumes rich: "sg_rich G" and tautology: "sprop_tautology P"
    and atoms: "\<And>a. a \<in> sprop_atoms P \<Longrightarrow> named_in_language paper_logical_type \<Sigma> G (v a) Prop"
  shows "paper_named_H \<Sigma> G (named_paper_prop_instance G v P)"
  by (rule paper_named_H.PC[OF named_PC_instance[OF tautology named_paper_prop_instance_language[OF rich atoms]]])

lemma paper_named_H_iff_refl:
  assumes rich: "sg_rich G" and A: "named_in_language paper_logical_type \<Sigma> G A Prop"
  shows "paper_named_H \<Sigma> G (named_paper_iff G A A)"
proof -
  let ?P = "SPIff (SPAtom (0 :: nat)) (SPAtom 0)"
  have taut: "sprop_tautology ?P" by (simp add: sprop_tautology_def)
  have instantiated: "paper_named_H \<Sigma> G (named_paper_prop_instance G (\<lambda>_. A) ?P)"
    by (rule paper_named_H_PC_instance[OF rich taut]) (rule A)
  show ?thesis using instantiated by simp
qed

lemma paper_named_H_iff_sym_schema:
  assumes rich: "sg_rich G" and A: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "named_in_language paper_logical_type \<Sigma> G B Prop"
  shows "paper_named_H \<Sigma> G (named_paper_imp G (named_paper_iff G A B) (named_paper_iff G B A))"
proof -
  let ?P = "SPImp (SPIff (SPAtom (0 :: nat)) (SPAtom 1)) (SPIff (SPAtom 1) (SPAtom 0))"
  let ?v = "\<lambda>n. if n = 0 then A else B"
  have taut: "sprop_tautology ?P" by (auto simp: sprop_tautology_def)
  have atoms: "named_in_language paper_logical_type \<Sigma> G (?v n) Prop" for n
    using A B by (cases "n = 0") simp_all
  have instantiated: "paper_named_H \<Sigma> G (named_paper_prop_instance G ?v ?P)"
    by (rule paper_named_H_PC_instance[OF rich taut]) (rule atoms)
  show ?thesis using instantiated by simp
qed

lemma paper_named_H_iff_trans_schema:
  assumes rich: "sg_rich G" and A: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "named_in_language paper_logical_type \<Sigma> G B Prop"
    and C: "named_in_language paper_logical_type \<Sigma> G C Prop"
  shows "paper_named_H \<Sigma> G (named_paper_imp G (named_paper_iff G A B)
    (named_paper_imp G (named_paper_iff G B C) (named_paper_iff G A C)))"
proof -
  let ?P = "SPImp (SPIff (SPAtom (0 :: nat)) (SPAtom 1))
    (SPImp (SPIff (SPAtom 1) (SPAtom 2)) (SPIff (SPAtom 0) (SPAtom 2)))"
  let ?v = "\<lambda>n. if n = 0 then A else if n = 1 then B else C"
  have taut: "sprop_tautology ?P" by (auto simp: sprop_tautology_def)
  have atoms: "named_in_language paper_logical_type \<Sigma> G (?v n) Prop" for n
    using A B C by (auto split: if_splits)
  have instantiated: "paper_named_H \<Sigma> G (named_paper_prop_instance G ?v ?P)"
    by (rule paper_named_H_PC_instance[OF rich taut]) (rule atoms)
  show ?thesis using instantiated by simp
qed

lemma paper_named_H_iff_elim_schema:
  assumes rich: "sg_rich G" and A: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "named_in_language paper_logical_type \<Sigma> G B Prop"
  shows "paper_named_H \<Sigma> G (named_paper_imp G (named_paper_iff G A B) (named_paper_imp G A B))"
proof -
  let ?P = "SPImp (SPIff (SPAtom (0 :: nat)) (SPAtom 1)) (SPImp (SPAtom 0) (SPAtom 1))"
  let ?v = "\<lambda>n. if n = 0 then A else B"
  have taut: "sprop_tautology ?P" by (auto simp: sprop_tautology_def)
  have atoms: "named_in_language paper_logical_type \<Sigma> G (?v n) Prop" for n
    using A B by (cases "n = 0") simp_all
  have instantiated: "paper_named_H \<Sigma> G (named_paper_prop_instance G ?v ?P)"
    by (rule paper_named_H_PC_instance[OF rich taut]) (rule atoms)
  show ?thesis using instantiated by simp
qed

end
