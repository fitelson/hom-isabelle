theory Bacon_Source_Relational_Propositional_Inversion
  imports Bacon_Source_Relational_Language_Inversion Bacon_Source_Relational_H
begin

section \<open>Only occurring template atoms inherit the instance guards\<close>

text \<open>
  A PC instance is guarded as a whole formula. Its occurring template
  atoms inherit R-language membership and assignment adequacy.
  Source: Figure 2, p.8. Unused entries of the template substitution
  are unrestricted. These are syntax and finite Boolean-template
  facts, not F theoremhood or semantic soundness assumptions.
\<close>

lemma paper_R_named_instance_language_atoms:
  assumes rich: "paper_R_rich G"
    and whole: "paper_R_in_language \<Sigma> G (named_paper_prop_instance G v P) Prop"
  shows "\<forall>a\<in>sprop_atoms P. paper_R_in_language \<Sigma> G (v a) Prop"
  using whole
proof (induction P)
  case (SPAtom a)
  show ?case using SPAtom.prems by (simp only: named_paper_prop_instance.simps sprop_atoms.simps singleton_iff; blast)
next
  case (SPNot P)
  have inner: "paper_R_in_language \<Sigma> G (named_paper_prop_instance G v P) Prop"
    by (rule paper_R_not_language_operand[OF SPNot.prems[unfolded named_paper_prop_instance.simps]])
  show ?case by (simp only: sprop_atoms.simps; rule SPNot.IH[OF inner])
next
  case (SPAnd P Q)
  have parts: "paper_R_in_language \<Sigma> G (named_paper_prop_instance G v P) Prop \<and>
    paper_R_in_language \<Sigma> G (named_paper_prop_instance G v Q) Prop"
    by (rule paper_R_and_language_operands[OF SPAnd.prems[unfolded named_paper_prop_instance.simps]])
  have left: "\<forall>a\<in>sprop_atoms P. paper_R_in_language \<Sigma> G (v a) Prop"
    by (rule SPAnd.IH(1)[OF conjunct1[OF parts]])
  have right: "\<forall>a\<in>sprop_atoms Q. paper_R_in_language \<Sigma> G (v a) Prop"
    by (rule SPAnd.IH(2)[OF conjunct2[OF parts]])
  show ?case using left right by (auto simp only: sprop_atoms.simps)
next
  case (SPOr P Q)
  have parts: "paper_R_in_language \<Sigma> G (named_paper_prop_instance G v P) Prop \<and>
    paper_R_in_language \<Sigma> G (named_paper_prop_instance G v Q) Prop"
    by (rule paper_R_or_language_operands[OF SPOr.prems[unfolded named_paper_prop_instance.simps]])
  have left: "\<forall>a\<in>sprop_atoms P. paper_R_in_language \<Sigma> G (v a) Prop"
    by (rule SPOr.IH(1)[OF conjunct1[OF parts]])
  have right: "\<forall>a\<in>sprop_atoms Q. paper_R_in_language \<Sigma> G (v a) Prop"
    by (rule SPOr.IH(2)[OF conjunct2[OF parts]])
  show ?case using left right by (auto simp only: sprop_atoms.simps)
next
  case (SPImp P Q)
  have parts: "paper_R_in_language \<Sigma> G (named_paper_prop_instance G v P) Prop \<and>
    paper_R_in_language \<Sigma> G (named_paper_prop_instance G v Q) Prop"
    by (rule paper_R_imp_language_operands[OF rich SPImp.prems[unfolded named_paper_prop_instance.simps]])
  have left: "\<forall>a\<in>sprop_atoms P. paper_R_in_language \<Sigma> G (v a) Prop"
    by (rule SPImp.IH(1)[OF conjunct1[OF parts]])
  have right: "\<forall>a\<in>sprop_atoms Q. paper_R_in_language \<Sigma> G (v a) Prop"
    by (rule SPImp.IH(2)[OF conjunct2[OF parts]])
  show ?case using left right by (auto simp only: sprop_atoms.simps)
next
  case (SPIff P Q)
  have parts: "paper_R_in_language \<Sigma> G (named_paper_prop_instance G v P) Prop \<and>
    paper_R_in_language \<Sigma> G (named_paper_prop_instance G v Q) Prop"
    by (rule paper_R_iff_language_operands[OF rich SPIff.prems[unfolded named_paper_prop_instance.simps]])
  have left: "\<forall>a\<in>sprop_atoms P. paper_R_in_language \<Sigma> G (v a) Prop"
    by (rule SPIff.IH(1)[OF conjunct1[OF parts]])
  have right: "\<forall>a\<in>sprop_atoms Q. paper_R_in_language \<Sigma> G (v a) Prop"
    by (rule SPIff.IH(2)[OF conjunct2[OF parts]])
  show ?case using left right by (auto simp only: sprop_atoms.simps)
qed

lemma paper_R_named_instance_adequacy_atoms:
  assumes whole: "named_adequate g (named_paper_prop_instance G v P)"
  shows "\<forall>a\<in>sprop_atoms P. named_adequate g (v a)"
  using whole
  by (induction P)
    (auto simp only: named_paper_prop_instance.simps sprop_atoms.simps paper_R_named_connective_adequacy)

end
