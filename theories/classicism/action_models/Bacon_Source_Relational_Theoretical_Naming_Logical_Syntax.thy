theory Bacon_Source_Relational_Theoretical_Naming_Logical_Syntax
  imports Bacon_Source_Relational_Naming_Replacement Bacon_Source_Relational_H
begin

section \<open>Chart replacement preserves the literal logical syntax\<close>

lemma paper_R_parameter_replace_primitive:
  "paper_R_naming_replace x (named_paper_not A) = named_paper_not (paper_R_naming_replace x A)"
  "paper_R_naming_replace x (named_paper_and A B) =
    named_paper_and (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
  "paper_R_naming_replace x (named_paper_or A B) =
    named_paper_or (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
  "paper_R_naming_replace x (named_paper_eq \<sigma> A B) =
    named_paper_eq \<sigma> (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
  "paper_R_naming_replace x (named_paper_all \<sigma> A) =
    named_paper_all \<sigma> (paper_R_naming_replace x A)"
  "paper_R_naming_replace x (named_paper_ex \<sigma> A) =
    named_paper_ex \<sigma> (paper_R_naming_replace x A)"
  by (simp_all only: named_paper_not_def named_paper_and_def named_paper_or_def
    named_paper_eq_def named_paper_all_def named_paper_ex_def paper_R_naming_replace.simps)

lemma paper_R_parameter_replace_defined_heads:
  "paper_R_naming_replace x (named_paper_imp_const G) = named_paper_imp_const G"
  "paper_R_naming_replace x (named_paper_iff_const G) = named_paper_iff_const G"
  by (simp_all only: named_paper_imp_const_def named_paper_iff_const_def
    paper_R_parameter_replace_primitive paper_R_naming_replace.simps)

lemma paper_R_parameter_replace_imp:
  "paper_R_naming_replace x (named_paper_imp G A B) =
    named_paper_imp G (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
  by (simp only: named_paper_imp_def paper_R_naming_replace.simps paper_R_parameter_replace_defined_heads)

lemma paper_R_parameter_replace_iff:
  "paper_R_naming_replace x (named_paper_iff G A B) =
    named_paper_iff G (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
  by (simp only: named_paper_iff_def paper_R_naming_replace.simps paper_R_parameter_replace_defined_heads)

lemma paper_R_parameter_replace_prop_instance:
  "paper_R_naming_replace x (named_paper_prop_instance G v P) =
    named_paper_prop_instance G (\<lambda>a. paper_R_naming_replace x (v a)) P"
  by (induction P) (simp_all only: named_paper_prop_instance.simps
    paper_R_parameter_replace_primitive paper_R_parameter_replace_imp paper_R_parameter_replace_iff)

text \<open>
  These are literal structural equations. The λ-defined → and ↔
  heads retain their original bound names; no β simplification or
  identification with primitive operators is made. Source: Figure 1,
  p.6, as used in the parameter extension for n.73.
\<close>

end
