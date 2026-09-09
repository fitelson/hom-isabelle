theory Bacon_Source_Relational_Parameter_Quantified_Closure
  imports Bacon_Source_Relational_Parameter_Propositional_Closure
    Bacon_Source_Relational_Language_Inversion
begin

section \<open>Gen and Inst retain their exact eigenvariable guards\<close>

theorem paper_R_parameter_theory_Gen:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and premise: "named_paper_imp G P Q \<in> paper_R_parameter_theory \<Sigma> G D T"
    and variable: "G n = \<sigma>" and fresh: "n \<notin> named_fv P"
    and conclusion: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G
      (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))) Prop"
  shows "named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)) \<in>
    paper_R_parameter_theory \<Sigma> G D T"
proof -
  let ?I = "named_paper_imp G P Q"
  let ?C = "named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))"
  let ?F = "{?I,?C,P}"
  have il: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G ?I Prop"
    by (rule paper_R_parameter_theory_language[OF premise])
  have pl: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G P Prop"
    by (rule conjunct1[OF paper_R_imp_language_operands[OF rich il]])
  have languages: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    if "A \<in> ?F" for A using that il conclusion pl by blast
  obtain x where chart: "paper_R_naming_chart G (paper_R_naming_family_support ?F)
      (paper_R_naming_family_vars ?F) x"
    by (rule paper_R_parameter_family_chart[where F="?F", OF rich _ languages]) simp
  have ic: "paper_R_naming_chart G (paper_R_naming_support ?I) (named_vars ?I) x"
    and cc: "paper_R_naming_chart G (paper_R_naming_support ?C) (named_vars ?C) x"
    by (rule paper_R_parameter_family_chart_at[OF chart]; simp)+
  have nvars: "n \<in> named_vars ?C"
    by (simp add: named_paper_imp_def named_paper_all_def)
  have bound_name: "n \<in> paper_R_naming_family_vars ?F"
    using nvars by (auto simp: paper_R_naming_family_vars_def)
  have pm: "P \<in> ?F" by simp
  have old_fresh: "n \<notin> named_fv (paper_R_naming_replace x P)"
    by (rule paper_R_parameter_family_fresh[OF chart pm bound_name fresh])
  have old_i: "named_paper_imp G (paper_R_naming_replace x P) (paper_R_naming_replace x Q) \<in> T"
    using iffD1[OF paper_R_parameter_theory_at_chart_iff[OF rich theory_h il ic] premise]
    by (simp only: paper_R_parameter_replace_imp)
  have replaced_language: "paper_R_in_language \<Sigma> G (paper_R_naming_replace x ?C) Prop"
    by (rule paper_R_naming_replace_language[OF conclusion cc subset_refl])
  have old_conclusion: "paper_R_in_language \<Sigma> G
      (named_paper_imp G (paper_R_naming_replace x P)
        (named_paper_all \<sigma> (NLam n (paper_R_naming_replace x Q)))) Prop"
    using replaced_language by (simp only: paper_R_parameter_replace_imp
      paper_R_parameter_replace_primitive paper_R_naming_replace.simps)
  have result: "named_paper_imp G (paper_R_naming_replace x P)
      (named_paper_all \<sigma> (NLam n (paper_R_naming_replace x Q))) \<in> T"
    by (rule paper_R_H_theory_Gen[OF theory_h old_i variable old_fresh old_conclusion])
  have replaced: "paper_R_naming_replace x ?C \<in> T"
    by (simp only: paper_R_parameter_replace_imp paper_R_parameter_replace_primitive
      paper_R_naming_replace.simps; rule result)
  show ?thesis by (rule paper_R_parameter_theoryI[OF conclusion cc replaced])
qed

theorem paper_R_parameter_theory_Inst:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and premise: "named_paper_imp G P Q \<in> paper_R_parameter_theory \<Sigma> G D T"
    and variable: "G n = \<sigma>" and fresh: "n \<notin> named_fv Q"
    and conclusion: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G
      (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop"
  shows "named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q \<in>
    paper_R_parameter_theory \<Sigma> G D T"
proof -
  let ?I = "named_paper_imp G P Q"
  let ?C = "named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q"
  let ?F = "{?I,?C,Q}"
  have il: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G ?I Prop"
    by (rule paper_R_parameter_theory_language[OF premise])
  have ql: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G Q Prop"
    by (rule conjunct2[OF paper_R_imp_language_operands[OF rich il]])
  have languages: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    if "A \<in> ?F" for A using that il conclusion ql by blast
  obtain x where chart: "paper_R_naming_chart G (paper_R_naming_family_support ?F)
      (paper_R_naming_family_vars ?F) x"
    by (rule paper_R_parameter_family_chart[where F="?F", OF rich _ languages]) simp
  have ic: "paper_R_naming_chart G (paper_R_naming_support ?I) (named_vars ?I) x"
    and cc: "paper_R_naming_chart G (paper_R_naming_support ?C) (named_vars ?C) x"
    by (rule paper_R_parameter_family_chart_at[OF chart]; simp)+
  have nvars: "n \<in> named_vars ?C"
    by (simp add: named_paper_imp_def named_paper_ex_def)
  have bound_name: "n \<in> paper_R_naming_family_vars ?F"
    using nvars by (auto simp: paper_R_naming_family_vars_def)
  have qm: "Q \<in> ?F" by simp
  have old_fresh: "n \<notin> named_fv (paper_R_naming_replace x Q)"
    by (rule paper_R_parameter_family_fresh[OF chart qm bound_name fresh])
  have old_i: "named_paper_imp G (paper_R_naming_replace x P) (paper_R_naming_replace x Q) \<in> T"
    using iffD1[OF paper_R_parameter_theory_at_chart_iff[OF rich theory_h il ic] premise]
    by (simp only: paper_R_parameter_replace_imp)
  have replaced_language: "paper_R_in_language \<Sigma> G (paper_R_naming_replace x ?C) Prop"
    by (rule paper_R_naming_replace_language[OF conclusion cc subset_refl])
  have old_conclusion: "paper_R_in_language \<Sigma> G
      (named_paper_imp G (named_paper_ex \<sigma> (NLam n (paper_R_naming_replace x P)))
        (paper_R_naming_replace x Q)) Prop"
    using replaced_language by (simp only: paper_R_parameter_replace_imp
      paper_R_parameter_replace_primitive paper_R_naming_replace.simps)
  have result: "named_paper_imp G (named_paper_ex \<sigma> (NLam n (paper_R_naming_replace x P)))
      (paper_R_naming_replace x Q) \<in> T"
    by (rule paper_R_H_theory_Inst[OF theory_h old_i variable old_fresh old_conclusion])
  have replaced: "paper_R_naming_replace x ?C \<in> T"
    by (simp only: paper_R_parameter_replace_imp paper_R_parameter_replace_primitive
      paper_R_naming_replace.simps; rule result)
  show ?thesis by (rule paper_R_parameter_theoryI[OF conclusion cc replaced])
qed

text \<open>
  The common finite chart avoids the quantified conclusion's binder,
  as well as all other variables in the chosen rule instance. Thus
  markers do not invalidate the ORIGINAL Gen/Inst eigenvariable
  condition. These are closure lemmas only: H inclusion in T↑ has
  not been used or asserted. Source: Figure 2, p.8, and n.73.
\<close>

end
