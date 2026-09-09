theory Bacon_Source_Relational_Parameter_Conversion_Axioms
  imports Bacon_Source_Relational_Parameter_Logical_Axioms
    Bacon_Source_Relational_Naming_Conversion_Steps
begin

section \<open>Literal contextual β and η axioms in the parameter theory\<close>

lemma paper_R_parameter_theory_conversion_axiom:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and al: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    and bl: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G B Prop"
    and step: "named_compatible_step named_beta_contract A B \<or>
      named_compatible_step named_eta_contract A B"
    and il: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (named_paper_iff G A B) Prop"
  shows "named_paper_iff G A B \<in> paper_R_parameter_theory \<Sigma> G D T"
proof -
  let ?I = "named_paper_iff G A B"
  let ?F = "{A,B,?I}"
  have languages: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G C Prop"
    if "C \<in> ?F" for C using that al bl il by blast
  obtain x where chart: "paper_R_naming_chart G (paper_R_naming_family_support ?F)
      (paper_R_naming_family_vars ?F) x"
    by (rule paper_R_parameter_family_chart[where F="?F", OF rich _ languages]) simp
  have ac: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
    and bc: "paper_R_naming_chart G (paper_R_naming_support B) (named_vars B) x"
    and ic: "paper_R_naming_chart G (paper_R_naming_support ?I) (named_vars ?I) x"
    by (rule paper_R_parameter_family_chart_at[OF chart]; simp)+
  have old_al: "paper_R_in_language \<Sigma> G (paper_R_naming_replace x A) Prop"
    by (rule paper_R_naming_replace_language[OF al ac subset_refl])
  have old_bl: "paper_R_in_language \<Sigma> G (paper_R_naming_replace x B) Prop"
    by (rule paper_R_naming_replace_language[OF bl bc subset_refl])
  have old_il: "paper_R_in_language \<Sigma> G
      (named_paper_iff G (paper_R_naming_replace x A) (paper_R_naming_replace x B)) Prop"
    using paper_R_naming_replace_language[OF il ic subset_refl]
    by (simp only: paper_R_parameter_replace_iff)
  have old_H: "paper_R_named_H \<Sigma> G
      (named_paper_iff G (paper_R_naming_replace x A) (paper_R_naming_replace x B))"
  proof (rule disjE[OF step])
    assume beta: "named_compatible_step named_beta_contract A B"
    have transformed: "named_compatible_step named_beta_contract
        (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
      by (rule paper_R_naming_chart_beta_step[OF beta ac subset_refl subset_refl])
    show ?thesis by (rule paper_R_named_H.Beta[OF old_al old_bl transformed old_il])
  next
    assume eta: "named_compatible_step named_eta_contract A B"
    have transformed: "named_compatible_step named_eta_contract
        (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
      by (rule paper_R_naming_chart_eta_step[OF eta ac subset_refl subset_refl])
    show ?thesis by (rule paper_R_named_H.Eta[OF old_al old_bl transformed old_il])
  qed
  have old_member: "named_paper_iff G (paper_R_naming_replace x A) (paper_R_naming_replace x B) \<in> T"
    by (rule paper_R_H_theory_H[OF theory_h old_H])
  have replaced: "paper_R_naming_replace x ?I \<in> T"
    by (simp only: paper_R_parameter_replace_iff; rule old_member)
  show ?thesis by (rule paper_R_parameter_theoryI[OF il ic replaced])
qed

lemma paper_R_parameter_theory_Beta:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and al: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    and bl: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G B Prop"
    and step: "named_compatible_step named_beta_contract A B"
    and il: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (named_paper_iff G A B) Prop"
  shows "named_paper_iff G A B \<in> paper_R_parameter_theory \<Sigma> G D T"
  by (rule paper_R_parameter_theory_conversion_axiom[OF rich theory_h al bl disjI1[OF step] il])

lemma paper_R_parameter_theory_Eta:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and al: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    and bl: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G B Prop"
    and step: "named_compatible_step named_eta_contract A B"
    and il: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (named_paper_iff G A B) Prop"
  shows "named_paper_iff G A B \<in> paper_R_parameter_theory \<Sigma> G D T"
  by (rule paper_R_parameter_theory_conversion_axiom[OF rich theory_h al bl disjI2[OF step] il])

text \<open>
  A single common chart avoids all variable names of both endpoints
  and their literal biconditional. The actual contextual contraction
  therefore survives replacement, including capture and η freshness
  guards inside the context. These are the immediate Figure 2 axioms,
  not whole chains or a new α rule. No semantic model is used.
\<close>

end
