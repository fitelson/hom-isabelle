theory Bacon_Source_Relational_Parameter_Propositional_Closure
  imports Bacon_Source_Relational_Parameter_Finite_Charts
    Bacon_Source_Relational_Theoretical_Naming_Logical_Syntax
begin

section \<open>MP and conditional PE closure of the parameter theory\<close>

theorem paper_R_parameter_theory_MP:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and antecedent: "P \<in> paper_R_parameter_theory \<Sigma> G D T"
    and implication: "named_paper_imp G P Q \<in> paper_R_parameter_theory \<Sigma> G D T"
    and ql: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G Q Prop"
  shows "Q \<in> paper_R_parameter_theory \<Sigma> G D T"
proof -
  let ?F = "{P,Q,named_paper_imp G P Q}"
  have pl: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G P Prop"
    by (rule paper_R_parameter_theory_language[OF antecedent])
  have il: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (named_paper_imp G P Q) Prop"
    by (rule paper_R_parameter_theory_language[OF implication])
  have languages: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    if "A \<in> ?F" for A using that pl ql il by blast
  obtain x where chart: "paper_R_naming_chart G (paper_R_naming_family_support ?F)
      (paper_R_naming_family_vars ?F) x"
    by (rule paper_R_parameter_family_chart[where F="?F", OF rich _ languages]) simp
  have at: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
    if "A \<in> ?F" for A by (rule paper_R_parameter_family_chart_at[OF chart that])
  have pc: "paper_R_naming_chart G (paper_R_naming_support P) (named_vars P) x"
    and qc: "paper_R_naming_chart G (paper_R_naming_support Q) (named_vars Q) x"
    and ic: "paper_R_naming_chart G (paper_R_naming_support (named_paper_imp G P Q))
      (named_vars (named_paper_imp G P Q)) x"
    by (rule at; simp)+
  have old_p: "paper_R_naming_replace x P \<in> T"
    by (rule iffD1[OF paper_R_parameter_theory_at_chart_iff[OF rich theory_h pl pc] antecedent])
  have old_i: "named_paper_imp G (paper_R_naming_replace x P) (paper_R_naming_replace x Q) \<in> T"
    using iffD1[OF paper_R_parameter_theory_at_chart_iff[OF rich theory_h il ic] implication]
    by (simp only: paper_R_parameter_replace_imp)
  have old_ql: "paper_R_in_language \<Sigma> G (paper_R_naming_replace x Q) Prop"
    by (rule paper_R_naming_replace_language[OF ql qc subset_refl])
  have old_q: "paper_R_naming_replace x Q \<in> T"
    by (rule paper_R_H_theory_MP[OF theory_h old_p old_i old_ql])
  show ?thesis by (rule paper_R_parameter_theoryI[OF ql qc old_q])
qed

theorem paper_R_parameter_theory_PE:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T"
    and pl: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G P Prop"
    and ql: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G Q Prop"
    and equivalence: "named_paper_iff G P Q \<in> paper_R_parameter_theory \<Sigma> G D T"
  shows "named_paper_eq Prop P Q \<in> paper_R_parameter_theory \<Sigma> G D T"
proof -
  let ?I = "named_paper_iff G P Q"
  let ?E = "named_paper_eq Prop P Q"
  let ?F = "{P,Q,?I,?E}"
  have il: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G ?I Prop"
    by (rule paper_R_parameter_theory_language[OF equivalence])
  have el: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G ?E Prop"
    by (rule paper_R_named_identity_language[OF pl ql])
  have languages: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    if "A \<in> ?F" for A using that pl ql il el by blast
  obtain x where chart: "paper_R_naming_chart G (paper_R_naming_family_support ?F)
      (paper_R_naming_family_vars ?F) x"
    by (rule paper_R_parameter_family_chart[where F="?F", OF rich _ languages]) simp
  have at: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
    if "A \<in> ?F" for A by (rule paper_R_parameter_family_chart_at[OF chart that])
  have pc: "paper_R_naming_chart G (paper_R_naming_support P) (named_vars P) x"
    and qc: "paper_R_naming_chart G (paper_R_naming_support Q) (named_vars Q) x"
    and ic: "paper_R_naming_chart G (paper_R_naming_support ?I) (named_vars ?I) x"
    and ec: "paper_R_naming_chart G (paper_R_naming_support ?E) (named_vars ?E) x"
    by (rule at; simp)+
  have old_pl: "paper_R_in_language \<Sigma> G (paper_R_naming_replace x P) Prop"
    by (rule paper_R_naming_replace_language[OF pl pc subset_refl])
  have old_ql: "paper_R_in_language \<Sigma> G (paper_R_naming_replace x Q) Prop"
    by (rule paper_R_naming_replace_language[OF ql qc subset_refl])
  have old_i: "named_paper_iff G (paper_R_naming_replace x P) (paper_R_naming_replace x Q) \<in> T"
    using iffD1[OF paper_R_parameter_theory_at_chart_iff[OF rich theory_h il ic] equivalence]
    by (simp only: paper_R_parameter_replace_iff)
  have old_e: "named_paper_eq Prop (paper_R_naming_replace x P) (paper_R_naming_replace x Q) \<in> T"
    by (rule paper_R_PE_closedD[OF pe old_pl old_ql old_i])
  have replaced: "paper_R_naming_replace x ?E \<in> T"
    by (simp only: paper_R_parameter_replace_primitive; rule old_e)
  show ?thesis by (rule paper_R_parameter_theoryI[OF el ec replaced])
qed

corollary paper_R_parameter_theory_PE_closed:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pe: "paper_R_PE_closed \<Sigma> G T"
  shows "paper_R_PE_closed (paper_R_naming_signature \<Sigma> D) G (paper_R_parameter_theory \<Sigma> G D T)"
  unfolding paper_R_PE_closed_def
  by (intro allI impI; rule paper_R_parameter_theory_PE[OF rich theory_h pe]; assumption)

text \<open>
  Each inference uses one common finite chart. PE is preserved only
  when it is a closure property of the original T; no semantic
  identity-from-truth principle is invoked. H inclusion and the
  quantified rules are not assumed in either argument.
\<close>

end
