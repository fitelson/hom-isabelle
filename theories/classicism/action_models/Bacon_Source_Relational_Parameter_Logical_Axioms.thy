theory Bacon_Source_Relational_Parameter_Logical_Axioms
  imports Bacon_Source_Relational_Parameter_Quantified_Closure
begin

section \<open>The non-conversion axioms belong to the parameter theory\<close>

lemma paper_R_parameter_theory_logical_axiomI:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    and transform: "\<And>x. paper_R_in_language \<Sigma> G (paper_R_naming_replace x A) Prop
      \<Longrightarrow> paper_R_named_H \<Sigma> G (paper_R_naming_replace x A)"
  shows "A \<in> paper_R_parameter_theory \<Sigma> G D T"
proof -
  have typed: "paper_R_has_type G A Prop"
    using language unfolding paper_R_in_language_def by blast
  have types: "\<forall>k\<in>paper_R_naming_support A. paper_R_type (fst k)"
    by (rule paper_R_naming_support_R_types[OF typed])
  obtain x where chart: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
    using paper_R_naming_chart_exists[OF rich paper_R_naming_support_finite types named_vars_finite] by blast
  have old_language: "paper_R_in_language \<Sigma> G (paper_R_naming_replace x A) Prop"
    by (rule paper_R_naming_replace_language[OF language chart subset_refl])
  have member: "paper_R_naming_replace x A \<in> T"
    by (rule paper_R_H_theory_H[OF theory_h transform[OF old_language]])
  show ?thesis by (rule paper_R_parameter_theoryI[OF language chart member])
qed

lemma paper_R_parameter_replace_PC:
  assumes pc: "paper_R_named_PC (paper_R_naming_signature \<Sigma> D) G A"
    and language: "paper_R_in_language \<Sigma> G (paper_R_naming_replace x A) Prop"
  shows "paper_R_named_PC \<Sigma> G (paper_R_naming_replace x A)"
proof -
  obtain P :: "nat sprop_template" and v where tautology: "sprop_tautology P"
    and shape: "A = named_paper_prop_instance G v P"
    using pc unfolding paper_R_named_PC_def by blast
  have instance_eq: "paper_R_naming_replace x A =
      named_paper_prop_instance G (\<lambda>a. paper_R_naming_replace x (v a)) P"
    by (simp only: shape paper_R_parameter_replace_prop_instance)
  show ?thesis unfolding paper_R_named_PC_def
    by (rule conjI[OF language], rule exI[where x=P],
      rule exI[where x="\<lambda>a. paper_R_naming_replace x (v a)"],
      rule conjI[OF tautology instance_eq])
qed

lemma paper_R_parameter_theory_PC:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and pc: "paper_R_named_PC (paper_R_naming_signature \<Sigma> D) G A"
  shows "A \<in> paper_R_parameter_theory \<Sigma> G D T"
  by (rule paper_R_parameter_theory_logical_axiomI[
    OF rich theory_h paper_R_named_PC_language[OF pc]];
    rule paper_R_named_H.PC, rule paper_R_parameter_replace_PC[OF pc]; assumption)

lemma paper_R_parameter_theory_UI:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G
      (named_paper_imp G (named_paper_all \<sigma> F) (NApp F A)) Prop"
  shows "named_paper_imp G (named_paper_all \<sigma> F) (NApp F A) \<in> paper_R_parameter_theory \<Sigma> G D T"
proof (rule paper_R_parameter_theory_logical_axiomI[OF rich theory_h language])
  fix x
  assume old: "paper_R_in_language \<Sigma> G
      (paper_R_naming_replace x (named_paper_imp G (named_paper_all \<sigma> F) (NApp F A))) Prop"
  show "paper_R_named_H \<Sigma> G
      (paper_R_naming_replace x (named_paper_imp G (named_paper_all \<sigma> F) (NApp F A)))"
    by (simp only: paper_R_parameter_replace_imp paper_R_parameter_replace_primitive paper_R_naming_replace.simps;
      rule paper_R_named_H.UI; use old in \<open>simp only: paper_R_parameter_replace_imp
        paper_R_parameter_replace_primitive paper_R_naming_replace.simps\<close>)
qed

lemma paper_R_parameter_theory_EG:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G
      (named_paper_imp G (NApp F A) (named_paper_ex \<sigma> F)) Prop"
  shows "named_paper_imp G (NApp F A) (named_paper_ex \<sigma> F) \<in> paper_R_parameter_theory \<Sigma> G D T"
proof (rule paper_R_parameter_theory_logical_axiomI[OF rich theory_h language])
  fix x
  assume old: "paper_R_in_language \<Sigma> G
      (paper_R_naming_replace x (named_paper_imp G (NApp F A) (named_paper_ex \<sigma> F))) Prop"
  show "paper_R_named_H \<Sigma> G
      (paper_R_naming_replace x (named_paper_imp G (NApp F A) (named_paper_ex \<sigma> F)))"
    by (simp only: paper_R_parameter_replace_imp paper_R_parameter_replace_primitive paper_R_naming_replace.simps;
      rule paper_R_named_H.EG; use old in \<open>simp only: paper_R_parameter_replace_imp
        paper_R_parameter_replace_primitive paper_R_naming_replace.simps\<close>)
qed

lemma paper_R_parameter_theory_Ref:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G (named_paper_eq \<sigma> A A) Prop"
  shows "named_paper_eq \<sigma> A A \<in> paper_R_parameter_theory \<Sigma> G D T"
proof (rule paper_R_parameter_theory_logical_axiomI[OF rich theory_h language])
  fix x
  assume old: "paper_R_in_language \<Sigma> G (paper_R_naming_replace x (named_paper_eq \<sigma> A A)) Prop"
  show "paper_R_named_H \<Sigma> G (paper_R_naming_replace x (named_paper_eq \<sigma> A A))"
    by (simp only: paper_R_parameter_replace_primitive; rule paper_R_named_H.Ref;
      use old in \<open>simp only: paper_R_parameter_replace_primitive\<close>)
qed

lemma paper_R_parameter_theory_LL:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G
      (named_paper_imp G (named_paper_eq \<sigma> A B) (named_paper_imp G (NApp F A) (NApp F B))) Prop"
  shows "named_paper_imp G (named_paper_eq \<sigma> A B) (named_paper_imp G (NApp F A) (NApp F B)) \<in>
    paper_R_parameter_theory \<Sigma> G D T"
proof (rule paper_R_parameter_theory_logical_axiomI[OF rich theory_h language])
  fix x
  assume old: "paper_R_in_language \<Sigma> G (paper_R_naming_replace x
      (named_paper_imp G (named_paper_eq \<sigma> A B) (named_paper_imp G (NApp F A) (NApp F B)))) Prop"
  show "paper_R_named_H \<Sigma> G (paper_R_naming_replace x
      (named_paper_imp G (named_paper_eq \<sigma> A B) (named_paper_imp G (NApp F A) (NApp F B))))"
    by (simp only: paper_R_parameter_replace_imp paper_R_parameter_replace_primitive paper_R_naming_replace.simps;
      rule paper_R_named_H.LL; use old in \<open>simp only: paper_R_parameter_replace_imp
        paper_R_parameter_replace_primitive paper_R_naming_replace.simps\<close>)
qed

text \<open>
  Each replacement is an actual original-language native H axiom.
  PC retains its original Boolean template without restrictions on
  unused atom values. These proofs use H⊆T only in the original
  signature; H inclusion in the parameter theory is not a premise.
  Source: the first five schemas of Figure 2, p.8.
\<close>

end
