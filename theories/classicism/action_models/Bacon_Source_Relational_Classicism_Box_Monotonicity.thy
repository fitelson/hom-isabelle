theory Bacon_Source_Relational_Classicism_Box_Monotonicity
  imports Bacon_Source_Relational_Classicism_H_Theory
    Bacon_Source_Relational_H_Theory_Normal_K
begin

section \<open>Box monotonicity for actual C theorems\<close>

theorem paper_R_classicism_box_monotone:
  assumes rich: "paper_R_rich G"
    and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
    and premise: "paper_R_classicism_proves \<Sigma> G (named_paper_imp G A B)"
  shows "paper_R_classicism_proves \<Sigma> G
    (named_paper_imp G (paper_R_named_box G A) (paper_R_named_box G B))"
proof -
  have necessitated: "paper_R_classicism_proves \<Sigma> G (paper_R_named_box G (named_paper_imp G A B))"
    by (rule paper_R_classicism_necessitation[OF rich premise])
  have K_member: "named_paper_imp G (paper_R_named_box G (named_paper_imp G A B))
      (named_paper_imp G (paper_R_named_box G A) (paper_R_named_box G B))
      \<in> {P. paper_R_classicism_proves \<Sigma> G P}"
    by (rule paper_R_H_theory_normal_K[OF rich paper_R_classicism_is_H_theory
      paper_R_classicism_is_PE_closed[OF rich] al bl])
  have K_theorem: "paper_R_classicism_proves \<Sigma> G
      (named_paper_imp G (paper_R_named_box G (named_paper_imp G A B))
        (named_paper_imp G (paper_R_named_box G A) (paper_R_named_box G B)))"
    using K_member by simp
  have language: "paper_R_in_language \<Sigma> G
      (named_paper_imp G (paper_R_named_box G A) (paper_R_named_box G B)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich
      paper_R_named_box_language[OF rich al] paper_R_named_box_language[OF rich bl]])
  show ?thesis by (rule paper_R_classicism_proves.MP[OF necessitated K_theorem language])
qed

text \<open>
  Necessitation is applied to a theorem of the ORIGINAL C theory,
  then its proved K schema is used by MP. There is no temporary
  assumption in this lemma. Source: §1.5, pp.16–18, and n.22.
\<close>

end
