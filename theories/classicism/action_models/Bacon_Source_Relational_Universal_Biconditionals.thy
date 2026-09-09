theory Bacon_Source_Relational_Universal_Biconditionals
  imports Bacon_Source_Relational_Universal_Proof_Basics Bacon_Source_Relational_Distribution_PC
begin

section \<open>Native H biconditional composition\<close>

lemma paper_R_named_H_iff_sym:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and premise: "paper_R_named_H \<Sigma> G (named_paper_iff G A B)"
  shows "paper_R_named_H \<Sigma> G (named_paper_iff G B A)"
proof -
  have tautology: "sprop_tautology (SPImp (SPIff (SPAtom (0::nat)) (SPAtom 1)) (SPIff (SPAtom 1) (SPAtom 0)))"
    by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_iff G A B) (named_paper_iff G B A))"
    using paper_R_named_H_binary_PC[OF rich al bl tautology] by simp
  show ?thesis by (rule paper_R_named_H.MP[OF premise schema paper_R_named_paper_iff_language[OF rich bl al]])
qed

lemma paper_R_named_H_iff_trans:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and cl: "paper_R_in_language \<Sigma> G C Prop"
    and first: "paper_R_named_H \<Sigma> G (named_paper_iff G A B)"
    and second: "paper_R_named_H \<Sigma> G (named_paper_iff G B C)"
  shows "paper_R_named_H \<Sigma> G (named_paper_iff G A C)"
proof -
  have tautology: "sprop_tautology (SPImp (SPIff (SPAtom (0::nat)) (SPAtom 1))
    (SPImp (SPIff (SPAtom 1) (SPAtom 2)) (SPIff (SPAtom 0) (SPAtom 2))))"
    by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_iff G A B)
    (named_paper_imp G (named_paper_iff G B C) (named_paper_iff G A C)))"
    using paper_R_named_H_ternary_PC[OF rich al bl cl tautology] by simp
  show ?thesis by (rule paper_R_named_H_MP2[OF rich first second schema paper_R_named_paper_iff_language[OF rich al cl]])
qed

section \<open>Universal logical consequence, not identity abstraction\<close>

text \<open>
  H's UI and Gen lift A→B to ∀u.A→∀u.B. The antecedent
  ∀u.A is u-fresh because u is already bound; A and B themselves
  may be open. Biconditional congruence follows in both directions.
  This is ordinary logical consequence in H, not λ-congruence of
  object-language identity. Source: Figure 2 and Appendix A.2, p.66.
\<close>

lemma paper_R_named_H_all_binder_mono:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>"
    and premise: "paper_R_named_H \<Sigma> G (named_paper_imp G A B)"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_imp G (named_paper_all \<sigma> (NLam u A)) (named_paper_all \<sigma> (NLam u B)))"
proof -
  have aa: "paper_R_in_language \<Sigma> G (named_paper_all \<sigma> (NLam u A)) Prop"
    by (rule paper_R_named_all_binder_language[OF al variable rt])
  have ba: "paper_R_in_language \<Sigma> G (named_paper_all \<sigma> (NLam u B)) Prop"
    by (rule paper_R_named_all_binder_language[OF bl variable rt])
  have body: "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_all \<sigma> (NLam u A)) B)"
    by (rule paper_R_named_H_imp_trans[OF rich aa al bl
      paper_R_named_H_all_binder_instance[OF rich al variable rt] premise])
  have fresh: "u \<notin> named_fv (named_paper_all \<sigma> (NLam u A))" by (simp add: named_paper_primitive_fv)
  show ?thesis by (rule paper_R_named_H.Gen[OF body variable fresh paper_R_named_paper_imp_language[OF rich aa ba]])
qed

lemma paper_R_named_H_all_binder_iff:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>"
    and premise: "paper_R_named_H \<Sigma> G (named_paper_iff G A B)"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_iff G (named_paper_all \<sigma> (NLam u A)) (named_paper_all \<sigma> (NLam u B)))"
proof -
  have ab: "paper_R_named_H \<Sigma> G (named_paper_imp G A B)"
    by (rule paper_R_named_H.MP[OF premise paper_R_named_H_iff_forward[OF rich al bl] paper_R_named_paper_imp_language[OF rich al bl]])
  have ba: "paper_R_named_H \<Sigma> G (named_paper_imp G B A)"
    by (rule paper_R_named_H.MP[OF premise paper_R_named_H_iff_backward[OF rich al bl] paper_R_named_paper_imp_language[OF rich bl al]])
  show ?thesis by (rule paper_R_named_H_iff_intro[OF rich
    paper_R_named_all_binder_language[OF al variable rt] paper_R_named_all_binder_language[OF bl variable rt]
    paper_R_named_H_all_binder_mono[OF rich al bl variable rt ab]
    paper_R_named_H_all_binder_mono[OF rich bl al variable rt ba]])
qed

end
