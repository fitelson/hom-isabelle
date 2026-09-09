theory Bacon_Source_Relational_Existential_Proof_Basics
  imports Bacon_Source_Relational_Universal_Proof_Basics Bacon_Source_Relational_Distribution_PC
begin

section \<open>Literal existential-binder introduction in native H\<close>

lemma paper_R_named_ex_binder_language:
  assumes body: "paper_R_in_language \<Sigma> G A Prop" and variable: "G u = \<sigma>"
    and rt: "paper_R_type \<sigma>"
  shows "paper_R_in_language \<Sigma> G (named_paper_ex \<sigma> (NLam u A)) Prop"
proof -
  have ur: "paper_R_type (G u)" by (simp only: variable; rule rt)
  have predicate: "paper_R_in_language \<Sigma> G (NLam u A) (Arr \<sigma> Prop)"
    using paper_R_named_identity_test_language[OF body ur] by (simp only: variable)
  show ?thesis by (rule paper_R_predicate_exists_language[OF predicate])
qed

theorem paper_R_named_H_ex_binder_instance:
  assumes rich: "paper_R_rich G" and body: "paper_R_in_language \<Sigma> G A Prop"
    and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_R_named_H \<Sigma> G (named_paper_imp G A (named_paper_ex \<sigma> (NLam u A)))"
proof -
  have ur: "paper_R_type (G u)" by (simp only: variable; rule rt)
  have predicate: "paper_R_in_language \<Sigma> G (NLam u A) (Arr \<sigma> Prop)"
    using paper_R_named_identity_test_language[OF body ur] by (simp only: variable)
  have argument: "paper_R_in_language \<Sigma> G (NVar u) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=u, OF variable rt])
  have application: "paper_R_in_language \<Sigma> G (NApp (NLam u A) (NVar u)) Prop"
    by (rule paper_R_language_App[OF predicate argument])
  have exists_language: "paper_R_in_language \<Sigma> G (named_paper_ex \<sigma> (NLam u A)) Prop"
    by (rule paper_R_predicate_exists_language[OF predicate])
  have eg: "paper_R_named_H \<Sigma> G (named_paper_imp G
      (NApp (NLam u A) (NVar u)) (named_paper_ex \<sigma> (NLam u A)))"
    by (rule paper_R_named_H.EG[OF paper_R_named_paper_imp_language[OF rich application exists_language]])
  have root_step: "named_beta_contract (NApp (NLam u A) (NVar u)) A"
    using named_beta_contract.beta[OF named_free_for_same_variable, where x=u and A=A]
    by (simp only: named_subst_same_variable)
  have step: "named_compatible_step named_beta_contract (NApp (NLam u A) (NVar u)) A"
    by (rule named_compatible_step.root[where R=named_beta_contract
      and M="NApp (NLam u A) (NVar u)" and N=A, OF root_step])
  have beta_iff: "paper_R_named_H \<Sigma> G (named_paper_iff G (NApp (NLam u A) (NVar u)) A)"
    by (rule paper_R_named_H.Beta[OF application body step paper_R_named_paper_iff_language[OF rich application body]])
  have backward: "paper_R_named_H \<Sigma> G (named_paper_imp G A (NApp (NLam u A) (NVar u)))"
    by (rule paper_R_named_H.MP[OF beta_iff paper_R_named_H_iff_backward[OF rich application body]
      paper_R_named_paper_imp_language[OF rich body application]])
  show ?thesis by (rule paper_R_named_H_imp_trans[OF rich body application exists_language backward eg])
qed

lemma paper_R_named_H_negative_swap:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
    and premise: "paper_R_named_H \<Sigma> G (named_paper_imp G A (named_paper_not B))"
  shows "paper_R_named_H \<Sigma> G (named_paper_imp G B (named_paper_not A))"
proof -
  have tautology: "sprop_tautology (SPImp (SPImp (SPAtom (0::nat)) (SPNot (SPAtom 1)))
      (SPImp (SPAtom 1) (SPNot (SPAtom 0))))" by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Sigma> G (named_paper_imp G
      (named_paper_imp G A (named_paper_not B)) (named_paper_imp G B (named_paper_not A)))"
    using paper_R_named_H_binary_PC[OF rich al bl tautology] by simp
  show ?thesis by (rule paper_R_named_H.MP[OF premise schema
    paper_R_named_paper_imp_language[OF rich bl paper_R_named_not_language[OF al]]])
qed

text \<open>
  These are native EG/β and PC deductions. Source: Figure 2, p.8,
  used for the Inst case of Appendix A.2. No semantic duality or
  general quantifier congruence is assumed.
\<close>

end
