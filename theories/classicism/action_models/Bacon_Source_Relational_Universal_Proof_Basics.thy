theory Bacon_Source_Relational_Universal_Proof_Basics
  imports Bacon_Source_Relational_Classicism_A2_H
begin

section \<open>Literal universal-binder instantiation in native H\<close>

lemma paper_R_named_all_binder_language:
  assumes body: "paper_R_in_language \<Sigma> G A Prop" and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_R_in_language \<Sigma> G (named_paper_all \<sigma> (NLam u A)) Prop"
proof -
  have ur: "paper_R_type (G u)" by (simp only: variable; rule rt)
  have predicate: "paper_R_in_language \<Sigma> G (NLam u A) (Arr \<sigma> Prop)"
    using paper_R_named_identity_test_language[OF body ur] by (simp only: variable)
  show ?thesis by (rule paper_R_predicate_all_language[OF predicate])
qed

theorem paper_R_named_H_all_binder_instance:
  assumes rich: "paper_R_rich G" and body: "paper_R_in_language \<Sigma> G A Prop"
    and variable: "G u = \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_all \<sigma> (NLam u A)) A)"
proof -
  have ur: "paper_R_type (G u)" by (simp only: variable; rule rt)
  have predicate: "paper_R_in_language \<Sigma> G (NLam u A) (Arr \<sigma> Prop)"
    using paper_R_named_identity_test_language[OF body ur] by (simp only: variable)
  have argument: "paper_R_in_language \<Sigma> G (NVar u) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=u, OF variable rt])
  have app_language: "paper_R_in_language \<Sigma> G (NApp (NLam u A) (NVar u)) Prop"
    by (rule paper_R_language_App[OF predicate argument])
  have all_language: "paper_R_in_language \<Sigma> G (named_paper_all \<sigma> (NLam u A)) Prop"
    by (rule paper_R_predicate_all_language[OF predicate])
  have ui: "paper_R_named_H \<Sigma> G
    (named_paper_imp G (named_paper_all \<sigma> (NLam u A)) (NApp (NLam u A) (NVar u)))"
    by (rule paper_R_named_H.UI[OF paper_R_named_paper_imp_language[OF rich all_language app_language]])
  have root_step: "named_beta_contract (NApp (NLam u A) (NVar u)) A"
    using named_beta_contract.beta[OF named_free_for_same_variable, where x=u and A=A]
    by (simp only: named_subst_same_variable)
  have step: "named_compatible_step named_beta_contract (NApp (NLam u A) (NVar u)) A"
    by (rule named_compatible_step.root[where R=named_beta_contract and M="NApp (NLam u A) (NVar u)" and N=A, OF root_step])
  have il: "paper_R_in_language \<Sigma> G (named_paper_iff G (NApp (NLam u A) (NVar u)) A) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich app_language body])
  have beta_iff: "paper_R_named_H \<Sigma> G (named_paper_iff G (NApp (NLam u A) (NVar u)) A)"
    by (rule paper_R_named_H.Beta[OF app_language body step il])
  have beta_forward: "paper_R_named_H \<Sigma> G (named_paper_imp G (NApp (NLam u A) (NVar u)) A)"
    by (rule paper_R_named_H.MP[OF beta_iff paper_R_named_H_iff_forward[OF rich app_language body]
      paper_R_named_paper_imp_language[OF rich app_language body]])
  show ?thesis by (rule paper_R_named_H_imp_trans[OF rich all_language app_language body ui beta_forward])
qed

section \<open>Every universal instance of literal truth is an H theorem\<close>

text \<open>
  H proves ∀u.⊤ for every R type of u. Here ⊤ remains
  Figure 1's literal (∀p p)∨¬(∀p p). Start with ⊤→⊤,
  apply native Gen using FV(⊤)={}, then use H's theorem ⊤
  and MP. Source role: Appendix A.1 and the Gen/Inst calculation
  of A.2, pp.65–67. This proof uses only H constructors and PC;
  it neither assumes nor derives a general C abstraction rule.
\<close>

theorem paper_R_named_H_all_top:
  assumes rich: "paper_R_rich G" and rt: "paper_R_type \<sigma>" and variable: "G u = \<sigma>"
  shows "paper_R_named_H \<Sigma> G (named_paper_all \<sigma> (NLam u (paper_R_named_top G)))"
proof -
  have top: "paper_R_in_language \<Sigma> G (paper_R_named_top G) Prop" by (rule paper_R_named_top_language[OF rich])
  have all_top: "paper_R_in_language \<Sigma> G (named_paper_all \<sigma> (NLam u (paper_R_named_top G))) Prop"
    by (rule paper_R_named_all_binder_language[OF top variable rt])
  have premise: "paper_R_named_H \<Sigma> G (named_paper_imp G (paper_R_named_top G) (paper_R_named_top G))"
    by (rule paper_R_named_H_imp_refl[OF rich top])
  have fresh: "u \<notin> named_fv (paper_R_named_top G)" by (simp only: paper_R_named_top_closed; simp)
  have generalized: "paper_R_named_H \<Sigma> G
    (named_paper_imp G (paper_R_named_top G) (named_paper_all \<sigma> (NLam u (paper_R_named_top G))))"
    by (rule paper_R_named_H.Gen[OF premise variable fresh paper_R_named_paper_imp_language[OF rich top all_top]])
  show ?thesis by (rule paper_R_named_H.MP[OF paper_R_named_H_top[OF rich] generalized all_top])
qed

end
