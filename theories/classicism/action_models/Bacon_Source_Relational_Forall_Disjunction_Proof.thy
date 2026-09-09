theory Bacon_Source_Relational_Forall_Disjunction_Proof
  imports Bacon_Source_Relational_Universal_Proof_Basics Bacon_Source_Relational_Distribution_PC
begin

section \<open>Native H proves the source universal-disjunction distribution biconditional\<close>

text \<open>
  ⊢Hᴿ (∀u:σ.(F u∨P)) ↔ ((∀σF)∨P),
  where u is free in neither F nor P. Source role: the material
  quantifier law underlying Distribution-∨∀ in Appendix A.2, p.66.

  UI followed by literal β gives C→(Fu∨P), with C=∀u.(Fu∨P).
  PC gives (C∧¬P)→Fu; Gen and η then give (C∧¬P)→∀F,
  hence C→(∀F∨P). Conversely UI and propositional introductions
  give ∀F→(Fu∨P) and P→(Fu∨P). Gen applies separately
  to their u-fresh antecedents, and PC combines the two implications.
  Every step is native H; no C Equivalence, semantic truth law,
  Functionality or completeness theorem is used.
\<close>

theorem paper_R_named_H_forall_or_distribution:
  assumes rich: "paper_R_rich G" and predicate: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
    and parameter: "paper_R_in_language \<Sigma> G P Prop"
    and variable: "G u = \<sigma>" and fresh_F: "u \<notin> named_fv F" and fresh_P: "u \<notin> named_fv P"
  shows "paper_R_named_H \<Sigma> G (named_paper_iff G
    (named_paper_all \<sigma> (NLam u (named_paper_or (NApp F (NVar u)) P)))
    (named_paper_or (named_paper_all \<sigma> F) P))"
proof -
  let ?B = "NApp F (NVar u)"
  let ?Body = "named_paper_or ?B P"
  let ?A = "named_paper_all \<sigma> F"
  let ?C = "named_paper_all \<sigma> (NLam u ?Body)"
  let ?L = "named_paper_all \<sigma> (NLam u ?B)"
  let ?D = "named_paper_and ?C (named_paper_not P)"
  let ?R = "named_paper_or ?A P"
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have argument: "paper_R_in_language \<Sigma> G (NVar u) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=u, OF variable rt])
  have bl: "paper_R_in_language \<Sigma> G ?B Prop" by (rule paper_R_language_App[OF predicate argument])
  have body: "paper_R_in_language \<Sigma> G ?Body Prop" by (rule paper_R_named_or_language[OF bl parameter])
  have al: "paper_R_in_language \<Sigma> G ?A Prop" by (rule paper_R_predicate_all_language[OF predicate])
  have cl: "paper_R_in_language \<Sigma> G ?C Prop" by (rule paper_R_named_all_binder_language[OF body variable rt])
  have ll: "paper_R_in_language \<Sigma> G ?L Prop" by (rule paper_R_named_all_binder_language[OF bl variable rt])
  have dl: "paper_R_in_language \<Sigma> G ?D Prop"
    by (rule paper_R_named_and_language[OF cl paper_R_named_not_language[OF parameter]])
  have rl: "paper_R_in_language \<Sigma> G ?R Prop" by (rule paper_R_named_or_language[OF al parameter])
  have c_instance: "paper_R_named_H \<Sigma> G (named_paper_imp G ?C ?Body)"
    by (rule paper_R_named_H_all_binder_instance[OF rich body variable rt])
  have guarded_body: "paper_R_named_H \<Sigma> G (named_paper_imp G ?D ?B)"
    by (rule paper_R_named_H_or_negative_antecedent[OF rich cl bl parameter c_instance])
  have fresh_D: "u \<notin> named_fv ?D"
    by (simp add: named_paper_primitive_fv fresh_P)
  have generalized_D: "paper_R_named_H \<Sigma> G (named_paper_imp G ?D ?L)"
    by (rule paper_R_named_H.Gen[OF guarded_body variable fresh_D paper_R_named_paper_imp_language[OF rich dl ll]])
  have eta: "paper_R_named_H \<Sigma> G (named_paper_imp G ?L ?A)"
    by (rule paper_R_named_H_all_eta_contract[OF rich predicate variable fresh_F])
  have guarded_all: "paper_R_named_H \<Sigma> G (named_paper_imp G ?D ?A)"
    by (rule paper_R_named_H_imp_trans[OF rich dl ll al generalized_D eta])
  have forward: "paper_R_named_H \<Sigma> G (named_paper_imp G ?C ?R)"
    by (rule paper_R_named_H_or_restore[OF rich cl al parameter guarded_all])
  have ui: "paper_R_named_H \<Sigma> G (named_paper_imp G ?A ?B)"
    by (rule paper_R_named_H.UI[OF paper_R_named_paper_imp_language[OF rich al bl]])
  have introduce_left: "paper_R_named_H \<Sigma> G (named_paper_imp G ?B ?Body)"
    by (rule paper_R_named_H_or_left[OF rich bl parameter])
  have all_to_body: "paper_R_named_H \<Sigma> G (named_paper_imp G ?A ?Body)"
    by (rule paper_R_named_H_imp_trans[OF rich al bl body ui introduce_left])
  have fresh_A: "u \<notin> named_fv ?A" by (simp only: named_paper_primitive_fv; rule fresh_F)
  have all_to_C: "paper_R_named_H \<Sigma> G (named_paper_imp G ?A ?C)"
    by (rule paper_R_named_H.Gen[OF all_to_body variable fresh_A paper_R_named_paper_imp_language[OF rich al cl]])
  have parameter_to_body: "paper_R_named_H \<Sigma> G (named_paper_imp G P ?Body)"
    by (rule paper_R_named_H_or_right[OF rich bl parameter])
  have parameter_to_C: "paper_R_named_H \<Sigma> G (named_paper_imp G P ?C)"
    by (rule paper_R_named_H.Gen[OF parameter_to_body variable fresh_P paper_R_named_paper_imp_language[OF rich parameter cl]])
  have backward: "paper_R_named_H \<Sigma> G (named_paper_imp G ?R ?C)"
    by (rule paper_R_named_H_or_cases[OF rich al parameter cl all_to_C parameter_to_C])
  show ?thesis by (rule paper_R_named_H_iff_intro[OF rich cl rl forward backward])
qed

end
