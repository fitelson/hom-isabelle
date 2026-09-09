theory Bacon_Source_Relational_Witness_Eta
  imports Bacon_Source_Relational_Witness_Syntax Bacon_Source_Relational_Local_Inst
    Bacon_Source_Relational_Existence
begin

section \<open>η expands the existential predicate without changing the formula\<close>

lemma paper_R_named_H_exists_eta_expand:
  assumes rich: "paper_R_rich G" and predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
    and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "paper_R_named_H \<Omega> G
    (named_paper_imp G (named_paper_ex \<sigma> F) (named_paper_ex \<sigma> (NLam n (NApp F (NVar n)))))"
proof -
  let ?E = "named_paper_ex \<sigma> F"
  let ?L = "named_paper_ex \<sigma> (NLam n (NApp F (NVar n)))"
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have variable: "paper_R_in_language \<Omega> G (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Omega> and G=G and n=n, OF nt rt])
  have body: "paper_R_in_language \<Omega> G (NApp F (NVar n)) Prop" by (rule paper_R_language_App[OF predicate variable])
  have ll: "paper_R_in_language \<Omega> G ?L Prop" by (rule paper_R_local_exists_binder_language[OF body nt rt])
  have el: "paper_R_in_language \<Omega> G ?E Prop" by (rule paper_R_predicate_exists_language[OF predicate])
  have step: "named_compatible_step named_eta_contract ?L ?E"
    unfolding named_paper_ex_def
    by (rule named_compatible_step.App_right, rule named_compatible_step.root, rule named_eta_contract.eta[OF fresh])
  have il: "paper_R_in_language \<Omega> G (named_paper_iff G ?L ?E) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich ll el])
  have conversion: "paper_R_named_H \<Omega> G (named_paper_iff G ?L ?E)"
    by (rule paper_R_named_H.Eta[OF ll el step il])
  show ?thesis by (rule paper_R_named_H.MP[OF conversion paper_R_named_H_iff_backward[OF rich ll el]
    paper_R_named_paper_imp_language[OF rich el ll]])
qed

end
