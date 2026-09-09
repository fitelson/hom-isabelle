theory Bacon_Source_Relational_Quantifier_Duality
  imports Bacon_Source_Relational_Quantifier_PC Bacon_Source_Relational_Witness_Syntax
    Bacon_Source_Relational_Application_Identity_Tests
begin

section \<open>The universal operator and its literal η contraction\<close>

lemma paper_R_predicate_all_language:
  assumes predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
  shows "paper_R_in_language \<Omega> G (named_paper_all \<sigma> F) Prop"
proof -
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have qr: "paper_R_type (paper_logical_type (SAll \<sigma>))" using rt by simp
  have qt: "paper_R_has_type G (NLogical (SAll \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_R_has_type.Logical[where G=G and l="SAll \<sigma>", OF qr] by simp
  have ql: "paper_R_in_language \<Omega> G (NLogical (SAll \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
    unfolding paper_R_in_language_def by (rule conjI[OF qt]; simp)
  show ?thesis unfolding named_paper_all_def by (rule paper_R_language_App[OF ql predicate])
qed

lemma paper_R_named_H_all_eta_contract:
  assumes rich: "paper_R_rich G" and predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
    and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "paper_R_named_H \<Omega> G
    (named_paper_imp G (named_paper_all \<sigma> (NLam n (NApp F (NVar n)))) (named_paper_all \<sigma> F))"
proof -
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have variable: "paper_R_in_language \<Omega> G (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Omega> and G=G and n=n, OF nt rt])
  have body: "paper_R_in_language \<Omega> G (NApp F (NVar n)) Prop" by (rule paper_R_language_App[OF predicate variable])
  have nr: "paper_R_type (G n)" by (simp only: nt; rule rt)
  have lp: "paper_R_in_language \<Omega> G (NLam n (NApp F (NVar n))) (Arr \<sigma> Prop)"
    using paper_R_named_identity_test_language[OF body nr] by (simp only: nt)
  let ?L = "named_paper_all \<sigma> (NLam n (NApp F (NVar n)))"
  let ?R = "named_paper_all \<sigma> F"
  have ll: "paper_R_in_language \<Omega> G ?L Prop" by (rule paper_R_predicate_all_language[OF lp])
  have rl: "paper_R_in_language \<Omega> G ?R Prop" by (rule paper_R_predicate_all_language[OF predicate])
  have step: "named_compatible_step named_eta_contract ?L ?R"
    unfolding named_paper_all_def
    by (rule named_compatible_step.App_right, rule named_compatible_step.root, rule named_eta_contract.eta[OF fresh])
  have il: "paper_R_in_language \<Omega> G (named_paper_iff G ?L ?R) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich ll rl])
  have equivalence: "paper_R_named_H \<Omega> G (named_paper_iff G ?L ?R)"
    by (rule paper_R_named_H.Eta[OF ll rl step il])
  show ?thesis by (rule paper_R_named_H.MP[OF equivalence paper_R_named_H_iff_forward[OF rich ll rl]
    paper_R_named_paper_imp_language[OF rich ll rl]])
qed

section \<open>Universal-existential duality is an actual native R-H theorem\<close>

text \<open>
  ⊢Hᴿ ¬∀σF ↔ ∃σ(λn.¬F n), where n:σ and n∉FV(F).
  Source: Figure 2, p.8, and the universal direction of the
  canonical truth lemma in Theorem 3.2, footnote 64, p.45.

  Put X=∃σ(λn.¬F n). EG and literal same-variable β give
  ¬F n→X; PC, Gen and η give ¬X→∀σF. UI, PC
  contraposition and Inst give X→¬∀σF. An explicit PC
  certificate combines the implications into the displayed ↔.
  F may be open. No semantic quantifier duality, model, Functionality,
  full-F proof or added quantifier axiom is used.
\<close>

theorem paper_R_named_H_quantifier_duality:
  assumes rich: "paper_R_rich G" and predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
    and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "paper_R_named_H \<Omega> G
    (named_paper_iff G (named_paper_not (named_paper_all \<sigma> F))
      (named_paper_ex \<sigma> (NLam n (named_paper_not (NApp F (NVar n))))))"
proof -
  let ?B = "NApp F (NVar n)"
  let ?N = "named_paper_not ?B"
  let ?NF = "NLam n ?N"
  let ?X = "named_paper_ex \<sigma> ?NF"
  let ?A = "named_paper_all \<sigma> F"
  let ?L = "named_paper_all \<sigma> (NLam n ?B)"
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have variable: "paper_R_in_language \<Omega> G (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Omega> and G=G and n=n, OF nt rt])
  have bl: "paper_R_in_language \<Omega> G ?B Prop" by (rule paper_R_language_App[OF predicate variable])
  have nl: "paper_R_in_language \<Omega> G ?N Prop" by (rule paper_R_named_not_language[OF bl])
  have nr: "paper_R_type (G n)" by (simp only: nt; rule rt)
  have nf: "paper_R_in_language \<Omega> G ?NF (Arr \<sigma> Prop)"
    using paper_R_named_identity_test_language[OF nl nr] by (simp only: nt)
  have positive_predicate: "paper_R_in_language \<Omega> G (NLam n ?B) (Arr \<sigma> Prop)"
    using paper_R_named_identity_test_language[OF bl nr] by (simp only: nt)
  have xl: "paper_R_in_language \<Omega> G ?X Prop" by (rule paper_R_predicate_exists_language[OF nf])
  have al: "paper_R_in_language \<Omega> G ?A Prop" by (rule paper_R_predicate_all_language[OF predicate])
  have ll: "paper_R_in_language \<Omega> G ?L Prop" by (rule paper_R_predicate_all_language[OF positive_predicate])
  have nxl: "paper_R_in_language \<Omega> G (named_paper_not ?X) Prop" by (rule paper_R_named_not_language[OF xl])
  have nal: "paper_R_in_language \<Omega> G (named_paper_not ?A) Prop" by (rule paper_R_named_not_language[OF al])
  have application_language: "paper_R_in_language \<Omega> G (NApp ?NF (NVar n)) Prop"
    by (rule paper_R_language_App[OF nf variable])
  have free_for: "named_free_for (NVar n) n ?N" by (rule named_free_for_same_variable)
  have beta_root: "named_beta_contract (NApp ?NF (NVar n)) ?N"
    using named_beta_contract.beta[OF free_for] by (simp only: named_subst_same_variable)
  have beta_step: "named_compatible_step named_beta_contract (NApp ?NF (NVar n)) ?N"
    by (rule named_compatible_step.root[where R=named_beta_contract and M="NApp ?NF (NVar n)" and N="?N", OF beta_root])
  have beta_iff_language: "paper_R_in_language \<Omega> G (named_paper_iff G (NApp ?NF (NVar n)) ?N) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich application_language nl])
  have beta_iff: "paper_R_named_H \<Omega> G (named_paper_iff G (NApp ?NF (NVar n)) ?N)"
    by (rule paper_R_named_H.Beta[OF application_language nl beta_step beta_iff_language])
  have beta_backward: "paper_R_named_H \<Omega> G (named_paper_imp G ?N (NApp ?NF (NVar n)))"
    by (rule paper_R_named_H.MP[OF beta_iff paper_R_named_H_iff_backward[OF rich application_language nl]
      paper_R_named_paper_imp_language[OF rich nl application_language]])
  have eg: "paper_R_named_H \<Omega> G (named_paper_imp G (NApp ?NF (NVar n)) ?X)"
    by (rule paper_R_named_H.EG[OF paper_R_named_paper_imp_language[OF rich application_language xl]])
  have negative_to_exists: "paper_R_named_H \<Omega> G (named_paper_imp G ?N ?X)"
    by (rule paper_R_named_H_imp_trans[OF rich nl application_language xl beta_backward eg])
  have body_implication: "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_not ?X) ?B)"
    by (rule paper_R_named_H_negative_contraposition[OF rich bl xl negative_to_exists])
  have fresh_X: "n \<notin> named_fv (named_paper_not ?X)"
    by (simp add: named_paper_primitive_fv)
  have generalized: "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_not ?X) ?L)"
    by (rule paper_R_named_H.Gen[OF body_implication nt fresh_X paper_R_named_paper_imp_language[OF rich nxl ll]])
  have eta: "paper_R_named_H \<Omega> G (named_paper_imp G ?L ?A)"
    by (rule paper_R_named_H_all_eta_contract[OF rich predicate nt fresh])
  have first: "paper_R_named_H \<Omega> G (named_paper_imp G (named_paper_not ?X) ?A)"
    by (rule paper_R_named_H_imp_trans[OF rich nxl ll al generalized eta])
  have ui: "paper_R_named_H \<Omega> G (named_paper_imp G ?A ?B)"
    by (rule paper_R_named_H.UI[OF paper_R_named_paper_imp_language[OF rich al bl]])
  have contrapositive: "paper_R_named_H \<Omega> G (named_paper_imp G ?N (named_paper_not ?A))"
    by (rule paper_R_named_H_contraposition[OF rich al bl ui])
  have fresh_A: "n \<notin> named_fv (named_paper_not ?A)"
    using fresh by (simp only: named_paper_primitive_fv; simp)
  have second: "paper_R_named_H \<Omega> G (named_paper_imp G ?X (named_paper_not ?A))"
    by (rule paper_R_named_H.Inst[OF contrapositive nt fresh_A paper_R_named_paper_imp_language[OF rich xl nal]])
  show ?thesis by (rule paper_R_named_H_duality_from_implications[OF rich al xl first second])
qed

end
