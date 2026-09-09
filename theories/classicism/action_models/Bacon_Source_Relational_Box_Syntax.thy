theory Bacon_Source_Relational_Box_Syntax
  imports Bacon_Source_Relational_Identity_Proof_Basics
begin

section \<open>The literal necessity operator of Figure 1\<close>

definition paper_R_named_box_const :: "sgcontext \<Rightarrow> 'c paper_named_term" where
  "paper_R_named_box_const G = NLam (named_paper_p G)
    (named_paper_eq Prop (NVar (named_paper_p G))
      (named_paper_or (NVar (named_paper_p G)) (named_paper_not (NVar (named_paper_p G)))))"

definition paper_R_named_box :: "sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term" where
  "paper_R_named_box G P = NApp (paper_R_named_box_const G) P"

lemma paper_R_named_box_const_closed:
  "named_fv (paper_R_named_box_const G) = {}"
  by (simp add: paper_R_named_box_const_def named_paper_primitive_fv)

lemma paper_R_named_box_fv:
  "named_fv (paper_R_named_box G P) = named_fv P"
  by (simp add: paper_R_named_box_def paper_R_named_box_const_closed)

lemma paper_R_named_box_const_language:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "paper_R_rich G"
  shows "paper_R_in_language \<Sigma> G (paper_R_named_box_const G) (Arr Prop Prop)"
proof -
  let ?p = "named_paper_p G"
  let ?P = "NVar ?p"
  let ?B = "named_paper_eq Prop ?P (named_paper_or ?P (named_paper_not ?P)) :: 'c paper_named_term"
  have pt: "G ?p = Prop" by (rule paper_R_named_paper_p_type[OF rich])
  have rt: "paper_R_type Prop" by simp
  have variable: "paper_R_in_language \<Sigma> G ?P Prop"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n="?p", OF pt rt])
  have body: "paper_R_in_language \<Sigma> G ?B Prop"
    by (rule paper_R_named_identity_language[OF variable
      paper_R_named_or_language[OF variable paper_R_named_not_language[OF variable]]])
  have bt: "paper_R_has_type G ?B Prop" using body unfolding paper_R_in_language_def by (rule conjunct1)
  have pr: "paper_R_type (G ?p)" by (simp only: pt; rule rt)
  have abstraction: "paper_R_has_type G (NLam ?p ?B) (Arr (G ?p) Prop)"
    by (rule paper_R_has_type.Lam[OF bt pr]; simp)
  show ?thesis using abstraction
    by (simp add: paper_R_in_language_def paper_R_named_box_const_def pt
      named_paper_eq_def named_paper_or_def named_paper_not_def)
qed

lemma paper_R_named_box_language:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G P Prop"
  shows "paper_R_in_language \<Sigma> G (paper_R_named_box G P) Prop"
  unfolding paper_R_named_box_def by (rule paper_R_language_App[OF paper_R_named_box_const_language[OF rich] language])

text \<open>
  □ is λp.(p=ₜ(p∨¬p)), exactly Figure 1, p.6. □P is its
  application, not an inlined definition by an arbitrary truth constant.
  The one β step below is literal and free-for for every payload P:
  the shallow equality/Boolean body contains no further binder.
  This is syntax and an H β certificate, not an H Necessitation rule.
\<close>

lemma paper_R_named_box_beta:
  "named_compatible_step named_beta_contract (paper_R_named_box G P)
    (named_paper_eq Prop P (named_paper_or P (named_paper_not P)))"
proof -
  let ?p = "named_paper_p G"
  let ?B = "named_paper_eq Prop (NVar ?p) (named_paper_or (NVar ?p) (named_paper_not (NVar ?p)))"
  have free_for: "named_free_for P ?p ?B"
    by (simp add: named_paper_eq_def named_paper_or_def named_paper_not_def)
  have contract: "named_beta_contract (NApp (NLam ?p ?B) P)
    (named_paper_eq Prop P (named_paper_or P (named_paper_not P)))"
    using named_beta_contract.beta[OF free_for]
    by (simp add: named_paper_eq_def named_paper_or_def named_paper_not_def)
  show ?thesis unfolding paper_R_named_box_def paper_R_named_box_const_def
    by (rule named_compatible_step.root[where R=named_beta_contract and M="NApp (NLam ?p ?B) P"
      and N="named_paper_eq Prop P (named_paper_or P (named_paper_not P))", OF contract])
qed

theorem paper_R_named_H_box_fold:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_imp G (named_paper_eq Prop P (named_paper_or P (named_paper_not P))) (paper_R_named_box G P))"
proof -
  have bl: "paper_R_in_language \<Sigma> G (paper_R_named_box G P) Prop" by (rule paper_R_named_box_language[OF rich pl])
  have el: "paper_R_in_language \<Sigma> G (named_paper_eq Prop P (named_paper_or P (named_paper_not P))) Prop"
    by (rule paper_R_named_identity_language[OF pl paper_R_named_or_language[OF pl paper_R_named_not_language[OF pl]]])
  have il: "paper_R_in_language \<Sigma> G
    (named_paper_iff G (paper_R_named_box G P) (named_paper_eq Prop P (named_paper_or P (named_paper_not P)))) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich bl el])
  have conversion: "paper_R_named_H \<Sigma> G
    (named_paper_iff G (paper_R_named_box G P) (named_paper_eq Prop P (named_paper_or P (named_paper_not P))))"
    by (rule paper_R_named_H.Beta[OF bl el paper_R_named_box_beta il])
  show ?thesis by (rule paper_R_named_H.MP[OF conversion paper_R_named_H_iff_backward[OF rich bl el]
    paper_R_named_paper_imp_language[OF rich el bl]])
qed

end
