theory Bacon_Source_Relational_Existence
  imports Bacon_Source_Relational_Deduction
begin

section \<open>A native PC bridge from a biconditional back to its left side\<close>

lemma paper_R_named_H_iff_backward:
  assumes rich: "paper_R_rich G" and left: "paper_R_in_language \<Sigma> G A Prop"
    and right: "paper_R_in_language \<Sigma> G B Prop"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_imp G (named_paper_iff G A B) (named_paper_imp G B A))"
proof -
  have biconditional: "paper_R_in_language \<Sigma> G (named_paper_iff G A B) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich left right])
  have conditional: "paper_R_in_language \<Sigma> G (named_paper_imp G B A) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich right left])
  have whole: "paper_R_in_language \<Sigma> G
    (named_paper_imp G (named_paper_iff G A B) (named_paper_imp G B A)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich biconditional conditional])
  have tautology: "sprop_tautology (SPImp (SPIff (SPAtom (0::nat)) (SPAtom 1)) (SPImp (SPAtom 1) (SPAtom 0)))"
    by (auto simp: sprop_tautology_def)
  show ?thesis by (rule paper_R_named_H_PC_instance[OF whole tautology,
    where v="\<lambda>i. if i=0 then A else B"]; simp)
qed

section \<open>Existence is derived at each R type\<close>

text \<open>
  ⊢Hᴿ ∃n:σ.(n=σn).
  Source: the Existence discussion following Figure 2, pp.8–9.
  Ref proves n=n. One literal β step gives (λn.n=n)n↔n=n;
  PC and MP therefore prove that application, and EG yields Existence.

  The witness argument is the variable n itself. Substitution of n for
  n is explicitly free-for and is the identity on the body, including
  any shadowing. No new Existence rule, F theorem, model nonemptiness,
  or closed inhabitant in the original nonlogical signature is assumed.
  This theorem will later supply inhabited closed-term classes only
  after the separate witness-completion construction.
\<close>

theorem paper_R_named_type_existence:
  assumes variable: "G n = \<sigma>" and rt: "paper_R_type \<sigma>" and rich: "paper_R_rich G"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_ex \<sigma> (NLam n (named_paper_eq \<sigma> (NVar n) (NVar n))))"
proof -
  let ?v = "NVar n"
  let ?E = "named_paper_eq \<sigma> ?v ?v"
  let ?F = "NLam n ?E"
  let ?A = "NApp ?F ?v"
  let ?X = "named_paper_ex \<sigma> ?F"
  have vt: "paper_R_has_type G ?v \<sigma>"
  proof -
    have nr: "paper_R_type (G n)" by (simp only: variable; rule rt)
    show ?thesis using paper_R_has_type.Var[where G=G and n=n, OF nr]
      by (simp only: variable)
  qed
  have vl: "paper_R_in_language \<Sigma> G ?v \<sigma>"
    unfolding paper_R_in_language_def by (rule conjI[OF vt]; simp)
  have eqr: "paper_R_type (paper_logical_type (SEq \<sigma>))" using rt by simp
  have eqt: "paper_R_has_type G (NLogical (SEq \<sigma>)) (Arr \<sigma> (Arr \<sigma> Prop))"
    using paper_R_has_type.Logical[where G=G and l="SEq \<sigma>", OF eqr] by simp
  have et: "paper_R_has_type G ?E Prop"
    unfolding named_paper_eq_def by (rule paper_R_has_type.App[OF paper_R_has_type.App[OF eqt vt] vt])
  have el: "paper_R_in_language \<Sigma> G ?E Prop"
    unfolding paper_R_in_language_def by (rule conjI[OF et]; simp add: named_paper_eq_def)
  have nr: "paper_R_type (G n)" by (simp only: variable; rule rt)
  have raw_ft: "paper_R_has_type G ?F (Arr (G n) Prop)"
    by (rule paper_R_has_type.Lam[OF et nr]; simp)
  have ft: "paper_R_has_type G ?F (Arr \<sigma> Prop)" using raw_ft by (simp only: variable)
  have fl: "paper_R_in_language \<Sigma> G ?F (Arr \<sigma> Prop)"
    unfolding paper_R_in_language_def by (rule conjI[OF ft]; simp add: named_paper_eq_def)
  have al: "paper_R_in_language \<Sigma> G ?A Prop" by (rule paper_R_language_App[OF fl vl])
  have exr: "paper_R_type (paper_logical_type (SEx \<sigma>))" using rt by simp
  have ext: "paper_R_has_type G (NLogical (SEx \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_R_has_type.Logical[where G=G and l="SEx \<sigma>", OF exr] by simp
  have xt: "paper_R_has_type G ?X Prop"
    unfolding named_paper_ex_def by (rule paper_R_has_type.App[OF ext ft])
  have xl: "paper_R_in_language \<Sigma> G ?X Prop"
    unfolding paper_R_in_language_def by (rule conjI[OF xt]; simp add: named_paper_ex_def named_paper_eq_def)
  have reflexive: "paper_R_named_H \<Sigma> G ?E" by (rule paper_R_named_H.Ref[OF el])
  have free_for: "named_free_for ?v n ?E" by (rule named_free_for_same_variable)
  have root_step: "named_beta_contract ?A ?E"
    using named_beta_contract.beta[OF free_for] by (simp only: named_subst_same_variable)
  have step: "named_compatible_step named_beta_contract ?A ?E"
    by (rule named_compatible_step.root[where R=named_beta_contract and M="?A" and N="?E", OF root_step])
  have iff_language: "paper_R_in_language \<Sigma> G (named_paper_iff G ?A ?E) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich al el])
  have conversion: "paper_R_named_H \<Sigma> G (named_paper_iff G ?A ?E)"
    by (rule paper_R_named_H.Beta[OF al el step iff_language])
  have backwards: "paper_R_named_H \<Sigma> G (named_paper_imp G ?E ?A)"
    by (rule paper_R_named_H.MP[OF conversion paper_R_named_H_iff_backward[OF rich al el]
      paper_R_named_paper_imp_language[OF rich el al]])
  have application: "paper_R_named_H \<Sigma> G ?A" by (rule paper_R_named_H.MP[OF reflexive backwards al])
  have eg_language: "paper_R_in_language \<Sigma> G (named_paper_imp G ?A ?X) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich al xl])
  have eg: "paper_R_named_H \<Sigma> G (named_paper_imp G ?A ?X)" by (rule paper_R_named_H.EG[OF eg_language])
  show ?thesis by (rule paper_R_named_H.MP[OF application eg xl])
qed

lemma paper_R_named_type_existence_closed:
  "named_fv (named_paper_ex \<sigma> (NLam n (named_paper_eq \<sigma> (NVar n) (NVar n)))) = {}"
  by (simp add: named_paper_ex_def named_paper_eq_def)

corollary paper_R_named_type_existence_language:
  assumes variable: "G n = \<sigma>" and rt: "paper_R_type \<sigma>" and rich: "paper_R_rich G"
  shows "paper_R_in_language \<Sigma> G
    (named_paper_ex \<sigma> (NLam n (named_paper_eq \<sigma> (NVar n) (NVar n)))) Prop"
  by (rule paper_R_named_H_language[OF paper_R_named_type_existence[OF variable rt rich]])

end
