theory Bacon_Source_Relational_Witness_Propositional
  imports Bacon_Source_Relational_Explosion
begin

section \<open>Discharge a positive assumption from a contradictory pair\<close>

lemma paper_R_named_H_positive_discharge:
  assumes rich: "paper_R_rich G" and wl: "paper_R_in_language \<Sigma> G W Prop"
    and al: "paper_R_in_language \<Sigma> G A Prop"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_imp G (named_paper_imp G W A)
      (named_paper_imp G (named_paper_imp G W (named_paper_not A)) (named_paper_not W)))"
proof -
  have na: "paper_R_in_language \<Sigma> G (named_paper_not A) Prop" by (rule paper_R_named_not_language[OF al])
  have nw: "paper_R_in_language \<Sigma> G (named_paper_not W) Prop" by (rule paper_R_named_not_language[OF wl])
  have wa: "paper_R_in_language \<Sigma> G (named_paper_imp G W A) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich wl al])
  have wna: "paper_R_in_language \<Sigma> G (named_paper_imp G W (named_paper_not A)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich wl na])
  have whole: "paper_R_in_language \<Sigma> G
    (named_paper_imp G (named_paper_imp G W A)
      (named_paper_imp G (named_paper_imp G W (named_paper_not A)) (named_paper_not W))) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich wa paper_R_named_paper_imp_language[OF rich wna nw]])
  let ?P = "SPImp (SPImp (SPAtom (0::nat)) (SPAtom 1))
    (SPImp (SPImp (SPAtom 0) (SPNot (SPAtom 1))) (SPNot (SPAtom 0)))"
  have taut: "sprop_tautology ?P" by (auto simp: sprop_tautology_def)
  show ?thesis by (rule paper_R_named_H_PC_instance[OF whole taut, where v="\<lambda>i. if i=0 then W else A"]; simp)
qed

theorem paper_R_named_derivable_not_intro:
  assumes rich: "paper_R_rich G" and wl: "paper_R_in_language \<Sigma> G W Prop"
    and positive: "paper_R_named_derivable \<Sigma> G (insert W S) A"
    and negative: "paper_R_named_derivable \<Sigma> G (insert W S) (named_paper_not A)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_not W)"
proof -
  have al: "paper_R_in_language \<Sigma> G A Prop" by (rule paper_R_named_derivable_language[OF positive])
  have na: "paper_R_in_language \<Sigma> G (named_paper_not A) Prop" by (rule paper_R_named_not_language[OF al])
  have nw: "paper_R_in_language \<Sigma> G (named_paper_not W) Prop" by (rule paper_R_named_not_language[OF wl])
  have first: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G W A)"
    by (rule paper_R_named_derivable_deduction[OF rich wl positive])
  have second: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G W (named_paper_not A))"
    by (rule paper_R_named_derivable_deduction[OF rich wl negative])
  have sl: "paper_R_in_language \<Sigma> G (named_paper_imp G W (named_paper_not A)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich wl na])
  have axiom: "paper_R_named_derivable \<Sigma> G S
    (named_paper_imp G (named_paper_imp G W A)
      (named_paper_imp G (named_paper_imp G W (named_paper_not A)) (named_paper_not W)))"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_positive_discharge[OF rich wl al]])
  have conditional: "paper_R_named_derivable \<Sigma> G S
    (named_paper_imp G (named_paper_imp G W (named_paper_not A)) (named_paper_not W))"
    by (rule paper_R_named_derivable.MP[OF first axiom paper_R_named_paper_imp_language[OF rich sl nw]])
  show ?thesis by (rule paper_R_named_derivable.MP[OF second conditional nw])
qed

section \<open>The two consequences of a failed conditional witness\<close>

text \<open>
  From ¬(E→B), propositional logic gives E and B→¬E.
  Both are actual native R-PC instances. Their later application to
  E=∃σF and B=Fx will precede the separately proved local Inst rule.
  No quantifier, consistency or model premise occurs here.
\<close>

lemma paper_R_named_derivable_not_imp_components:
  assumes rich: "paper_R_rich G" and el: "paper_R_in_language \<Sigma> G E Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
    and failed: "paper_R_named_derivable \<Sigma> G S (named_paper_not (named_paper_imp G E B))"
  shows "paper_R_named_derivable \<Sigma> G S E \<and>
    paper_R_named_derivable \<Sigma> G S (named_paper_imp G B (named_paper_not E))"
proof -
  let ?N = "named_paper_not (named_paper_imp G E B)"
  let ?C = "named_paper_imp G B (named_paper_not E)"
  have nl: "paper_R_in_language \<Sigma> G ?N Prop"
    by (rule paper_R_named_not_language[OF paper_R_named_paper_imp_language[OF rich el bl]])
  have cl: "paper_R_in_language \<Sigma> G ?C Prop"
    by (rule paper_R_named_paper_imp_language[OF rich bl paper_R_named_not_language[OF el]])
  have first_language: "paper_R_in_language \<Sigma> G (named_paper_imp G ?N E) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich nl el])
  have second_language: "paper_R_in_language \<Sigma> G (named_paper_imp G ?N ?C) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich nl cl])
  have first_taut: "sprop_tautology (SPImp (SPNot (SPImp (SPAtom (0::nat)) (SPAtom 1))) (SPAtom 0))"
    by (auto simp: sprop_tautology_def)
  have second_taut: "sprop_tautology
    (SPImp (SPNot (SPImp (SPAtom (0::nat)) (SPAtom 1))) (SPImp (SPAtom 1) (SPNot (SPAtom 0))))"
    by (auto simp: sprop_tautology_def)
  have first: "paper_R_named_H \<Sigma> G (named_paper_imp G ?N E)"
    by (rule paper_R_named_H_PC_instance[OF first_language first_taut, where v="\<lambda>i. if i=0 then E else B"]; simp)
  have second: "paper_R_named_H \<Sigma> G (named_paper_imp G ?N ?C)"
    by (rule paper_R_named_H_PC_instance[OF second_language second_taut, where v="\<lambda>i. if i=0 then E else B"]; simp)
  show ?thesis by (rule conjI;
    (rule paper_R_named_derivable.MP[OF failed paper_R_named_derivable.Theorem[OF first] el] |
     rule paper_R_named_derivable.MP[OF failed paper_R_named_derivable.Theorem[OF second] cl]))
qed

end
