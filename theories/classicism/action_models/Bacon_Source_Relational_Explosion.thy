theory Bacon_Source_Relational_Explosion
  imports Bacon_Source_Relational_Deduction
begin

section \<open>Native PC certificates for contradiction and reductio\<close>

lemma paper_R_named_H_explosion:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
  shows "paper_R_named_H \<Sigma> G (named_paper_imp G A (named_paper_imp G (named_paper_not A) B))"
proof -
  have na: "paper_R_in_language \<Sigma> G (named_paper_not A) Prop"
    by (rule paper_R_named_not_language[OF al])
  have whole: "paper_R_in_language \<Sigma> G
    (named_paper_imp G A (named_paper_imp G (named_paper_not A) B)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich al paper_R_named_paper_imp_language[OF rich na bl]])
  have tautology: "sprop_tautology (SPImp (SPAtom (0::nat)) (SPImp (SPNot (SPAtom 0)) (SPAtom 1)))"
    by (simp add: sprop_tautology_def)
  show ?thesis by (rule paper_R_named_H_PC_instance[OF whole tautology,
    where v="\<lambda>i. if i=0 then A else B"]; simp)
qed

lemma paper_R_named_H_contradiction_discharge:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_imp G (named_paper_imp G (named_paper_not B) A)
      (named_paper_imp G (named_paper_imp G (named_paper_not B) (named_paper_not A)) B))"
proof -
  have na: "paper_R_in_language \<Sigma> G (named_paper_not A) Prop"
    by (rule paper_R_named_not_language[OF al])
  have nb: "paper_R_in_language \<Sigma> G (named_paper_not B) Prop"
    by (rule paper_R_named_not_language[OF bl])
  have first: "paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_not B) A) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich nb al])
  have second: "paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_not B) (named_paper_not A)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich nb na])
  have whole: "paper_R_in_language \<Sigma> G
    (named_paper_imp G (named_paper_imp G (named_paper_not B) A)
      (named_paper_imp G (named_paper_imp G (named_paper_not B) (named_paper_not A)) B)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich first paper_R_named_paper_imp_language[OF rich second bl]])
  let ?P = "SPImp (SPImp (SPNot (SPAtom (1::nat))) (SPAtom 0))
    (SPImp (SPImp (SPNot (SPAtom 1)) (SPNot (SPAtom 0))) (SPAtom 1))"
  have tautology: "sprop_tautology ?P" by (auto simp: sprop_tautology_def)
  show ?thesis by (rule paper_R_named_H_PC_instance[OF whole tautology,
    where v="\<lambda>i. if i=0 then A else B"]; simp)
qed

section \<open>Explosion and reductio in local consequence\<close>

text \<open>
  A derivable contradictory pair yields every well-formed R formula.
  Conversely, a contradictory pair obtained locally after assuming ¬B
  yields B without that assumption. The witnesses may be open.
  Source role: consistency and finite-premise reasoning in Theorem 3.2,
  footnote 64, and Theorem 3.12, footnote 73.
  Only native R-PC, MP and the local deduction theorem are used.
\<close>

theorem paper_R_named_derivable_explosion:
  assumes rich: "paper_R_rich G"
    and positive: "paper_R_named_derivable \<Sigma> G S A"
    and negative: "paper_R_named_derivable \<Sigma> G S (named_paper_not A)"
    and conclusion: "paper_R_in_language \<Sigma> G B Prop"
  shows "paper_R_named_derivable \<Sigma> G S B"
proof -
  have al: "paper_R_in_language \<Sigma> G A Prop" by (rule paper_R_named_derivable_language[OF positive])
  have na: "paper_R_in_language \<Sigma> G (named_paper_not A) Prop"
    by (rule paper_R_named_not_language[OF al])
  have axiom: "paper_R_named_derivable \<Sigma> G S
    (named_paper_imp G A (named_paper_imp G (named_paper_not A) B))"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_explosion[OF rich al conclusion]])
  have conditional: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G (named_paper_not A) B)"
    by (rule paper_R_named_derivable.MP[
      OF positive axiom paper_R_named_paper_imp_language[OF rich na conclusion]])
  show ?thesis by (rule paper_R_named_derivable.MP[OF negative conditional conclusion])
qed

theorem paper_R_named_derivable_reductio:
  assumes rich: "paper_R_rich G" and bl: "paper_R_in_language \<Sigma> G B Prop"
    and positive: "paper_R_named_derivable \<Sigma> G (insert (named_paper_not B) S) A"
    and negative: "paper_R_named_derivable \<Sigma> G (insert (named_paper_not B) S) (named_paper_not A)"
  shows "paper_R_named_derivable \<Sigma> G S B"
proof -
  have al: "paper_R_in_language \<Sigma> G A Prop" by (rule paper_R_named_derivable_language[OF positive])
  have na: "paper_R_in_language \<Sigma> G (named_paper_not A) Prop"
    by (rule paper_R_named_not_language[OF al])
  have nb: "paper_R_in_language \<Sigma> G (named_paper_not B) Prop"
    by (rule paper_R_named_not_language[OF bl])
  have first: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G (named_paper_not B) A)"
    by (rule paper_R_named_derivable_deduction[OF rich nb positive])
  have second: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G (named_paper_not B) (named_paper_not A))"
    by (rule paper_R_named_derivable_deduction[OF rich nb negative])
  have second_language: "paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_not B) (named_paper_not A)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich nb na])
  have axiom: "paper_R_named_derivable \<Sigma> G S
    (named_paper_imp G (named_paper_imp G (named_paper_not B) A)
      (named_paper_imp G (named_paper_imp G (named_paper_not B) (named_paper_not A)) B))"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_contradiction_discharge[OF rich al bl]])
  have conditional: "paper_R_named_derivable \<Sigma> G S
    (named_paper_imp G (named_paper_imp G (named_paper_not B) (named_paper_not A)) B)"
    by (rule paper_R_named_derivable.MP[
      OF first axiom paper_R_named_paper_imp_language[OF rich second_language bl]])
  show ?thesis by (rule paper_R_named_derivable.MP[OF second conditional bl])
qed

end
