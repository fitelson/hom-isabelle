theory Bacon_Source_Relational_Local_Exchange
  imports Bacon_Source_Relational_Deduction
begin

section \<open>Empty local consequence is exactly native H theoremhood\<close>

lemma paper_R_named_derivable_empty_frame:
  assumes derivation: "paper_R_named_derivable \<Sigma> G S A" and empty: "S = {}"
  shows "paper_R_named_H \<Sigma> G A"
  using derivation empty
proof (induction rule: paper_R_named_derivable.induct)
  case (Assumption A S)
  show ?case using Assumption.hyps(1) Assumption.prems by simp
next
  case (Theorem A S)
  show ?case by (rule Theorem.hyps)
next
  case (MP S A B)
  show ?case by (rule paper_R_named_H.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
qed

lemma paper_R_named_derivable_empty_iff:
  "paper_R_named_derivable \<Sigma> G {} A \<longleftrightarrow> paper_R_named_H \<Sigma> G A"
  using paper_R_named_derivable_empty_frame[where S="{}"] paper_R_named_derivable.Theorem by blast

section \<open>Exchange antecedents by an actual native PC certificate\<close>

lemma paper_R_named_H_imp_exchange:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and cl: "paper_R_in_language \<Sigma> G C Prop"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_imp G (named_paper_imp G A (named_paper_imp G B C))
      (named_paper_imp G B (named_paper_imp G A C)))"
proof -
  have bc: "paper_R_in_language \<Sigma> G (named_paper_imp G B C) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich bl cl])
  have ac: "paper_R_in_language \<Sigma> G (named_paper_imp G A C) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich al cl])
  have whole: "paper_R_in_language \<Sigma> G
    (named_paper_imp G (named_paper_imp G A (named_paper_imp G B C))
      (named_paper_imp G B (named_paper_imp G A C))) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich
      paper_R_named_paper_imp_language[OF rich al bc] paper_R_named_paper_imp_language[OF rich bl ac]])
  let ?P = "SPImp (SPImp (SPAtom (0::nat)) (SPImp (SPAtom 1) (SPAtom 2)))
    (SPImp (SPAtom 1) (SPImp (SPAtom 0) (SPAtom 2)))"
  have taut: "sprop_tautology ?P" by (auto simp: sprop_tautology_def)
  show ?thesis by (rule paper_R_named_H_PC_instance[OF whole taut,
    where v="\<lambda>i. if i=0 then A else if i=1 then B else C"]; simp)
qed

lemma paper_R_named_derivable_imp_exchange:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and cl: "paper_R_in_language \<Sigma> G C Prop"
    and derivation: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G A (named_paper_imp G B C))"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_imp G B (named_paper_imp G A C))"
proof -
  have axiom: "paper_R_named_derivable \<Sigma> G S
    (named_paper_imp G (named_paper_imp G A (named_paper_imp G B C))
      (named_paper_imp G B (named_paper_imp G A C)))"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_imp_exchange[OF rich al bl cl]])
  have language: "paper_R_in_language \<Sigma> G (named_paper_imp G B (named_paper_imp G A C)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich bl paper_R_named_paper_imp_language[OF rich al cl]])
  show ?thesis by (rule paper_R_named_derivable.MP[OF derivation axiom language])
qed

end
