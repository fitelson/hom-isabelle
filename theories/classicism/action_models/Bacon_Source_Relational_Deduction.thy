theory Bacon_Source_Relational_Deduction
  imports Bacon_Source_Relational_Local_Consequence Bacon_Source_Relational_Logical_Language
begin

section \<open>The three native PC certificates needed for local deduction\<close>

text \<open>
  We use A→A, B→(A→B), and
  (A→(B→C))→((A→B)→(A→C)), each as an actual native
  R-PC instance. The operators remain Figure 1's literal λ definitions.
  No F theoremhood, semantic tautology principle for object terms,
  or pre-existing deduction theorem is used.
\<close>

lemma paper_R_named_H_PC_instance:
  fixes P :: "nat sprop_template"
  assumes language: "paper_R_in_language \<Sigma> G A Prop"
    and tautology: "sprop_tautology P"
    and instance_eq: "A = named_paper_prop_instance G v P"
  shows "paper_R_named_H \<Sigma> G A"
proof (rule paper_R_named_H.PC)
  show "paper_R_named_PC \<Sigma> G A"
    unfolding paper_R_named_PC_def
    by (rule conjI[OF language], rule exI[where x=P], rule exI[where x=v],
      rule conjI[OF tautology instance_eq])
qed

lemma paper_R_named_H_imp_refl:
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G A Prop"
  shows "paper_R_named_H \<Sigma> G (named_paper_imp G A A)"
proof -
  have whole: "paper_R_in_language \<Sigma> G (named_paper_imp G A A) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich language language])
  have tautology: "sprop_tautology (SPImp (SPAtom (0::nat)) (SPAtom 0))"
    by (simp add: sprop_tautology_def)
  show ?thesis by (rule paper_R_named_H_PC_instance[OF whole tautology, where v="\<lambda>_. A"]; simp)
qed

lemma paper_R_named_H_imp_weaken:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
  shows "paper_R_named_H \<Sigma> G (named_paper_imp G B (named_paper_imp G A B))"
proof -
  have whole: "paper_R_in_language \<Sigma> G (named_paper_imp G B (named_paper_imp G A B)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich bl paper_R_named_paper_imp_language[OF rich al bl]])
  have tautology: "sprop_tautology (SPImp (SPAtom (0::nat)) (SPImp (SPAtom 1) (SPAtom 0)))"
    by (simp add: sprop_tautology_def)
  show ?thesis
    by (rule paper_R_named_H_PC_instance[OF whole tautology, where v="\<lambda>i. if i=0 then B else A"]; simp)
qed

lemma paper_R_named_H_imp_distribute:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and cl: "paper_R_in_language \<Sigma> G C Prop"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_imp G (named_paper_imp G A (named_paper_imp G B C))
      (named_paper_imp G (named_paper_imp G A B) (named_paper_imp G A C)))"
proof -
  have bc: "paper_R_in_language \<Sigma> G (named_paper_imp G B C) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich bl cl])
  have abc: "paper_R_in_language \<Sigma> G (named_paper_imp G A (named_paper_imp G B C)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich al bc])
  have ab: "paper_R_in_language \<Sigma> G (named_paper_imp G A B) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich al bl])
  have ac: "paper_R_in_language \<Sigma> G (named_paper_imp G A C) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich al cl])
  have whole: "paper_R_in_language \<Sigma> G
    (named_paper_imp G (named_paper_imp G A (named_paper_imp G B C))
      (named_paper_imp G (named_paper_imp G A B) (named_paper_imp G A C))) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich abc paper_R_named_paper_imp_language[OF rich ab ac]])
  let ?P = "SPImp (SPImp (SPAtom (0::nat)) (SPImp (SPAtom 1) (SPAtom 2)))
    (SPImp (SPImp (SPAtom 0) (SPAtom 1)) (SPImp (SPAtom 0) (SPAtom 2)))"
  have tautology: "sprop_tautology ?P" by (auto simp: sprop_tautology_def)
  show ?thesis by (rule paper_R_named_H_PC_instance[OF whole tautology,
    where v="\<lambda>i. if i=0 then A else if i=1 then B else C"]; simp)
qed

section \<open>Conditionalization steps stay inside local R consequence\<close>

lemma paper_R_named_derivable_imp_weaken:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and derivation: "paper_R_named_derivable \<Sigma> G S B"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_imp G A B)"
proof -
  have bl: "paper_R_in_language \<Sigma> G B Prop" by (rule paper_R_named_derivable_language[OF derivation])
  have axiom: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G B (named_paper_imp G A B))"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_imp_weaken[OF rich al bl]])
  show ?thesis by (rule paper_R_named_derivable.MP[
    OF derivation axiom paper_R_named_paper_imp_language[OF rich al bl]])
qed

lemma paper_R_named_derivable_conditional_MP:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and cl: "paper_R_in_language \<Sigma> G C Prop"
    and first: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G A B)"
    and second: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G A (named_paper_imp G B C))"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_imp G A C)"
proof -
  have ab: "paper_R_in_language \<Sigma> G (named_paper_imp G A B) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich al bl])
  have ac: "paper_R_in_language \<Sigma> G (named_paper_imp G A C) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich al cl])
  have axiom: "paper_R_named_derivable \<Sigma> G S
    (named_paper_imp G (named_paper_imp G A (named_paper_imp G B C))
      (named_paper_imp G (named_paper_imp G A B) (named_paper_imp G A C)))"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_imp_distribute[OF rich al bl cl]])
  have conditional: "paper_R_named_derivable \<Sigma> G S
    (named_paper_imp G (named_paper_imp G A B) (named_paper_imp G A C))"
    by (rule paper_R_named_derivable.MP[
      OF second axiom paper_R_named_paper_imp_language[OF rich ab ac]])
  show ?thesis by (rule paper_R_named_derivable.MP[OF first conditional ac])
qed

section \<open>Deduction for Assumption, Theorem and MP only\<close>

text \<open>
  S∪{A}⊢HᴿB implies S⊢HᴿA→B.
  Source role: local consequence in pp.7–8 and the finite-diagram
  implication in Theorem 3.12, footnote 73, pp.51–52.

  S is arbitrary: it need not be finite, closed, or wholly well-typed.
  Every assumption actually used carries its own R-language guard.
  The distinguished A must be an R formula; B's language follows
  from its derivation. There are no local Gen/Inst cases. A theorem
  leaf may contain those rules internally, but is conditionalized
  as a whole theorem. This establishes no model-existence claim.
\<close>

lemma paper_R_named_derivable_deduction_frame:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and derivation: "paper_R_named_derivable \<Sigma> G T B" and frame: "T = insert A S"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_imp G A B)"
  using derivation frame
proof (induction rule: paper_R_named_derivable.induct)
  case (Assumption B T)
  show ?case
  proof (cases "B = A")
    case True
    show ?thesis by (simp only: True;
      rule paper_R_named_derivable.Theorem[OF paper_R_named_H_imp_refl[OF rich al]])
  next
    case False
    have member: "B \<in> S" using Assumption.hyps(1) Assumption.prems False by blast
    have premise: "paper_R_named_derivable \<Sigma> G S B"
      by (rule paper_R_named_derivable.Assumption[OF member Assumption.hyps(2)])
    show ?thesis by (rule paper_R_named_derivable_imp_weaken[OF rich al premise])
  qed
next
  case (Theorem B T)
  have premise: "paper_R_named_derivable \<Sigma> G S B"
    by (rule paper_R_named_derivable.Theorem[OF Theorem.hyps])
  show ?case by (rule paper_R_named_derivable_imp_weaken[OF rich al premise])
next
  case (MP T B C)
  have bl: "paper_R_in_language \<Sigma> G B Prop"
    by (rule paper_R_named_derivable_language[OF MP.hyps(1)])
  have first: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G A B)"
    by (rule MP.IH(1)[OF MP.prems])
  have second: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G A (named_paper_imp G B C))"
    by (rule MP.IH(2)[OF MP.prems])
  show ?case by (rule paper_R_named_derivable_conditional_MP[OF rich al bl MP.hyps(3) first second])
qed

theorem paper_R_named_derivable_deduction:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and derivation: "paper_R_named_derivable \<Sigma> G (insert A S) B"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_imp G A B)"
  by (rule paper_R_named_derivable_deduction_frame[OF rich al derivation refl])

corollary paper_R_named_derivable_deduction_iff:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
  shows "paper_R_named_derivable \<Sigma> G (insert A S) B \<longleftrightarrow>
    paper_R_named_derivable \<Sigma> G S (named_paper_imp G A B)"
proof
  assume derivation: "paper_R_named_derivable \<Sigma> G (insert A S) B"
  show "paper_R_named_derivable \<Sigma> G S (named_paper_imp G A B)"
    by (rule paper_R_named_derivable_deduction[OF rich al derivation])
next
  assume implication: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G A B)"
  have subset: "S \<subseteq> insert A S" by auto
  have moved: "paper_R_named_derivable \<Sigma> G (insert A S) (named_paper_imp G A B)"
    by (rule paper_R_named_derivable_mono[where \<Sigma>=\<Sigma> and G=G and S=S and T="insert A S",
      OF implication subset])
  have antecedent: "paper_R_named_derivable \<Sigma> G (insert A S) A"
    by (rule paper_R_named_derivable.Assumption; (rule insertI1 | rule al))
  show "paper_R_named_derivable \<Sigma> G (insert A S) B"
    by (rule paper_R_named_derivable.MP[OF antecedent moved bl])
qed

end
