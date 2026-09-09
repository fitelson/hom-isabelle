theory Bacon_Source_Relational_Consequence_Closure
  imports Bacon_Source_Relational_Consistency
begin

section \<open>Cut replaces only well-formed premises that are actually used\<close>

text \<open>
  If T⊢HᴿB and every usable member of T is derivable from S,
  then S⊢HᴿB. A usable member carries its R-formula guard.
  Unused malformed entries in either premise set impose no obligation.
  Source role: the local finite-premise reasoning underlying Theorem 3.2
  and footnote 73. There is no local Gen or Inst rule.
\<close>

theorem paper_R_named_derivable_cut:
  assumes derivation: "paper_R_named_derivable \<Sigma> G T B"
    and source_premises: "\<And>A. A \<in> T \<Longrightarrow> paper_R_in_language \<Sigma> G A Prop \<Longrightarrow>
      paper_R_named_derivable \<Sigma> G S A"
  shows "paper_R_named_derivable \<Sigma> G S B"
  using derivation source_premises
proof (induction rule: paper_R_named_derivable.induct)
  case (Assumption A T)
  show ?case by (rule Assumption.prems[OF Assumption.hyps])
next
  case (Theorem A T)
  show ?case by (rule paper_R_named_derivable.Theorem[OF Theorem.hyps])
next
  case (MP T A B)
  have first: "paper_R_named_derivable \<Sigma> G S A" by (rule MP.IH(1)[OF MP.prems])
  have second: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G A B)"
    by (rule MP.IH(2)[OF MP.prems])
  show ?case by (rule paper_R_named_derivable.MP[OF first second MP.hyps(3)])
qed

lemma paper_R_named_derivable_insert_cut:
  assumes inserted: "paper_R_named_derivable \<Sigma> G S A"
    and derivation: "paper_R_named_derivable \<Sigma> G (insert A S) B"
  shows "paper_R_named_derivable \<Sigma> G S B"
proof (rule paper_R_named_derivable_cut[OF derivation])
  fix C
  assume member: "C \<in> insert A S" and language: "paper_R_in_language \<Sigma> G C Prop"
  show "paper_R_named_derivable \<Sigma> G S C"
  proof (cases "C = A")
    case True
    show ?thesis by (simp only: True; rule inserted)
  next
    case False
    have original: "C \<in> S" using member False by blast
    show ?thesis by (rule paper_R_named_derivable.Assumption[OF original language])
  qed
qed

section \<open>Adding consequences and making one local decision\<close>

text \<open>
  Adding a derivable formula to a consistent local premise set preserves
  consistency. Hence, for every R formula A, either adding A or adding
  ¬A is consistent: if A is already derivable use cut, and otherwise
  use the proved negated-conclusion extension.

  S may be infinite and contain open formulas. These are local syntactic
  closure facts, not a globally satisfying model or a negation-complete
  open theory. No choice or maximal-extension principle is used.
\<close>

theorem paper_R_named_consistent_insert_derivable:
  assumes consistent: "paper_R_named_consistent \<Sigma> G S"
    and derivation: "paper_R_named_derivable \<Sigma> G S A"
  shows "paper_R_named_consistent \<Sigma> G (insert A S)"
proof (rule paper_R_named_consistentI)
  fix B
  assume positive: "paper_R_named_derivable \<Sigma> G (insert A S) B"
    and negative: "paper_R_named_derivable \<Sigma> G (insert A S) (named_paper_not B)"
  have original_positive: "paper_R_named_derivable \<Sigma> G S B"
    by (rule paper_R_named_derivable_insert_cut[OF derivation positive])
  have original_negative: "paper_R_named_derivable \<Sigma> G S (named_paper_not B)"
    by (rule paper_R_named_derivable_insert_cut[OF derivation negative])
  show False by (rule paper_R_named_consistentD[OF consistent original_positive original_negative])
qed

theorem paper_R_named_consistent_decision_extension:
  assumes rich: "paper_R_rich G" and consistent: "paper_R_named_consistent \<Sigma> G S"
    and language: "paper_R_in_language \<Sigma> G A Prop"
  shows "paper_R_named_consistent \<Sigma> G (insert A S) \<or>
    paper_R_named_consistent \<Sigma> G (insert (named_paper_not A) S)"
proof (cases "paper_R_named_derivable \<Sigma> G S A")
  case True
  show ?thesis by (rule disjI1, rule paper_R_named_consistent_insert_derivable[OF consistent True])
next
  case False
  show ?thesis by (rule disjI2, rule paper_R_named_consistent_insert_not[OF rich language False])
qed

end
