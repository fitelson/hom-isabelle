theory Bacon_Source_Local_Cut
  imports Bacon_Source_Local_Deduction
begin

section \<open>Replacing locally used assumptions by local derivations\<close>

text \<open>
  If T ⊢H A and S ⊢H B for every B in T, then S ⊢H A.
  This is composition of finite assumption/theorem/MP proofs, the local
  consequence notion associated with Bacon–Dorr Figure 2.

  Isabelle representation: induction on paper_global_derivable replaces
  assumption leaves, retains actual source H theorem leaves, and composes MP.
  Neither premise set needs to be finite or globally well-formed.

  Status: source local cut only. It does not generalize under undischarged
  assumptions and has no target proof or model premise.
\<close>

theorem paper_global_derivable_cut:
  assumes derivation: "paper_global_derivable \<Sigma> G T A"
    and replacements: "\<And>B. B \<in> T \<Longrightarrow> paper_global_derivable \<Sigma> G S B"
  shows "paper_global_derivable \<Sigma> G S A"
  using derivation replacements
proof (induction rule: paper_global_derivable.induct)
  case (Assumption A T)
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case (Theorem A T)
  show ?case by (rule paper_global_derivable.Theorem[OF Theorem.hyps])
next
  case (MP T A B)
  have left: "paper_global_derivable \<Sigma> G S A" by (rule MP.IH(1)[OF MP.prems])
  have right: "paper_global_derivable \<Sigma> G S (paper_imp A B)" by (rule MP.IH(2)[OF MP.prems])
  show ?case by (rule paper_global_derivable.MP[OF left right])
qed

end
