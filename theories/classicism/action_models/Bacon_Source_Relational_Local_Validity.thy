theory Bacon_Source_Relational_Local_Validity
  imports Bacon_Source_Relational_H_Soundness
    Bacon_Source_Relational_Local_Consequence
begin

section \<open>Local H consequence preserves truth in every assignment\<close>

text \<open>
  If every member of S is valid in an independent R-BBK model and
  S ⊢H A, then A is valid in that model. We follow the three local
  consequence constructors: Assumption, Theorem, and MP. The MP
  validity lemma extends a partial assignment only at R variables.

  Source: the soundness direction of Bacon–Dorr Theorem 3.2, pp.44–45.
  This statement assumes global validity of the premises. It does not
  turn truth of open premises at one assignment into global validity,
  and uses neither model existence nor a canonical-model premise.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_named_derivable_valid:
  assumes derivation: "paper_R_named_derivable signature stock S A"
    and premises_valid: "\<And>B. B \<in> S \<Longrightarrow> paper_R_valid B"
  shows "paper_R_valid A"
  using derivation premises_valid
proof (induction rule: paper_R_named_derivable.induct)
  case (Assumption A S)
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case (Theorem A S)
  show ?case by (rule paper_R_named_H_soundness[OF Theorem.hyps])
next
  case (MP S A B)
  have av: "paper_R_valid A" by (rule MP.IH(1)[OF MP.prems])
  have implication: "paper_R_valid (named_paper_imp stock A B)"
    by (rule MP.IH(2)[OF MP.prems])
  have al: "paper_R_in_language signature stock A Prop"
    by (rule paper_R_named_derivable_language[OF MP.hyps(1)])
  show ?case by (rule paper_R_valid_MP[OF al MP.hyps(3) av implication])
qed

end

end
