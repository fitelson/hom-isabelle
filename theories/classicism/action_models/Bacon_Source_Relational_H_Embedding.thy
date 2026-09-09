theory Bacon_Source_Relational_H_Embedding
  imports Bacon_Source_Relational_H
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_H
begin

section \<open>Every R proof is an F proof at the unchanged signature\<close>

text \<open>
  R⊆F, and each of Figure 2's ten rules has the same syntactic
  form in the larger grammar. Thus ⊢Hᴿ A implies ⊢Hᶠ A.
  Source: Bacon–Dorr §1.1, p.5, and Figure 2, p.8.

  This proof translates the independent R constructors one by one.
  The terms, signature, variable stock and literal substitution steps
  are unchanged. Only the language guards are embedded into F.
  No full-stock richness premise is needed for this implication.
  The converse is not established: an F derivation may use non-R
  intermediate formulas. F soundness therefore supplies no soundness
  theorem for arbitrary independently specified R models here.
\<close>

lemma paper_R_named_PC_embedding:
  assumes pc: "paper_R_named_PC \<Sigma> G A"
  shows "named_PC \<Sigma> G A"
proof -
  have language: "named_in_language paper_logical_type \<Sigma> G A Prop"
    by (rule paper_R_language_embedding[OF paper_R_named_PC_language[OF pc]])
  have instance_form: "\<exists>P :: nat sprop_template. \<exists>v.
      sprop_tautology P \<and> A = named_paper_prop_instance G v P"
    using pc unfolding paper_R_named_PC_def by (rule conjunct2)
  show ?thesis unfolding named_PC_def by (rule conjI[OF language instance_form])
qed

theorem paper_R_named_H_embedding:
  assumes derivation: "paper_R_named_H \<Sigma> G A"
  shows "paper_named_H \<Sigma> G A"
  using derivation
proof (induction rule: paper_R_named_H.induct)
  case PC
  show ?case by (rule paper_named_H.PC[OF paper_R_named_PC_embedding[OF PC.hyps]])
next
  case UI
  show ?case by (rule paper_named_H.UI[OF paper_R_language_embedding[OF UI.hyps]])
next
  case EG
  show ?case by (rule paper_named_H.EG[OF paper_R_language_embedding[OF EG.hyps]])
next
  case Ref
  show ?case by (rule paper_named_H.Ref[OF paper_R_language_embedding[OF Ref.hyps]])
next
  case LL
  show ?case by (rule paper_named_H.LL[OF paper_R_language_embedding[OF LL.hyps]])
next
  case Beta
  show ?case by (rule paper_named_H.Beta[OF paper_R_language_embedding[OF Beta.hyps(1)]
    paper_R_language_embedding[OF Beta.hyps(2)] Beta.hyps(3) paper_R_language_embedding[OF Beta.hyps(4)]])
next
  case Eta
  show ?case by (rule paper_named_H.Eta[OF paper_R_language_embedding[OF Eta.hyps(1)]
    paper_R_language_embedding[OF Eta.hyps(2)] Eta.hyps(3) paper_R_language_embedding[OF Eta.hyps(4)]])
next
  case MP
  show ?case by (rule paper_named_H.MP[OF MP.IH paper_R_language_embedding[OF MP.hyps(3)]])
next
  case Gen
  show ?case by (rule paper_named_H.Gen[OF Gen.IH Gen.hyps(2,3) paper_R_language_embedding[OF Gen.hyps(4)]])
next
  case Inst
  show ?case by (rule paper_named_H.Inst[OF Inst.IH Inst.hyps(2,3) paper_R_language_embedding[OF Inst.hyps(4)]])
qed

end
