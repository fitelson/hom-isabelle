theory Bacon_Source_Relational_Universal_Closure_Validity
  imports Bacon_Source_Relational_H_Theory_Sentence_Fragment
    Bacon_Source_Relational_H_Soundness
begin

section \<open>Recovering an H-theory from the validity of its sentences\<close>

text \<open>
  In a supplied independent R BBK model, validity of ∀n⃗.P implies
  validity of P. The native H theorem (∀n⃗.P)→P and native H
  soundness give the implication; validity-level MP handles typed
  adequate partial assignments. No assignment is silently assumed
  adequate for every open formula.

  Consequently, a model of the closed fragment of an H-theory is a
  model of the whole theory. This is the recovery step for the
  sentence-set formulation of Theorem 3.2 and the theories in n.73,
  not a model-existence assertion for arbitrary open premise sets.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_valid_all_vec_instance:
  assumes language: "paper_R_in_language signature stock P Prop"
    and binders: "list_all paper_R_type (map stock ns)"
    and universal: "paper_R_valid (paper_R_all_vec stock ns P)"
  shows "paper_R_valid P"
proof -
  have closure_language: "paper_R_in_language signature stock
      (paper_R_all_vec stock ns P) Prop"
    by (rule paper_R_all_vec_language[OF language binders])
  have implication: "paper_R_valid
      (named_paper_imp stock (paper_R_all_vec stock ns P) P)"
    by (rule paper_R_named_H_soundness[
      OF paper_R_named_H_all_vec_instance[OF stock_rich language binders]])
  show ?thesis
    by (rule paper_R_valid_MP[OF closure_language language universal implication])
qed

theorem paper_R_H_theory_valid_from_sentence_fragment:
  assumes theory_h: "paper_R_H_theory signature stock T"
    and sentences: "\<And>A. A \<in> paper_R_sentence_fragment signature stock T
      \<Longrightarrow> paper_R_valid A"
    and member: "P \<in> T"
  shows "paper_R_valid P"
proof -
  have language: "paper_R_in_language signature stock P Prop"
    by (rule paper_R_H_theory_language[OF theory_h member])
  obtain ns where binders: "list_all paper_R_type (map stock ns)"
    and included: "paper_R_all_vec stock ns P \<in>
      paper_R_sentence_fragment signature stock T"
    using paper_R_H_theory_fragment_universal[OF stock_rich theory_h member]
    by blast
  have universal: "paper_R_valid (paper_R_all_vec stock ns P)"
    by (rule sentences[OF included])
  show ?thesis
    by (rule paper_R_valid_all_vec_instance[OF language binders universal])
qed

end

end
