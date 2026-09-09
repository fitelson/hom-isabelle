theory Bacon_H_Only_To_Classicism
  imports Bacon_H_Only_Classicism_Development.Bacon_H_Equivalence_Syntax_Bridge
    Bacon_C_Equivalence_Development.Bacon_C_Rule_Equivalence
begin

section \<open>H-only Equivalence presentations are contained in axiom-based C\<close>

text \<open>
  Every theorem of H closed under the Rule of Equivalence is a theorem
  of axiom-based C.  Source: the inclusion (1) ⊆ (3) of Bacon,
  Theorem 6.1, pp.126–127, established by C's independent closure under
  Equivalence; compare Bacon–Dorr Appendix A, pp.65–67.

  Isabelle representation.  The induction starts from HE_proves, whose
  only base-theorem constructor imports H, not C.  Its recursive
  Equivalence case first translates the premise into C and then uses
  C_rule_equivalence.  The checked syntax bridge preserves the reversed
  de Bruijn argument order, the arrow type, and the raising operation.

  Scope.  This is a one-way represented-calculus inclusion for full F
  types and unrestricted string constants, with the documented primitive
  connective and H-presentation qualifications.  The converse requires
  independent H proofs certifying every added Classical/Boolean identity
  as a Logical Equivalence instance; it is not inferred here from the
  earlier C = CE = CEV results.  No semantic claim is made.
\<close>

theorem HE_proves_to_C:
  assumes derivation: "HE_proves \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>C A"
  using derivation
proof (induction rule: HE_proves.induct)
  case (H \<Gamma> A)
  show ?case by (rule C_proves.H[OF H.hyps])
next
  case (Equivalence \<Gamma> F \<Delta> G)
  have F: "\<Gamma> \<turnstile> F : arrow_type (rev \<Delta>) Prop"
    using Equivalence.hyps(1) by (simp only: H_rule_arrow_bridge)
  have G: "\<Gamma> \<turnstile> G : arrow_type (rev \<Delta>) Prop"
    using Equivalence.hyps(2) by (simp only: H_rule_arrow_bridge)
  have premise_C: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>C
    (app_vec (C_vector_raise (length \<Delta>) F) (rev (fresh_vars (length \<Delta>)))
      \<longleftrightarrow>\<^sub>o
     app_vec (C_vector_raise (length \<Delta>) G) (rev (fresh_vars (length \<Delta>))))"
    using Equivalence.IH by (simp only: H_rule_body_bridge)
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop) F G"
    by (rule C_rule_equivalence[OF F G premise_C])
  show ?case using identity by (simp only: H_rule_arrow_bridge)
next
  case (MP \<Gamma> A B)
  show ?case by (rule C_proves.MP[OF MP.IH])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case by (rule C_proves.Gen[OF Gen.hyps(1,2) Gen.IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case by (rule C_proves.Inst[OF Inst.hyps(1,2) Inst.IH])
qed

corollary HLE_proves_to_C:
  "HLE_proves \<Gamma> A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>C A"
  by (rule HE_proves_to_C, rule HLE_proves_to_HE, assumption)

end
