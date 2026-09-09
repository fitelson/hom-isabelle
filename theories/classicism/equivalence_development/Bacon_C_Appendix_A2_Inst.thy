theory Bacon_C_Appendix_A2_Inst
  imports Bacon_C_Exists_Distribution_Vector Bacon_C_Vector_Implication_Context
begin

section \<open>Appendix A.2: the Inst induction step\<close>

text \<open>
  Suppose ⊢C (λv̄λx:σ.A → B) = (λv̄λx:σ.⊤₀), with x not free in B.
  Boolean replacement yields (λv̄λx.B ∧ A) = (λv̄λx.A).  Quantifying
  this supplied identity and using Distribution-∧∃ gives
  (λv̄.B ∧ ∃x.A) = (λv̄.∃x.A).  In the antecedent of · → B, the
  left expression gives a PC tautology.  Thus
  ⊢C (λv̄.∃x.A → B) = (λv̄.⊤₀).
  Source: Bacon--Dorr Figure 2 Inst, p.8; Figure 4, p.13; A.2, pp.65–67.

  Isabelle representation.  The fresh inner occurrence of B is shift B.
  Source typing premises are explicit, and induction_hypothesis is exactly
  the vector truth identity for the Inst premise.
  Status.  No arbitrary open C equation is abstracted.  This proof needs
  neither an existential truth/falsity assumption nor C Equivalence.
\<close>

lemma C_vector_imp_truth_absorption:
  assumes A: "\<Delta> @ \<Gamma> \<turnstile> A : Prop" and B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop"
    and implication_truth: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
      (C_abstract_prefix \<Delta> (Imp A B)) (C_abstract_prefix \<Delta> ObjTrue)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj B A)) (C_abstract_prefix \<Delta> A)"
proof -
  have implication_type: "\<Delta> @ \<Gamma> \<turnstile> Imp A B : Prop" by (rule has_type.Imp[OF A B])
  have left_normal: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj (Imp A B) A)) (C_abstract_prefix \<Delta> A)"
    by (rule C_A1_trans[OF C_vector_conj_congruence_left[OF implication_type typed_ObjTrue A implication_truth]
      C_vector_conj_true_left[OF A]])
  have PC: "prop_tautology (\<Delta> @ \<Gamma>) (Conj (Imp A B) A \<longleftrightarrow>\<^sub>o Conj B A)"
    unfolding prop_tautology_def using A B implication_type by auto
  have boolean: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj (Imp A B) A)) (C_abstract_prefix \<Delta> (Conj B A))"
    by (rule C_PC_boolean_equivalence_vector_abstraction[OF PC])
  show ?thesis by (rule C_A1_trans[OF C_A1_sym[OF boolean] left_normal])
qed

theorem C_A2_Inst_vector:
  assumes A: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> A : Prop"
    and B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop"
    and induction_hypothesis: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev (\<sigma> # \<Delta>)) Prop)
      (C_abstract_prefix (\<sigma> # \<Delta>) (Imp A (shift B)))
      (C_abstract_prefix (\<sigma> # \<Delta>) ObjTrue)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (Exists \<sigma> A) B)) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  have A_extended: "(\<sigma> # \<Delta>) @ \<Gamma> \<turnstile> A : Prop" using A by simp
  have B_shifted: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> shift B : Prop" by (rule weakening_front[OF B])
  have B_extended: "(\<sigma> # \<Delta>) @ \<Gamma> \<turnstile> shift B : Prop" using B_shifted by simp
  have inner_absorption: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev (\<sigma> # \<Delta>)) Prop)
    (C_abstract_prefix (\<sigma> # \<Delta>) (Conj (shift B) A))
    (C_abstract_prefix (\<sigma> # \<Delta>) A)"
    by (rule C_vector_imp_truth_absorption[OF A_extended B_extended induction_hypothesis])
  have quantified: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Exists \<sigma> (Conj (shift B) A)))
    (C_abstract_prefix \<Delta> (Exists \<sigma> A))"
    by (rule C_vector_Exists_congruence[OF inner_absorption])
  have outer_absorption: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj B (Exists \<sigma> A)))
    (C_abstract_prefix \<Delta> (Exists \<sigma> A))"
    by (rule C_A1_trans[OF C_vector_Exists_distribution[OF A B] quantified])
  have exists_type: "\<Delta> @ \<Gamma> \<turnstile> Exists \<sigma> A : Prop" by (rule has_type.Exists[OF A])
  have conjunction_type: "\<Delta> @ \<Gamma> \<turnstile> Conj B (Exists \<sigma> A) : Prop"
    by (rule has_type.Conj[OF B exists_type])
  have implication_context: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (Conj B (Exists \<sigma> A)) B))
    (C_abstract_prefix \<Delta> (Imp (Exists \<sigma> A) B))"
    by (rule C_vector_imp_congruence_left[OF conjunction_type exists_type B outer_absorption])
  have formula_type: "\<Delta> @ \<Gamma> \<turnstile> Imp (Conj B (Exists \<sigma> A)) B : Prop"
    by (rule has_type.Imp[OF conjunction_type B])
  have PC: "prop_tautology (\<Delta> @ \<Gamma>) (Imp (Conj B (Exists \<sigma> A)) B)"
    unfolding prop_tautology_def by (rule conjI[OF formula_type]) simp
  show ?thesis by (rule C_A1_trans[OF C_A1_sym[OF implication_context] C_PC_vector_abstraction[OF PC]])
qed

end
