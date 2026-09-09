theory Bacon_C_Equivalence_From_Vector_Truth
  imports Bacon_C_Appendix_A2_Inst
begin

section \<open>From a biconditional's vector truth identity to Equivalence\<close>

text \<open>
  If (λv̄.A ↔ B) = (λv̄.⊤), then (λv̄.A) = (λv̄.B).
  This is the final algebraic implication used in Bacon–Dorr A.3,
  following the vector truth theorem A.2 (Appendix A, pp.65–67).

  Isabelle representation: PC and the checked vector MP step extract
  the two implication identities. Their conjunction-absorption consequences,
  together with commutativity, identify the two abstractions. All formulas
  may depend on every variable of the mixed-type vector.

  Status: the vector truth identity is an explicit premise. This leaf does
  not yet infer it from a bare C theorem A ↔ B. No Equivalence constructor
  from either stronger presentation is used in the proof.
\<close>

theorem C_vector_biconditional_truth_identity:
  assumes truth: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (A \<longleftrightarrow>\<^sub>o B))
    (C_abstract_prefix \<Delta> ObjTrue)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> B)"
proof -
  have iff_type: "\<Delta> @ \<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    by (rule C_vector_truth_identity_body_type[OF truth])
  have A: "\<Delta> @ \<Gamma> \<turnstile> A : Prop" and B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop"
    using iff_type by (auto elim: has_type.cases)
  have forward_pc: "prop_tautology (\<Delta> @ \<Gamma>)
    (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp A B))"
    unfolding prop_tautology_def using A B by auto
  have reverse_pc: "prop_tautology (\<Delta> @ \<Gamma>)
    (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp B A))"
    unfolding prop_tautology_def using A B by auto
  have forward: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp A B)) (C_abstract_prefix \<Delta> ObjTrue)"
    by (rule C_A2_MP_vector[OF truth C_PC_vector_abstraction[OF forward_pc]])
  have reverse: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp B A)) (C_abstract_prefix \<Delta> ObjTrue)"
    by (rule C_A2_MP_vector[OF truth C_PC_vector_abstraction[OF reverse_pc]])
  have absorbs_A: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj B A)) (C_abstract_prefix \<Delta> A)"
    by (rule C_vector_imp_truth_absorption[OF A B forward])
  have absorbs_B: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj A B)) (C_abstract_prefix \<Delta> B)"
    by (rule C_vector_imp_truth_absorption[OF B A reverse])
  have comm_pc: "prop_tautology (\<Delta> @ \<Gamma>)
    (Conj B A \<longleftrightarrow>\<^sub>o Conj A B)"
    unfolding prop_tautology_def using A B by auto
  have comm: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj B A)) (C_abstract_prefix \<Delta> (Conj A B))"
    by (rule C_PC_boolean_equivalence_vector_abstraction[OF comm_pc])
  show ?thesis by (rule C_A1_transport[OF comm absorbs_A absorbs_B])
qed

end
