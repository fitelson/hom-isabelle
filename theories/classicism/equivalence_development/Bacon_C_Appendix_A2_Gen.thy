theory Bacon_C_Appendix_A2_Gen
  imports Bacon_C_Forall_Distribution_Vector
begin

section \<open>The Gen rule preserves truth beneath arbitrary vectors\<close>

text \<open>
  From ⊢C (λv̄λx:σ.(A → B)) = (λv̄λx:σ.⊤₀), with x not
  free in A, derive ⊢C (λv̄.(A → ∀x:σ.B)) = (λv̄.⊤₀).
  Sources: Bacon–Dorr Figure 2 Gen, p.8; Figure 4 Distribution-∨∀,
  p.13; Appendix A.1–A.2, pp.65–66.

  Isabelle representation.  The premise writes shift A explicitly under
  x.  Quantifier congruence first gives ∀x.(A → B) = ∀x.⊤₀ beneath
  the vector; A.1 normalizes the latter.  Material implication and the
  source distribution identity identify ∀x.(A → B) with A → ∀x.B.
  Each replacement uses a supplied ambient operation identity, never an
  abstraction rule for arbitrary open C equations.

  Status.  The final theorem has only its displayed vector-truth premise.
  Typing, including the unshifted antecedent, is recovered syntactically.
  There is no CE/CEV, general C Equivalence, or semantic assumption.
\<close>

lemma C_shift_type_reflection:
  assumes shifted: "\<sigma> # \<Gamma> \<turnstile> shift A : \<tau>"
  shows "\<Gamma> \<turnstile> A : \<tau>"
proof -
  have argument: "\<Gamma> \<turnstile> Const '''' \<sigma> : \<sigma>" by (rule has_type.Const)
  have restored: "\<Gamma> \<turnstile> subst0 (Const '''' \<sigma>) (shift A) : \<tau>"
    by (rule subst0_preserves_typing[OF shifted argument])
  show ?thesis using restored by (simp only: subst0_shift)
qed

text \<open>
  The constant in the preceding helper is used only in a syntax-typing
  argument: substituting any term in the unused slot leaves A unchanged.
  It supplies no new logical premise or semantic inhabitance assumption.
\<close>

lemma C_vector_material_implication:
  assumes A: "\<Delta> @ \<Gamma> \<turnstile> A : Prop" and B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp A B)) (C_abstract_prefix \<Delta> (Disj (Neg A) B))"
proof -
  have boolean: "prop_tautology (\<Delta> @ \<Gamma>) (Imp A B \<longleftrightarrow>\<^sub>o Disj (Neg A) B)"
    unfolding prop_tautology_def using A B by auto
  show ?thesis by (rule C_PC_boolean_equivalence_vector_abstraction[OF boolean])
qed

theorem C_A2_Gen_vector:
  assumes premise_identity: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev (\<sigma> # \<Delta>)) Prop)
    (C_abstract_prefix (\<sigma> # \<Delta>) (Imp (shift A) B))
    (C_abstract_prefix (\<sigma> # \<Delta>) ObjTrue)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp A (Forall \<sigma> B))) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  have I: "(\<sigma> # \<Delta>) @ \<Gamma> \<turnstile> Imp (shift A) B : Prop"
    by (rule C_vector_truth_identity_body_type[OF premise_identity])
  have shifted_A: "(\<sigma> # \<Delta>) @ \<Gamma> \<turnstile> shift A : Prop"
    and B: "(\<sigma> # \<Delta>) @ \<Gamma> \<turnstile> B : Prop"
    using I by (auto elim: has_type.cases)
  have shifted_A': "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> shift A : Prop" using shifted_A by simp
  have B_body: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> B : Prop" using B by simp
  have A: "\<Delta> @ \<Gamma> \<turnstile> A : Prop" by (rule C_shift_type_reflection[OF shifted_A'])
  have NA: "\<Delta> @ \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have QB: "\<Delta> @ \<Gamma> \<turnstile> Forall \<sigma> B : Prop" by (rule has_type.Forall[OF B_body])
  have quantified_truth: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Forall \<sigma> (Imp (shift A) B))) (C_abstract_prefix \<Delta> ObjTrue)"
    by (rule C_A1_trans[OF C_vector_Forall_congruence[OF premise_identity] C_vector_forall_truth])
  have material: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev (\<sigma> # \<Delta>)) Prop)
    (C_abstract_prefix (\<sigma> # \<Delta>) (Imp (shift A) B))
    (C_abstract_prefix (\<sigma> # \<Delta>) (Disj (Neg (shift A)) B))"
    by (rule C_vector_material_implication[OF shifted_A B])
  have quantified_material: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Forall \<sigma> (Imp (shift A) B)))
    (C_abstract_prefix \<Delta> (Forall \<sigma> (Disj (shift (Neg A)) B)))"
    using C_vector_Forall_congruence[OF material] by (simp only: shift_def rename.simps)
  have distribution: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Disj (Neg A) (Forall \<sigma> B)))
    (C_abstract_prefix \<Delta> (Forall \<sigma> (Disj (shift (Neg A)) B)))"
    by (rule C_vector_disj_forall_distribution[OF NA B_body])
  show ?thesis by (rule C_A1_trans[OF C_vector_material_implication[OF A QB]
    C_A1_trans[OF distribution C_A1_trans[OF C_A1_sym[OF quantified_material] quantified_truth]]])
qed

end
