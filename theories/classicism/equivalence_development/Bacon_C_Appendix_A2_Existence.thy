theory Bacon_C_Appendix_A2_Existence
  imports Bacon_C_Appendix_A2_LL
begin

section \<open>Existential reflexivity and the target existence constructor\<close>

text \<open>
  For each type σ, a typed constant c supplies c =σ c.  The proved
  vector Ref and EG cases, followed by vector MP, yield
  ⊢C (λv̄.∃x:σ.x =σ x) = (λv̄.⊤₀).
  Source role: the existence case in Bacon--Dorr Appendix A.2; the target
  H_proves presentation has an explicit IndividualExistence constructor.

  Isabelle representation.  The auxiliary Const term is permitted by
  the unrestricted typed-string syntax and disappears from the conclusion.
  Status.  This is a C vector-truth theorem.  It is distinct from the
  repository's exact ten-rule source derivation of Existence and makes
  no claim about an arbitrary restricted constant signature.
\<close>

theorem C_A2_type_existence_vector_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Exists \<sigma> (Eq \<sigma> (Var 0) (Var 0))))
    (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  let ?c = "Const ''A2-existence-witness'' \<sigma>"
  have witness_type: "\<Delta> @ \<Gamma> \<turnstile> ?c : \<sigma>" by (rule has_type.Const)
  have body_type: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> Eq \<sigma> (Var 0) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have reflexivity: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Eq \<sigma> ?c ?c)) (C_abstract_prefix \<Delta> ObjTrue)"
    by (rule C_A2_Ref_vector_truth[OF witness_type])
  have generalization: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (Eq \<sigma> ?c ?c) (Exists \<sigma> (Eq \<sigma> (Var 0) (Var 0)))))
    (C_abstract_prefix \<Delta> ObjTrue)"
    using C_A2_EG_vector_truth[OF body_type witness_type] by (simp add: subst0_def)
  show ?thesis by (rule C_A2_MP_vector[OF reflexivity generalization])
qed

corollary C_A2_individual_existence_vector_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Exists Ind (Eq Ind (Var 0) (Var 0))))
    (C_abstract_prefix \<Delta> ObjTrue)"
  by (rule C_A2_type_existence_vector_truth)

end
