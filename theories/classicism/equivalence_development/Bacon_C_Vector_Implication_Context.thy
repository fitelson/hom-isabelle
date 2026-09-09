theory Bacon_C_Vector_Implication_Context
  imports Bacon_C_Vector_Quantifier_Congruence
begin

section \<open>Replacing a vector identity in an implication antecedent\<close>

text \<open>
  From ⊢C (λv̄.A) = (λv̄.A′), derive
  ⊢C (λv̄.A → B) = (λv̄.A′ → B).
  Source role: typed Leibniz replacement in the Inst case of
  Bacon--Dorr Appendix A.2, pp.65–67.
  Isabelle representation.  The supplied vector operation is evaluated
  at the reversed fresh-variable list inside an implication context;
  explicit β deabstraction restores the original bodies.
  Status.  This replaces a proved operation identity, not an open equation.
\<close>

lemma C_vector_imp_evaluation_subst:
  "subst (C_vector_lift_subst n (case_nat F Var))
    (Imp (app_vec (Var n) (rev (fresh_vars n))) (rename (C_vector_lift_ren n Suc) B)) =
    Imp (app_vec (C_vector_raise n F) (rev (fresh_vars n))) B"
  by (simp only: subst.simps C_vector_evaluation_subst C_vector_remove_inserted_parameter)

lemma C_vector_imp_congruence_left:
  assumes A: "\<Delta> @ \<Gamma> \<turnstile> A : Prop" and A': "\<Delta> @ \<Gamma> \<turnstile> A' : Prop"
    and B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
      (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> A')"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp A B)) (C_abstract_prefix \<Delta> (Imp A' B))"
proof -
  let ?n = "length \<Delta>"
  let ?\<nu> = "arrow_type (rev \<Delta>) Prop"
  let ?F = "C_abstract_prefix \<Delta> A"
  let ?G = "C_abstract_prefix \<Delta> A'"
  let ?eval = "app_vec (Var ?n) (rev (fresh_vars ?n))"
  let ?body = "Imp ?eval (rename (C_vector_lift_ren ?n Suc) B)"
  have F: "\<Gamma> \<turnstile> ?F : ?\<nu>" by (rule C_abstract_prefix_type[OF A])
  have G: "\<Gamma> \<turnstile> ?G : ?\<nu>" by (rule C_abstract_prefix_type[OF A'])
  have eval_type: "\<Delta> @ (?\<nu> # \<Gamma>) \<turnstile> ?eval : Prop"
    by (rule C_vector_evaluation_slot_type)
  have inserted_B: "\<Delta> @ (?\<nu> # \<Gamma>) \<turnstile> rename (C_vector_lift_ren ?n Suc) B : Prop"
    by (rule C_vector_insert_parameter_type[OF B])
  have body_type: "\<Delta> @ (?\<nu> # \<Gamma>) \<turnstile> ?body : Prop"
    by (rule has_type.Imp[OF eval_type inserted_B])
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (app_vec (C_vector_raise ?n ?F) (rev (fresh_vars ?n))) B))
    (C_abstract_prefix \<Delta> (Imp (app_vec (C_vector_raise ?n ?G) (rev (fresh_vars ?n))) B))"
    using C_vector_identity_context[OF F G body_type identity]
    by (simp only: C_vector_imp_evaluation_subst)
  have left: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (Imp (app_vec (C_vector_raise ?n ?F) (rev (fresh_vars ?n))) B) (Imp A B)"
    by (rule C_PC_beta_eta_Imp[OF C_vector_deabstract_beta_eta[OF A] beta_eta_equiv.Refl[OF B]])
  have right: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (Imp (app_vec (C_vector_raise ?n ?G) (rev (fresh_vars ?n))) B) (Imp A' B)"
    by (rule C_PC_beta_eta_Imp[OF C_vector_deabstract_beta_eta[OF A'] beta_eta_equiv.Refl[OF B]])
  show ?thesis by (rule C_A1_transport[OF raw C_vector_conversion_identity[OF left]
    C_vector_conversion_identity[OF right]])
qed

end
