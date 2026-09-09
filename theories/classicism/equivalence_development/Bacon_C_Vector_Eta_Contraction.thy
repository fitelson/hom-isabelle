theory Bacon_C_Vector_Eta_Contraction
  imports Bacon_C_Vector_Beta_Evaluation
begin

section \<open>Typed vector η contraction in source argument order\<close>

text \<open>
  If F : σ₁ → ⋯ → σₙ → τ, then λv₁:σ₁.…λvₙ:σₙ.F v₁ … vₙ ≡η F.
  Source role: η conversion from Bacon--Dorr Figure 2, p.8, used when
  passing between abstraction vectors and their operations in Appendix A.

  Isabelle representation.  Δ lists innermost-to-outermost context slots;
  the function type is arrow_type (rev Δ) τ, and the application arguments
  are rev (fresh_vars (length Δ)).  The proof removes the innermost binder
  first and then applies the induction hypothesis to the remaining vector.
  Status.  This is typed syntactic βη equivalence, proved using η only.
  It is valid for mixed types and the empty vector, without CE/CEV.
\<close>

lemma C_eta_app_vec_append:
  "app_vec F (xs @ ys) = app_vec (app_vec F xs) ys"
  by (induction xs arbitrary: F) simp_all

lemma C_eta_shift_app_vec:
  "shift (app_vec F xs) = app_vec (shift F) (map shift xs)"
  by (induction xs arbitrary: F) (simp_all add: shift_def)

lemma C_vector_reverse_fresh_vars_shift:
  "rev (fresh_vars (Suc n)) = map shift (rev (fresh_vars n)) @ [Var 0]"
proof (induction n)
  case 0
  show ?case by (simp add: fresh_vars_def)
next
  case (Suc n)
  have left: "rev (fresh_vars (Suc (Suc n))) =
    Var (Suc n) # (map shift (rev (fresh_vars n)) @ [Var 0])"
    using C_vector_reverse_fresh_vars_Suc[of "Suc n"] by (simp only: Suc.IH)
  have right: "map shift (rev (fresh_vars (Suc n))) @ [Var 0] =
    Var (Suc n) # (map shift (rev (fresh_vars n)) @ [Var 0])"
    by (simp only: C_vector_reverse_fresh_vars_Suc list.map shift_def rename.simps append_Cons append_Nil)
  show ?case by (rule trans[OF left sym[OF right]])
qed

lemma C_eta_vector_application_Suc:
  "app_vec (C_vector_raise (Suc n) F) (rev (fresh_vars (Suc n))) =
    App (shift (app_vec (C_vector_raise n F) (rev (fresh_vars n)))) (Var 0)"
proof -
  have raised: "C_vector_raise (Suc n) F = shift (C_vector_raise n F)"
    by (simp add: shift_def)
  show ?thesis by (simp only: C_vector_reverse_fresh_vars_shift C_eta_app_vec_append
    app_vec.simps raised C_eta_shift_app_vec)
qed

lemma C_eta_vector_innermost_step:
  "compatible_step eta_contract
    (Lam \<sigma> (app_vec (C_vector_raise (Suc n) F) (rev (fresh_vars (Suc n)))))
    (app_vec (C_vector_raise n F) (rev (fresh_vars n)))"
proof -
  have "compatible_step eta_contract
    (Lam \<sigma> (App (shift (app_vec (C_vector_raise n F) (rev (fresh_vars n)))) (Var 0)))
    (app_vec (C_vector_raise n F) (rev (fresh_vars n)))"
    by (rule compatible_step.root[where R=eta_contract]) (rule eta_contract.eta)
  then show ?thesis by (simp only: C_eta_vector_application_Suc)
qed

theorem C_vector_eta_beta_eta:
  assumes F: "\<Gamma> \<turnstile> F : arrow_type (rev \<Delta>) \<tau>"
  shows "beta_eta_equiv \<Gamma> (arrow_type (rev \<Delta>) \<tau>)
    (C_abstract_prefix \<Delta>
      (app_vec (C_vector_raise (length \<Delta>) F) (rev (fresh_vars (length \<Delta>))))) F"
  using F
proof (induction \<Delta> arbitrary: \<tau>)
  case Nil
  have F: "\<Gamma> \<turnstile> F : \<tau>" using Nil.prems by simp
  show ?case using beta_eta_equiv.Refl[OF F] by (simp add: fresh_vars_def)
next
  case (Cons \<sigma> \<Delta>)
  let ?n = "length \<Delta>"
  let ?partial = "app_vec (C_vector_raise ?n F) (rev (fresh_vars ?n))"
  let ?full = "app_vec (C_vector_raise (Suc ?n) F) (rev (fresh_vars (Suc ?n)))"
  have F_type: "\<Gamma> \<turnstile> F : arrow_type (rev \<Delta>) (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    using Cons.prems by (simp add: C_arrow_type_append)
  have raised_type: "\<Delta> @ \<Gamma> \<turnstile> C_vector_raise ?n F : arrow_type (rev \<Delta>) (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    by (rule C_vector_raise_type[OF F_type])
  have partial_type: "\<Delta> @ \<Gamma> \<turnstile> ?partial : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    by (rule typed_app_vec[OF raised_type C_vector_reverse_fresh_vars_type])
  have shifted_type: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> shift ?partial : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    by (rule weakening_front[OF partial_type])
  have variable: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  have full_type: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> ?full : \<tau>"
    using has_type.App[OF shifted_type variable] by (simp only: C_eta_vector_application_Suc)
  have lambda_type: "\<Delta> @ \<Gamma> \<turnstile> Lam \<sigma> ?full : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    by (rule has_type.Lam[OF full_type])
  have innermost: "beta_eta_equiv (\<Delta> @ \<Gamma>) (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Lam \<sigma> ?full) ?partial"
    by (rule beta_eta_equiv.Eta[OF lambda_type partial_type C_eta_vector_innermost_step])
  have prefix: "beta_eta_equiv \<Gamma> (arrow_type (rev \<Delta>) (\<sigma> \<rightarrow>\<^sub>o \<tau>))
    (C_abstract_prefix \<Delta> (Lam \<sigma> ?full)) (C_abstract_prefix \<Delta> ?partial)"
    by (rule C_beta_eta_abstract_prefix[OF innermost])
  have tail: "beta_eta_equiv \<Gamma> (arrow_type (rev \<Delta>) (\<sigma> \<rightarrow>\<^sub>o \<tau>))
    (C_abstract_prefix \<Delta> ?partial) F"
    by (rule Cons.IH[OF F_type])
  show ?case using beta_eta_equiv.Trans[OF prefix tail]
    by (simp add: C_abstract_prefix_cons C_arrow_type_append)
qed

corollary C_vector_eta_identity:
  assumes F: "\<Gamma> \<turnstile> F : arrow_type (rev \<Delta>) \<tau>"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) \<tau>)
    (C_abstract_prefix \<Delta>
      (app_vec (C_vector_raise (length \<Delta>) F) (rev (fresh_vars (length \<Delta>))))) F"
  by (rule C_closure_beta_eta_identity[OF C_vector_eta_beta_eta[OF F]])

text \<open>
  This theorem must not be applied directly to the older zeta_body σs,
  which uses ascending fresh_vars in the σs context and expects the
  arrow order σs.  C_abstract_prefix σs reverses the binder order.
  For example, Δ = [τ,σ] abstracts λx:σ.λy:τ and therefore applies a
  σ → τ → ρ operation to slots [1,0], not [0,1].  Connecting the
  older ζ interface to this η theorem requires an explicit typed
  permutation of variables and argument order.
\<close>

end
