theory Bacon_C_Appendix_A2_Ambient_Identity
  imports Bacon_C_Appendix_A2_Ref_Vector Bacon_C_Vector_Contexts
begin

section \<open>Ambient identities yield truth identities for raised equations\<close>

text \<open>
  From ⊢C F =τ G in Γ, derive
  ⊢C (λv̄.(F =τ G)) = (λv̄.⊤₀), where the displayed occurrences
  of F and G are raised beneath v̄.  Source role: the closed identity-axiom
  cases of Bacon–Dorr Appendix A.2(i), p.65, using Ref and LL.

  Isabelle representation.  Insert the ambient operation slot into
  Eq τ (Var |Δ|) (inserted raiseΔG).  Replacing F by G gives the
  reflexive equation on raiseΔG.  The checked full-vector Ref theorem
  identifies the abstraction of that reflexive equation with truth.

  Status.  The input identity is in Γ, not in the enlarged context Δ,Γ.
  The raises are essential: this theorem is not a rule abstracting an
  arbitrary equation whose terms depend on the newly bound variables.
  No CE/CEV, C Equivalence, or semantic premise is used.
\<close>

theorem C_A2_ambient_identity_vector_truth:
  assumes F: "\<Gamma> \<turnstile> F : \<tau>" and G: "\<Gamma> \<turnstile> G : \<tau>"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> F G"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Eq \<tau> (C_vector_raise (length \<Delta>) F) (C_vector_raise (length \<Delta>) G)))
    (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  let ?n = "length \<Delta>"
  let ?R = "C_vector_raise ?n G"
  let ?r = "C_vector_lift_ren ?n Suc"
  let ?M = "Eq \<tau> (Var ?n) (rename ?r ?R)"
  have raised_G: "\<Delta> @ \<Gamma> \<turnstile> ?R : \<tau>" by (rule C_vector_raise_type[OF G])
  have inserted_G: "\<Delta> @ (\<tau> # \<Gamma>) \<turnstile> rename ?r ?R : \<tau>"
    by (rule C_vector_insert_parameter_type[OF raised_G])
  have zero: "lookup (\<tau> # \<Gamma>) 0 = Some \<tau>" by simp
  have index: "lookup (\<Delta> @ (\<tau> # \<Gamma>)) ?n = Some \<tau>"
    using lookup_append_shift[OF zero, where \<Delta>=\<Delta>] by simp
  have variable: "\<Delta> @ (\<tau> # \<Gamma>) \<turnstile> Var ?n : \<tau>" by (rule has_type.Var[OF index])
  have body: "\<Delta> @ (\<tau> # \<Gamma>) \<turnstile> ?M : Prop" by (rule has_type.Eq[OF variable inserted_G])
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Eq \<tau> (C_vector_raise ?n F) ?R))
    (C_abstract_prefix \<Delta> (Eq \<tau> ?R ?R))"
    using C_vector_identity_context[OF F G body identity]
    by (simp only: subst.simps C_vector_lift_subst_slot C_vector_remove_inserted_parameter)
  show ?thesis by (rule C_A1_trans[OF replacement C_A2_Ref_vector_truth[OF raised_G]])
qed

lemma C_vector_raise_Eq:
  "C_vector_raise n (Eq \<tau> F G) = Eq \<tau> (C_vector_raise n F) (C_vector_raise n G)"
  by (induction n) simp_all

corollary C_A2_ambient_identity_formula_vector_truth:
  assumes identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> F G"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (C_vector_raise (length \<Delta>) (Eq \<tau> F G)))
    (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  have formula: "\<Gamma> \<turnstile> Eq \<tau> F G : Prop" by (rule C_proves_formula[OF identity])
  have F: "\<Gamma> \<turnstile> F : \<tau>" and G: "\<Gamma> \<turnstile> G : \<tau>"
    using formula by (auto elim: has_type.cases)
  show ?thesis using C_A2_ambient_identity_vector_truth[OF F G identity]
    by (simp only: C_vector_raise_Eq)
qed

lemma C_A2_closed_identity_vector_truth:
  assumes axiom: "\<Gamma> \<turnstile>\<^sub>C A" and shape: "A = Eq \<tau> F G"
    and closed: "C_vector_raise (length \<Delta>) A = A"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> F G" using axiom by (simp only: shape)
  have raised: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (C_vector_raise (length \<Delta>) A)) (C_abstract_prefix \<Delta> ObjTrue)"
    using C_A2_ambient_identity_formula_vector_truth[OF identity] by (simp only: shape)
  show ?thesis using raised by (simp only: closed)
qed

end
