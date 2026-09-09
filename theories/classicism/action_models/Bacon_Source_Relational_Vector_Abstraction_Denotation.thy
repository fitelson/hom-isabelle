theory Bacon_Source_Relational_Vector_Abstraction_Denotation
  imports Bacon_Source_Relational_Vector_Assignments Bacon_Source_Relational_Abstraction_Application
begin

section \<open>Typed argument vectors supply the bound names\<close>

lemma paper_R_update_vector_adequate_from_args:
  assumes args: "paper_R_vector_args D (map G ns) xs"
    and adequate: "named_adequate g (named_lam_vec ns A)"
  shows "named_adequate (paper_R_update_vector g ns xs) A"
proof -
  have lengths: "length ns = length xs" using paper_R_vector_args_length[OF args] by simp
  show ?thesis by (rule iffD2[OF paper_R_update_vector_adequate_iff[OF lengths] adequate])
qed

section \<open>Actual denotation of a finite R abstraction vector\<close>

text \<open>
  Applying ⟦λn₁…nₖ.A⟧ᵍ to a₁,…,aₖ gives
  ⟦A⟧ᵍ[n₁↦a₁]⋯[nₖ↦aₖ], with updates in source order.
  Source: the iterated λ convention, pp.5–9, and Definitions
  3.1 and 3.3, pp.43–46. A has type t, while intermediate
  bodies may have positive relational arity.

  The original g need cover only the abstraction's free variables.
  Each typed argument update supplies the next binder. Repeated
  names and arbitrary target-domain arguments are permitted; there
  is no distinctness, freshness, source-image, or total-completion
  premise. The induction uses the proved scalar R abstraction
  equation, not Functionality or abstraction extensionality.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_lam_vec_application_denote:
  assumes body: "paper_R_in_language signature stock A Prop"
    and binders: "list_all paper_R_type (map stock ns)"
    and typed: "named_env_typed domain stock g"
    and adequate: "named_adequate g (named_lam_vec ns A)"
    and args: "paper_R_vector_args domain (map stock ns) xs"
  shows "paper_R_apply_vector signature stock domain denote (map stock ns)
    (denote g (named_lam_vec ns A)) xs = denote (paper_R_update_vector g ns xs) A"
  using binders typed adequate args
proof (induction ns arbitrary: g xs)
  case Nil
  have empty: "xs = []" using Nil.prems(4) by simp
  show ?case by (simp only: empty list.map named_lam_vec.simps paper_R_apply_vector.simps paper_R_update_vector.simps)
next
  case (Cons n ns)
  have nt: "paper_R_type (stock n)" and tail_types: "list_all paper_R_type (map stock ns)"
    using Cons.prems(1) by simp_all
  obtain a ys where shape: "xs = a#ys" and member: "a \<in> domain (stock n)"
    and tail_args: "paper_R_vector_args domain (map stock ns) ys"
    using Cons.prems(4) by (cases xs) auto
  have inner: "paper_R_in_language signature stock (named_lam_vec ns A) (paper_type_vector (map stock ns) Prop)"
    by (rule paper_R_named_lam_vec_prop_language[OF body tail_types])
  have inner_result: "paper_type_vector (map stock ns) Prop \<noteq> Ind"
    by (rule paper_type_vector_Prop_not_Ind)
  have outer_adequate: "named_adequate g (NLam n (named_lam_vec ns A))"
    using Cons.prems(3) by (simp only: named_lam_vec.simps)
  have updated_typed: "named_env_typed domain stock (g(n := Some a))"
    by (rule named_assignment_update_typed[where D=domain and G=stock, OF Cons.prems(2) member])
  have updated_adequate: "named_adequate (g(n := Some a)) (named_lam_vec ns A)"
    by (rule iffD2[OF paper_R_named_lam_vec_head_update[where g=g and n=n and a=a and ns=ns and A=A]
      Cons.prems(3)])
  have scalar: "paper_R_application signature stock domain denote (stock n) (paper_type_vector (map stock ns) Prop)
    (denote g (NLam n (named_lam_vec ns A))) a = denote (g(n := Some a)) (named_lam_vec ns A)"
    by (rule paper_R_abstraction_application_denote[OF inner nt inner_result Cons.prems(2) outer_adequate member])
  have rest: "paper_R_apply_vector signature stock domain denote (map stock ns)
      (denote (g(n := Some a)) (named_lam_vec ns A)) ys =
    denote (paper_R_update_vector (g(n := Some a)) ns ys) A"
    by (rule Cons.IH[where g="g(n := Some a)" and xs=ys,
      OF tail_types updated_typed updated_adequate tail_args])
  show ?case by (simp only: shape list.map named_lam_vec.simps paper_R_apply_vector.simps
    paper_R_update_vector.simps scalar rest)
qed

end

end
