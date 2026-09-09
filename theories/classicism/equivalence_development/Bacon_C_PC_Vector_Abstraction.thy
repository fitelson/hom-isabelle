theory Bacon_C_PC_Vector_Abstraction
  imports Bacon_C_PC_Tuple_Representation
begin

section \<open>PC beneath an arbitrary abstraction vector\<close>

text \<open>
  If A is a propositional tautology, then ⊢C (λv̄.A) = (λv̄.⊤₀).
  Source: the PC case of Bacon–Dorr Appendix A.2(i), p.65.
  Enumerate A's finitely many propositional atoms, form their Church tuple,
  and replace atoms in the Boolean skeleton by projections of one tuple
  variable.  Single-abstraction PC proves equality of the resulting closed
  operations.  Substitute the atom tuple beneath λv̄ by operation
  congruence, then normalize both applications by typed βη conversion.

  Isabelle representation.  Δ is the de Bruijn context prefix; rev Δ is
  the outer-to-inner abstraction order.  Variables in Δ may have different
  types, but every component of the atom tuple has proposition type.
  The empty vector is included.  The finite atom enumeration does not
  assume distinctness or positive length, and each projection has its own
  checked index bound supplied by atom membership.

  Status.  This completes the full-vector PC case in axiom-based C alone.
  It neither abstracts an arbitrary C theorem nor uses CE/CEV Equivalence.
  The other axiom and rule cases of Appendix A.2 remain separate theorems.
\<close>

theorem C_PC_vector_abstraction:
  assumes tautology: "prop_tautology (\<Delta> @ \<Gamma>) A"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  have enumeration: "\<exists>xs. set xs = C_PC_atoms A" by (rule finite_list[OF C_PC_atoms_finite])
  from enumeration obtain xs where enumerates: "set xs = C_PC_atoms A" by (elim exE)
  have coverage: "C_PC_atoms A \<subseteq> set xs" by (simp only: enumerates subset_refl)
  have A_type: "\<Delta> @ \<Gamma> \<turnstile> A : Prop"
    using tautology unfolding prop_tautology_def by (rule conjunct1)
  have args: "\<Delta> @ \<Gamma> \<turnstile> a : Prop" if member: "a \<in> set xs" for a
  proof -
    have atom: "a \<in> C_PC_atoms A" using member by (simp only: enumerates)
    show ?thesis by (rule C_PC_atoms_typed[OF A_type atom])
  qed
  let ?F = "C_PC_tuple_operation xs A"
  let ?G = "C_PC_tuple_truth_operation (length xs)"
  let ?W = "C_Church_tuple xs"
  let ?T = "C_Church_tuple_type (length xs)"
  have F_type: "\<Gamma> \<turnstile> ?F : ?T \<rightarrow>\<^sub>o Prop" by (rule C_PC_tuple_operation_type[OF coverage])
  have G_type: "\<Gamma> \<turnstile> ?G : ?T \<rightarrow>\<^sub>o Prop" by (rule C_PC_tuple_truth_operation_type)
  have W_type: "\<Delta> @ \<Gamma> \<turnstile> ?W : ?T" by (rule C_Church_tuple_type[OF args])
  have operation_identity: "\<Gamma> \<turnstile>\<^sub>C Eq (?T \<rightarrow>\<^sub>o Prop) ?F ?G"
    by (rule C_PC_tuple_operation_identity[OF tautology coverage])
  have left_application: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop (App ?F ?W) A"
    by (rule C_PC_tuple_application_conversion[OF args coverage])
  have right_application: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop (App ?G ?W) ObjTrue"
    by (rule C_PC_tuple_truth_application_conversion[OF W_type])
  have left_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (App (C_vector_raise (length \<Delta>) ?F) ?W) A"
    using left_application by (simp only: C_PC_tuple_operation_raise)
  have right_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (App (C_vector_raise (length \<Delta>) ?G) ?W) ObjTrue"
    using right_application by (simp only: C_PC_tuple_truth_operation_raise)
  show ?thesis by (rule C_vector_function_congruence_beta[
    OF F_type G_type W_type operation_identity left_conversion right_conversion])
qed

end
