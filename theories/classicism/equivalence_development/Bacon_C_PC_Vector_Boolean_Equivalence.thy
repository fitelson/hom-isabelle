theory Bacon_C_PC_Vector_Boolean_Equivalence
  imports Bacon_C_PC_Boolean_Equivalence Bacon_C_PC_Vector_Abstraction
begin

section \<open>Boolean equivalence beneath arbitrary abstraction vectors\<close>

text \<open>
  If A ↔ B is a propositional tautology, then ⊢C (λv̄.A) = (λv̄.B).
  Enumerate At(A) ∪ At(B) by one shared list xs.  Replacing each atom
  by a projection of the same tuple variable preserves the tautological
  biconditional.  The one-binder Boolean-equivalence theorem identifies
  the two closed operations.  Apply both to ⟨xs⟩ beneath λv̄ and use
  the checked projection conversions.
  Source role: Boolean substitution in Bacon–Dorr Appendix A.2(i), p.65.

  Isabelle representation.  Both operations use the same tuple type and
  atom-index map.  The de Bruijn prefix Δ may contain arbitrary types;
  tuple entries are propositions.  Empty vectors are included and no
  positive atom-count premise is added.  This theorem concerns Boolean
  equivalence certified by prop_tautology, not arbitrary C theoremhood of
  A ↔ B.  No CE/CEV rule or general C Equivalence is asserted.
\<close>

lemma C_PC_tuple_boolean_equivalence:
  assumes tautology: "prop_tautology \<Xi> (A \<longleftrightarrow>\<^sub>o B)"
    and coverA: "C_PC_atoms A \<subseteq> set xs" and coverB: "C_PC_atoms B \<subseteq> set xs"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (C_Church_tuple_type (length xs) \<rightarrow>\<^sub>o Prop)
    (C_PC_tuple_operation xs A) (C_PC_tuple_operation xs B)"
proof -
  have coverage: "C_PC_atoms (A \<longleftrightarrow>\<^sub>o B) \<subseteq> set xs" using coverA coverB by auto
  have mapped_raw: "prop_tautology (C_Church_tuple_type (length xs) # \<Gamma>)
    (C_PC_tuple_body xs (A \<longleftrightarrow>\<^sub>o B))"
    by (rule C_PC_tuple_body_tautology[OF tautology coverage])
  have mapped: "prop_tautology (C_Church_tuple_type (length xs) # \<Gamma>)
    (C_PC_tuple_body xs A \<longleftrightarrow>\<^sub>o C_PC_tuple_body xs B)"
    using mapped_raw by (simp only: C_PC_tuple_body_def C_PC_map_atoms.simps)
  show ?thesis unfolding C_PC_tuple_operation_def
    by (rule C_PC_boolean_equivalence_single_abstraction[OF mapped])
qed

theorem C_PC_boolean_equivalence_vector_abstraction:
  assumes tautology: "prop_tautology (\<Delta> @ \<Gamma>) (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> B)"
proof -
  have finite_atoms: "finite (C_PC_atoms A \<union> C_PC_atoms B)"
    by (rule finite_UnI[OF C_PC_atoms_finite C_PC_atoms_finite])
  have enumeration: "\<exists>xs. set xs = C_PC_atoms A \<union> C_PC_atoms B" by (rule finite_list[OF finite_atoms])
  from enumeration obtain xs where enumerates: "set xs = C_PC_atoms A \<union> C_PC_atoms B" by (elim exE)
  have coverA: "C_PC_atoms A \<subseteq> set xs" and coverB: "C_PC_atoms B \<subseteq> set xs"
    by (auto simp only: enumerates)
  have A_type: "\<Delta> @ \<Gamma> \<turnstile> A : Prop" by (rule C_PC_tautological_biconditional_data(1)[OF tautology])
  have B_type: "\<Delta> @ \<Gamma> \<turnstile> B : Prop" by (rule C_PC_tautological_biconditional_data(2)[OF tautology])
  have args: "\<Delta> @ \<Gamma> \<turnstile> a : Prop" if member: "a \<in> set xs" for a
  proof -
    have union_member: "a \<in> C_PC_atoms A \<union> C_PC_atoms B" using member by (simp only: enumerates)
    show ?thesis
    proof (rule UnE[OF union_member])
      assume atom: "a \<in> C_PC_atoms A"
      show ?thesis by (rule C_PC_atoms_typed[OF A_type atom])
    next
      assume atom: "a \<in> C_PC_atoms B"
      show ?thesis by (rule C_PC_atoms_typed[OF B_type atom])
    qed
  qed
  let ?F = "C_PC_tuple_operation xs A"
  let ?G = "C_PC_tuple_operation xs B"
  let ?W = "C_Church_tuple xs"
  let ?T = "C_Church_tuple_type (length xs)"
  have F_type: "\<Gamma> \<turnstile> ?F : ?T \<rightarrow>\<^sub>o Prop" by (rule C_PC_tuple_operation_type[OF coverA])
  have G_type: "\<Gamma> \<turnstile> ?G : ?T \<rightarrow>\<^sub>o Prop" by (rule C_PC_tuple_operation_type[OF coverB])
  have W_type: "\<Delta> @ \<Gamma> \<turnstile> ?W : ?T" by (rule C_Church_tuple_type[OF args])
  have operation_identity: "\<Gamma> \<turnstile>\<^sub>C Eq (?T \<rightarrow>\<^sub>o Prop) ?F ?G"
    by (rule C_PC_tuple_boolean_equivalence[OF tautology coverA coverB])
  have left_application: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop (App ?F ?W) A"
    by (rule C_PC_tuple_application_conversion[OF args coverA])
  have right_application: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop (App ?G ?W) B"
    by (rule C_PC_tuple_application_conversion[OF args coverB])
  have left_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (App (C_vector_raise (length \<Delta>) ?F) ?W) A"
    using left_application by (simp only: C_PC_tuple_operation_raise)
  have right_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (App (C_vector_raise (length \<Delta>) ?G) ?W) B"
    using right_application by (simp only: C_PC_tuple_operation_raise)
  show ?thesis by (rule C_vector_function_congruence_beta[
    OF F_type G_type W_type operation_identity left_conversion right_conversion])
qed

end
