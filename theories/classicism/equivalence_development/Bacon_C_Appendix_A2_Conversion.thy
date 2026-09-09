theory Bacon_C_Appendix_A2_Conversion
  imports Bacon_C_PC_Vector_Abstraction Bacon_C_PC_Beta_Congruence
begin

section \<open>Appendix A.2: the β and η axiom cases at vector generality\<close>

text \<open>
  If M ≡βη N : t in the context of v̄, then
  ⊢C (λv̄.M ↔ N) = (λv̄.⊤₀).
  Source: Bacon--Dorr Figure 2, p.8, the β and η axioms, and their
  conversion cases in Proposition A.2, pp.65–67.

  Isabelle representation.  The literal biconditional is
  Conj (Imp M N) (Imp N M).  Syntactic conversion replaces N by M
  in both occurrences, giving the PC tautology M ↔ M.  Conversion is
  lifted through the entire abstraction prefix before vector PC is used.
  Status.  These are axiom-based C identities.  The βη premise is a
  typed syntactic conversion, not an arbitrary theorem M ↔ N; the full
  Equivalence rule and the remaining A.2 derivation cases are not assumed.
\<close>

lemma C_A2_biconditional_to_reflexive_conversion:
  assumes conversion: "beta_eta_equiv \<Gamma> Prop M N"
  shows "beta_eta_equiv \<Gamma> Prop (M \<longleftrightarrow>\<^sub>o N) (M \<longleftrightarrow>\<^sub>o M)"
proof -
  have M: "\<Gamma> \<turnstile> M : Prop" by (rule beta_eta_equiv_left_type[OF conversion])
  have reflexive: "beta_eta_equiv \<Gamma> Prop M M" by (rule beta_eta_equiv.Refl[OF M])
  have reverse_conversion: "beta_eta_equiv \<Gamma> Prop N M" by (rule beta_eta_equiv.Sym[OF conversion])
  have forward_imp: "beta_eta_equiv \<Gamma> Prop (Imp M N) (Imp M M)"
    by (rule C_PC_beta_eta_Imp[OF reflexive reverse_conversion])
  have reverse_imp: "beta_eta_equiv \<Gamma> Prop (Imp N M) (Imp M M)"
    by (rule C_PC_beta_eta_Imp[OF reverse_conversion reflexive])
  show ?thesis by (rule C_PC_beta_eta_Conj[OF forward_imp reverse_imp])
qed

lemma C_A2_reflexive_biconditional_PC:
  assumes M: "\<Gamma> \<turnstile> M : Prop"
  shows "prop_tautology \<Gamma> (M \<longleftrightarrow>\<^sub>o M)"
proof -
  have formula_type: "\<Gamma> \<turnstile> (M \<longleftrightarrow>\<^sub>o M) : Prop"
    by (intro has_type.Conj has_type.Imp M)
  have evaluation: "\<forall>w. prop_eval w (M \<longleftrightarrow>\<^sub>o M)" by simp
  show ?thesis unfolding prop_tautology_def by (rule conjI[OF formula_type evaluation])
qed

theorem C_A2_beta_eta_vector_truth:
  assumes conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop M N"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (M \<longleftrightarrow>\<^sub>o N)) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  have M: "\<Delta> @ \<Gamma> \<turnstile> M : Prop" by (rule beta_eta_equiv_left_type[OF conversion])
  have to_reflexive: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (M \<longleftrightarrow>\<^sub>o N))
    (C_abstract_prefix \<Delta> (M \<longleftrightarrow>\<^sub>o M))"
    by (rule C_vector_conversion_identity[OF C_A2_biconditional_to_reflexive_conversion[OF conversion]])
  have reflexive_truth: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (M \<longleftrightarrow>\<^sub>o M)) (C_abstract_prefix \<Delta> ObjTrue)"
    by (rule C_PC_vector_abstraction[OF C_A2_reflexive_biconditional_PC[OF M]])
  show ?thesis by (rule C_A1_trans[OF to_reflexive reflexive_truth])
qed

corollary C_A2_beta_axiom_vector_truth:
  assumes M: "\<Delta> @ \<Gamma> \<turnstile> M : Prop" and N: "\<Delta> @ \<Gamma> \<turnstile> N : Prop"
    and step: "compatible_step beta_contract M N"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (M \<longleftrightarrow>\<^sub>o N)) (C_abstract_prefix \<Delta> ObjTrue)"
  by (rule C_A2_beta_eta_vector_truth[OF beta_eta_equiv.Beta[OF M N step]])

corollary C_A2_eta_axiom_vector_truth:
  assumes M: "\<Delta> @ \<Gamma> \<turnstile> M : Prop" and N: "\<Delta> @ \<Gamma> \<turnstile> N : Prop"
    and step: "compatible_step eta_contract M N"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (M \<longleftrightarrow>\<^sub>o N)) (C_abstract_prefix \<Delta> ObjTrue)"
  by (rule C_A2_beta_eta_vector_truth[OF beta_eta_equiv.Eta[OF M N step]])

end
