theory Bacon_C_Appendix_A2_Closed_Axioms
  imports Bacon_C_Appendix_A2_Ambient_Identity Bacon_C_Appendix_A2_Zeroary
begin

section \<open>The closed Boolean and Classicist identity-axiom cases\<close>

text \<open>
  Every closed identity axiom E of C satisfies ⊢C (λv̄.E) = (λv̄.⊤₀).
  Sources: Bacon–Dorr Figure 3, p.10, Figure 4, p.13, and the identity-axiom
  cases of Appendix A.2(i), p.65.

  Isabelle representation.  Each listed schema is syntactically an
  identity of closed operations.  Its whole formula is unchanged by
  raising.  The preceding ambient-identity theorem therefore applies
  without abstracting an equation whose terms depend on Δ.

  Status.  This covers the six source Boolean identities, the represented
  material-implication operation bridge, and the five Classicist schemas.
  The material-implication bridge compensates for primitive Imp in the
  datatype; it is not a seventh independent source Boolean thesis.
  These are axiom cases, not yet the complete C proof induction.
\<close>

lemma C_A2_boolean_axiom_rename:
  assumes axiom: "A \<in> set all_boolean_identities"
  shows "rename r A = A"
  using axiom by (auto simp: all_boolean_identities_def bool_comm_conj_def bool_comm_disj_def
    bool_dist_conj_disj_def bool_dist_disj_conj_def bool_dissolve_conj_disj_def
    bool_dissolve_disj_conj_def bool_material_imp_def numeral_2_eq_2)

lemma C_A2_boolean_axiom_raise:
  assumes axiom: "A \<in> set all_boolean_identities"
  shows "C_vector_raise n A = A"
  by (induction n) (simp_all add: C_A2_boolean_axiom_rename[OF axiom])

theorem C_A2_BooleanIdentity_vector_truth:
  assumes axiom: "A \<in> set all_boolean_identities"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  obtain \<tau> F G where shape: "A = Eq \<tau> F G" by (rule C_A2_boolean_identity_shape[OF axiom])
  have source: "\<Gamma> \<turnstile>\<^sub>C A" by (rule C_proves.BooleanIdentity[OF axiom])
  have closed: "C_vector_raise (length \<Delta>) A = A" by (rule C_A2_boolean_axiom_raise[OF axiom])
  show ?thesis by (rule C_A2_closed_identity_vector_truth[OF source shape closed])
qed

lemma C_A2_classic_axiom_rename:
  assumes axiom: "A \<in> set [classic_identity_identity \<sigma>, classic_absorb_disj_forall \<sigma>,
    classic_dist_disj_forall \<sigma>, classic_absorb_conj_exists \<sigma>, classic_dist_conj_exists \<sigma>]"
  shows "rename r A = A"
  using axiom by (auto simp: classic_identity_identity_def classic_absorb_disj_forall_def
    classic_dist_disj_forall_def classic_absorb_conj_exists_def classic_dist_conj_exists_def numeral_2_eq_2)

lemma C_A2_classic_axiom_raise:
  assumes axiom: "A \<in> set [classic_identity_identity \<sigma>, classic_absorb_disj_forall \<sigma>,
    classic_dist_disj_forall \<sigma>, classic_absorb_conj_exists \<sigma>, classic_dist_conj_exists \<sigma>]"
  shows "C_vector_raise n A = A"
  by (induction n) (simp_all add: C_A2_classic_axiom_rename[OF axiom])

theorem C_A2_classic_axiom_vector_truth:
  assumes axiom: "A \<in> set [classic_identity_identity \<sigma>, classic_absorb_disj_forall \<sigma>,
    classic_dist_disj_forall \<sigma>, classic_absorb_conj_exists \<sigma>, classic_dist_conj_exists \<sigma>]"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  have source: "\<Gamma> \<turnstile>\<^sub>C A"
    using axiom by (auto intro: C_proves.IdentityIdentity C_proves.AbsorbDisjForall
      C_proves.DistDisjForall C_proves.AbsorbConjExists C_proves.DistConjExists)
  obtain \<tau> F G where shape: "A = Eq \<tau> F G"
    using axiom by (auto simp: classic_identity_identity_def classic_absorb_disj_forall_def
      classic_dist_disj_forall_def classic_absorb_conj_exists_def classic_dist_conj_exists_def)
  have closed: "C_vector_raise (length \<Delta>) A = A" by (rule C_A2_classic_axiom_raise[OF axiom])
  show ?thesis by (rule C_A2_closed_identity_vector_truth[OF source shape closed])
qed

corollary C_A2_IdentityIdentity_vector_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (classic_identity_identity \<sigma>)) (C_abstract_prefix \<Delta> ObjTrue)"
  by (rule C_A2_classic_axiom_vector_truth[where \<sigma>=\<sigma>]) simp

corollary C_A2_AbsorbDisjForall_vector_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (classic_absorb_disj_forall \<sigma>)) (C_abstract_prefix \<Delta> ObjTrue)"
  by (rule C_A2_classic_axiom_vector_truth[where \<sigma>=\<sigma>]) simp

corollary C_A2_DistDisjForall_vector_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (classic_dist_disj_forall \<sigma>)) (C_abstract_prefix \<Delta> ObjTrue)"
  by (rule C_A2_classic_axiom_vector_truth[where \<sigma>=\<sigma>]) simp

corollary C_A2_AbsorbConjExists_vector_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (classic_absorb_conj_exists \<sigma>)) (C_abstract_prefix \<Delta> ObjTrue)"
  by (rule C_A2_classic_axiom_vector_truth[where \<sigma>=\<sigma>]) simp

corollary C_A2_DistConjExists_vector_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (classic_dist_conj_exists \<sigma>)) (C_abstract_prefix \<Delta> ObjTrue)"
  by (rule C_A2_classic_axiom_vector_truth[where \<sigma>=\<sigma>]) simp

end
