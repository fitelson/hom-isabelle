theory Bacon_C_Appendix_A2_EG
  imports Bacon_C_Appendix_A2_UI
begin

section \<open>Appendix A.2: existential generalization beneath an arbitrary vector\<close>

text \<open>
  Absorption-∧∃ says F T ∧ ∃x.Fx = F T at the operation level.
  Replacing that operation inside λv̄.(· → ∃x.B), then reducing β,
  identifies B[T/x] → ∃x.B with (B[T/x] ∧ ∃x.B) → ∃x.B.
  Vector PC therefore gives
  ⊢C (λv̄.B[T/x] → ∃x.B) = (λv̄.⊤₀).
  Sources: Bacon--Dorr Figure 2 EG, p.8; Figure 4 Absorption-∧∃,
  p.13; Proposition A.2, pp.65–67.

  Isabelle representation.  B has context σ # (Δ @ Γ), and T has
  context Δ @ Γ.  The right operation is exactly the projection
  C_UI_absorb_right already used for universal instantiation.
  Status.  This is the full-vector EG axiom case in C, not a
  pointwise-identity abstraction, Equivalence rule, or model argument.
\<close>

definition C_EG_absorb_left :: "otype \<Rightarrow> oterm" where
  "C_EG_absorb_left \<sigma> = Lam (pred_ty \<sigma>) (Lam \<sigma>
    (Conj (App (Var 1) (Var 0)) (Exists \<sigma> (App (Var 2) (Var 0)))))"

lemma C_EG_absorb_type:
  "\<Gamma> \<turnstile> C_EG_absorb_left \<sigma> : pred_ty \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
  by (rule infer_type_sound) (simp add: C_EG_absorb_left_def pred_ty_def lookup_def)

lemma C_EG_absorb_identity:
  "\<Gamma> \<turnstile>\<^sub>C Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop)
    (C_EG_absorb_left \<sigma>) (C_UI_absorb_right \<sigma>)"
  using C_proves.AbsorbConjExists[of \<Gamma> \<sigma>]
  by (simp only: classic_absorb_conj_exists_def C_EG_absorb_left_def C_UI_absorb_right_def)

lemma C_EG_absorb_raised:
  "C_vector_raise n (C_EG_absorb_left \<sigma>) = C_EG_absorb_left \<sigma>"
  by (induction n) (simp_all add: C_EG_absorb_left_def numeral_2_eq_2)

lemma C_EG_quantified_predicate_beta:
  assumes B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "beta_eta_equiv \<Gamma> Prop
    (Exists \<sigma> (App (shift (Lam \<sigma> B)) (Var 0))) (Exists \<sigma> B)"
proof -
  have predicate_type: "\<Gamma> \<turnstile> Lam \<sigma> B : \<sigma> \<rightarrow>\<^sub>o Prop" by (rule has_type.Lam[OF B])
  have shifted: "\<sigma> # \<Gamma> \<turnstile> shift (Lam \<sigma> B) : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule weakening_front[OF predicate_type])
  have variable: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  have body: "\<sigma> # \<Gamma> \<turnstile> App (shift (Lam \<sigma> B)) (Var 0) : Prop"
    by (rule has_type.App[OF shifted variable])
  have source: "\<Gamma> \<turnstile> Exists \<sigma> (App (shift (Lam \<sigma> B)) (Var 0)) : Prop"
    by (rule has_type.Exists[OF body])
  have target_type: "\<Gamma> \<turnstile> Exists \<sigma> B : Prop" by (rule has_type.Exists[OF B])
  have step: "compatible_step beta_contract
    (Exists \<sigma> (App (shift (Lam \<sigma> B)) (Var 0))) (Exists \<sigma> B)"
    by (rule compatible_step.Exists_body[OF C_abstraction_argument_beta_step])
  show ?thesis by (rule beta_eta_equiv.Beta[OF source target_type step])
qed

lemma C_EG_absorb_left_beta:
  assumes B: "\<sigma> # \<Gamma> \<turnstile> B : Prop" and T: "\<Gamma> \<turnstile> T : \<sigma>"
  shows "beta_eta_equiv \<Gamma> Prop
    (App (App (C_EG_absorb_left \<sigma>) (Lam \<sigma> B)) T)
    (Conj (subst0 T B) (Exists \<sigma> B))"
proof -
  let ?P = "Conj (App (Var 1) (Var 0)) (Exists \<sigma> (App (Var 2) (Var 0)))"
  have body: "\<sigma> # pred_ty \<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have predicate_type: "\<Gamma> \<turnstile> Lam \<sigma> B : pred_ty \<sigma>"
    using has_type.Lam[OF B] by (simp only: pred_ty_def)
  have first: "beta_eta_equiv \<Gamma> Prop
    (App (App (C_EG_absorb_left \<sigma>) (Lam \<sigma> B)) T)
    (Conj (App (Lam \<sigma> B) T) (Exists \<sigma> (App (shift (Lam \<sigma> B)) (Var 0))))"
    using C_A2_binary_application_beta[OF body predicate_type T]
    by (simp add: C_EG_absorb_left_def subst0_def numeral_2_eq_2
      C_subst_twice_raised C_subst_raised C_remove_inserted_operation
      C_A2_subst_twice_lifted shift_def)
  have second: "beta_eta_equiv \<Gamma> Prop
    (Conj (App (Lam \<sigma> B) T) (Exists \<sigma> (App (shift (Lam \<sigma> B)) (Var 0))))
    (Conj (subst0 T B) (Exists \<sigma> B))"
    by (rule C_PC_beta_eta_Conj[OF C_UI_predicate_application_beta[OF B T]
      C_EG_quantified_predicate_beta[OF B]])
  show ?thesis by (rule beta_eta_equiv.Trans[OF first second])
qed

subsection \<open>Operation replacement in the antecedent of EG\<close>

lemma C_EG_vector_absorption_context:
  assumes B: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> B : Prop" and T: "\<Delta> @ \<Gamma> \<turnstile> T : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (Conj (subst0 T B) (Exists \<sigma> B)) (Exists \<sigma> B)))
    (C_abstract_prefix \<Delta> (Imp (subst0 T B) (Exists \<sigma> B)))"
proof -
  let ?K = "pred_ty \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
  let ?r = "C_vector_lift_ren (length \<Delta>) Suc"
  let ?E = "Exists \<sigma> B"
  let ?F = "Lam \<sigma> B"
  let ?M = "Imp (App (App (Var (length \<Delta>)) (rename ?r ?F)) (rename ?r T)) (rename ?r ?E)"
  have E: "\<Delta> @ \<Gamma> \<turnstile> ?E : Prop" by (rule has_type.Exists[OF B])
  have F: "\<Delta> @ \<Gamma> \<turnstile> ?F : pred_ty \<sigma>"
    using has_type.Lam[OF B] by (simp only: pred_ty_def)
  have E': "\<Delta> @ (?K # \<Gamma>) \<turnstile> rename ?r ?E : Prop" by (rule C_vector_insert_parameter_type[OF E])
  have F': "\<Delta> @ (?K # \<Gamma>) \<turnstile> rename ?r ?F : pred_ty \<sigma>" by (rule C_vector_insert_parameter_type[OF F])
  have T': "\<Delta> @ (?K # \<Gamma>) \<turnstile> rename ?r T : \<sigma>" by (rule C_vector_insert_parameter_type[OF T])
  have base_index: "lookup (?K # \<Gamma>) 0 = Some ?K" by simp
  have index: "lookup (\<Delta> @ (?K # \<Gamma>)) (length \<Delta>) = Some ?K"
    using lookup_append_shift[OF base_index, where \<Delta>=\<Delta>] by simp
  have operator: "\<Delta> @ (?K # \<Gamma>) \<turnstile> Var (length \<Delta>) : ?K" by (rule has_type.Var[OF index])
  have first_app: "\<Delta> @ (?K # \<Gamma>) \<turnstile> App (Var (length \<Delta>)) (rename ?r ?F) : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.App[OF operator F'])
  have second_app: "\<Delta> @ (?K # \<Gamma>) \<turnstile>
    App (App (Var (length \<Delta>)) (rename ?r ?F)) (rename ?r T) : Prop"
    by (rule has_type.App[OF first_app T'])
  have body: "\<Delta> @ (?K # \<Gamma>) \<turnstile> ?M : Prop" by (rule has_type.Imp[OF second_app E'])
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (App (App (C_EG_absorb_left \<sigma>) ?F) T) ?E))
    (C_abstract_prefix \<Delta> (Imp (App (App (C_UI_absorb_right \<sigma>) ?F) T) ?E))"
    using C_vector_identity_context[OF C_EG_absorb_type C_UI_absorb_types(2) body C_EG_absorb_identity]
    by (simp add: C_vector_remove_inserted_parameter C_vector_lift_subst_slot
      C_EG_absorb_raised C_UI_absorb_raised C_A2_remove_parameter_under_binder)
  have left_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (Imp (App (App (C_EG_absorb_left \<sigma>) ?F) T) ?E)
    (Imp (Conj (subst0 T B) ?E) ?E)"
    by (rule C_PC_beta_eta_Imp[OF C_EG_absorb_left_beta[OF B T] beta_eta_equiv.Refl[OF E]])
  have right_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (Imp (App (App (C_UI_absorb_right \<sigma>) ?F) T) ?E) (Imp (subst0 T B) ?E)"
    by (rule C_PC_beta_eta_Imp[OF C_UI_absorb_right_beta[OF B T] beta_eta_equiv.Refl[OF E]])
  show ?thesis by (rule C_A1_transport[OF raw C_vector_conversion_identity[OF left_conversion]
    C_vector_conversion_identity[OF right_conversion]])
qed

theorem C_A2_EG_vector_truth:
  assumes B: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> B : Prop" and T: "\<Delta> @ \<Gamma> \<turnstile> T : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (subst0 T B) (Exists \<sigma> B))) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  have E: "\<Delta> @ \<Gamma> \<turnstile> Exists \<sigma> B : Prop" by (rule has_type.Exists[OF B])
  have instance_type: "\<Delta> @ \<Gamma> \<turnstile> subst0 T B : Prop" by (rule subst0_preserves_typing[OF B T])
  have formula_type: "\<Delta> @ \<Gamma> \<turnstile> Imp (Conj (subst0 T B) (Exists \<sigma> B))
    (Exists \<sigma> B) : Prop"
    by (rule has_type.Imp[OF has_type.Conj[OF instance_type E] E])
  have PC: "prop_tautology (\<Delta> @ \<Gamma>)
    (Imp (Conj (subst0 T B) (Exists \<sigma> B)) (Exists \<sigma> B))"
    unfolding prop_tautology_def by (rule conjI[OF formula_type]) simp
  show ?thesis by (rule C_A1_trans[OF C_A1_sym[OF C_EG_vector_absorption_context[OF B T]]
    C_PC_vector_abstraction[OF PC]])
qed

end
