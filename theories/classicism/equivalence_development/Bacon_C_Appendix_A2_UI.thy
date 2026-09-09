theory Bacon_C_Appendix_A2_UI
  imports Bacon_C_Appendix_A2_Conversion
begin

section \<open>Appendix A.2: universal instantiation beneath an arbitrary vector\<close>

text \<open>
  Absorption-∨∀ says F T ∨ ∀x.Fx = F T at the operation level.
  Replacing that operation inside λv̄.(∀x.B → ·), then reducing β,
  identifies ∀x.B → B[T/x] with ∀x.B → (B[T/x] ∨ ∀x.B).
  The latter is a PC tautology.  Thus
  ⊢C (λv̄.∀x.B → B[T/x]) = (λv̄.⊤₀).
  Sources: Bacon--Dorr Figure 2 UI, p.8; Figure 4 Absorption-∨∀,
  p.13; Proposition A.2, pp.65–67.

  Isabelle representation.  The quantified body B has one additional
  σ-typed de Bruijn slot; T and ∀x.B may depend on the entire prefix Δ.
  Status.  The proof replaces the closed source operation identity,
  not a pointwise equality.  No C Equivalence or model premise is used.
\<close>

lemma C_A2_binary_application_beta:
  assumes P: "\<tau> # \<sigma> # \<Gamma> \<turnstile> P : \<rho>"
    and A: "\<Gamma> \<turnstile> A : \<sigma>" and B: "\<Gamma> \<turnstile> B : \<tau>"
  shows "beta_eta_equiv \<Gamma> \<rho>
    (App (App (Lam \<sigma> (Lam \<tau> P)) A) B)
    (subst0 B (subst (lift_subst (case_nat A Var)) P))"
proof -
  let ?Q = "subst (lift_subst (case_nat A Var)) P"
  have inner: "\<sigma> # \<Gamma> \<turnstile> Lam \<tau> P : \<tau> \<rightarrow>\<^sub>o \<rho>"
    by (rule has_type.Lam[OF P])
  have F: "\<Gamma> \<turnstile> Lam \<sigma> (Lam \<tau> P) : \<sigma> \<rightarrow>\<^sub>o \<tau> \<rightarrow>\<^sub>o \<rho>"
    by (rule has_type.Lam[OF inner])
  have FA: "\<Gamma> \<turnstile> App (Lam \<sigma> (Lam \<tau> P)) A : \<tau> \<rightarrow>\<^sub>o \<rho>"
    by (rule has_type.App[OF F A])
  have QL: "\<Gamma> \<turnstile> Lam \<tau> ?Q : \<tau> \<rightarrow>\<^sub>o \<rho>"
    using subst0_preserves_typing[OF inner A] by (simp add: subst0_def)
  have Q: "\<tau> # \<Gamma> \<turnstile> ?Q : \<rho>" using QL by (auto elim: has_type.cases)
  have middle: "\<Gamma> \<turnstile> App (Lam \<tau> ?Q) B : \<rho>"
    by (rule has_type.App[OF QL B])
  have target_type: "\<Gamma> \<turnstile> subst0 B ?Q : \<rho>"
    by (rule subst0_preserves_typing[OF Q B])
  have first_step: "compatible_step beta_contract
    (App (Lam \<sigma> (Lam \<tau> P)) A) (Lam \<tau> ?Q)"
  proof -
    have "compatible_step beta_contract
      (App (Lam \<sigma> (Lam \<tau> P)) A) (subst0 A (Lam \<tau> P))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis by (simp add: subst0_def)
  qed
  have first: "beta_eta_equiv \<Gamma> \<rho>
    (App (App (Lam \<sigma> (Lam \<tau> P)) A) B) (App (Lam \<tau> ?Q) B)"
    by (rule C_PC_beta_eta_App_left[OF beta_eta_equiv.Beta[OF FA QL first_step] B])
  have second_step: "compatible_step beta_contract (App (Lam \<tau> ?Q) B) (subst0 B ?Q)"
    by (intro compatible_step.root beta_contract.beta)
  show ?thesis by (rule beta_eta_equiv.Trans[OF first
    beta_eta_equiv.Beta[OF middle target_type second_step]])
qed

definition C_UI_absorb_left :: "otype \<Rightarrow> oterm" where
  "C_UI_absorb_left \<sigma> = Lam (pred_ty \<sigma>) (Lam \<sigma>
    (Disj (App (Var 1) (Var 0)) (Forall \<sigma> (App (Var 2) (Var 0)))))"

definition C_UI_absorb_right :: "otype \<Rightarrow> oterm" where
  "C_UI_absorb_right \<sigma> = Lam (pred_ty \<sigma>) (Lam \<sigma> (App (Var 1) (Var 0)))"

lemma C_UI_absorb_types:
  "\<Gamma> \<turnstile> C_UI_absorb_left \<sigma> : pred_ty \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
  "\<Gamma> \<turnstile> C_UI_absorb_right \<sigma> : pred_ty \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
proof -
  show "\<Gamma> \<turnstile> C_UI_absorb_left \<sigma> : pred_ty \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: C_UI_absorb_left_def pred_ty_def lookup_def)
  show "\<Gamma> \<turnstile> C_UI_absorb_right \<sigma> : pred_ty \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: C_UI_absorb_right_def pred_ty_def lookup_def)
qed

lemma C_UI_absorb_identity:
  "\<Gamma> \<turnstile>\<^sub>C Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop)
    (C_UI_absorb_left \<sigma>) (C_UI_absorb_right \<sigma>)"
  using C_proves.AbsorbDisjForall[of \<Gamma> \<sigma>]
  by (simp only: classic_absorb_disj_forall_def C_UI_absorb_left_def C_UI_absorb_right_def)

lemma C_UI_absorb_raised:
  "C_vector_raise n (C_UI_absorb_left \<sigma>) = C_UI_absorb_left \<sigma>"
  "C_vector_raise n (C_UI_absorb_right \<sigma>) = C_UI_absorb_right \<sigma>"
proof -
  show "C_vector_raise n (C_UI_absorb_left \<sigma>) = C_UI_absorb_left \<sigma>"
    by (induction n) (simp_all add: C_UI_absorb_left_def numeral_2_eq_2)
  show "C_vector_raise n (C_UI_absorb_right \<sigma>) = C_UI_absorb_right \<sigma>"
    by (induction n) (simp_all add: C_UI_absorb_right_def)
qed

lemma C_UI_predicate_application_beta:
  assumes B: "\<sigma> # \<Gamma> \<turnstile> B : Prop" and T: "\<Gamma> \<turnstile> T : \<sigma>"
  shows "beta_eta_equiv \<Gamma> Prop (App (Lam \<sigma> B) T) (subst0 T B)"
proof -
  have predicate_type: "\<Gamma> \<turnstile> Lam \<sigma> B : \<sigma> \<rightarrow>\<^sub>o Prop" by (rule has_type.Lam[OF B])
  have source: "\<Gamma> \<turnstile> App (Lam \<sigma> B) T : Prop" by (rule has_type.App[OF predicate_type T])
  have target_type: "\<Gamma> \<turnstile> subst0 T B : Prop" by (rule subst0_preserves_typing[OF B T])
  have step: "compatible_step beta_contract (App (Lam \<sigma> B) T) (subst0 T B)"
    by (intro compatible_step.root beta_contract.beta)
  show ?thesis by (rule beta_eta_equiv.Beta[OF source target_type step])
qed

lemma C_UI_quantified_predicate_beta:
  assumes B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "beta_eta_equiv \<Gamma> Prop
    (Forall \<sigma> (App (shift (Lam \<sigma> B)) (Var 0))) (Forall \<sigma> B)"
proof -
  have predicate_type: "\<Gamma> \<turnstile> Lam \<sigma> B : \<sigma> \<rightarrow>\<^sub>o Prop" by (rule has_type.Lam[OF B])
  have shifted: "\<sigma> # \<Gamma> \<turnstile> shift (Lam \<sigma> B) : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule weakening_front[OF predicate_type])
  have variable: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  have body: "\<sigma> # \<Gamma> \<turnstile> App (shift (Lam \<sigma> B)) (Var 0) : Prop"
    by (rule has_type.App[OF shifted variable])
  have source: "\<Gamma> \<turnstile> Forall \<sigma> (App (shift (Lam \<sigma> B)) (Var 0)) : Prop"
    by (rule has_type.Forall[OF body])
  have target_type: "\<Gamma> \<turnstile> Forall \<sigma> B : Prop" by (rule has_type.Forall[OF B])
  have step: "compatible_step beta_contract
    (Forall \<sigma> (App (shift (Lam \<sigma> B)) (Var 0))) (Forall \<sigma> B)"
    by (rule compatible_step.Forall_body[OF C_abstraction_argument_beta_step])
  show ?thesis by (rule beta_eta_equiv.Beta[OF source target_type step])
qed

lemma C_A2_subst_twice_lifted:
  "subst (lift_subst (lift_subst (case_nat T Var)))
    (rename (lift_ren Suc) (rename (lift_ren Suc) B)) = rename (lift_ren Suc) B"
  by (rule C_subst_two_renamings) (case_tac n; simp)

lemma C_UI_absorb_left_beta:
  assumes B: "\<sigma> # \<Gamma> \<turnstile> B : Prop" and T: "\<Gamma> \<turnstile> T : \<sigma>"
  shows "beta_eta_equiv \<Gamma> Prop
    (App (App (C_UI_absorb_left \<sigma>) (Lam \<sigma> B)) T)
    (Disj (subst0 T B) (Forall \<sigma> B))"
proof -
  let ?P = "Disj (App (Var 1) (Var 0)) (Forall \<sigma> (App (Var 2) (Var 0)))"
  have body: "\<sigma> # pred_ty \<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have predicate_type: "\<Gamma> \<turnstile> Lam \<sigma> B : pred_ty \<sigma>"
    using has_type.Lam[OF B] by (simp only: pred_ty_def)
  have first: "beta_eta_equiv \<Gamma> Prop
    (App (App (C_UI_absorb_left \<sigma>) (Lam \<sigma> B)) T)
    (Disj (App (Lam \<sigma> B) T) (Forall \<sigma> (App (shift (Lam \<sigma> B)) (Var 0))))"
    using C_A2_binary_application_beta[OF body predicate_type T]
    by (simp add: C_UI_absorb_left_def subst0_def numeral_2_eq_2
      C_subst_twice_raised C_subst_raised C_remove_inserted_operation
      C_A2_subst_twice_lifted shift_def)
  have second: "beta_eta_equiv \<Gamma> Prop
    (Disj (App (Lam \<sigma> B) T) (Forall \<sigma> (App (shift (Lam \<sigma> B)) (Var 0))))
    (Disj (subst0 T B) (Forall \<sigma> B))"
    by (rule C_PC_beta_eta_Disj[OF C_UI_predicate_application_beta[OF B T]
      C_UI_quantified_predicate_beta[OF B]])
  show ?thesis by (rule beta_eta_equiv.Trans[OF first second])
qed

lemma C_UI_absorb_right_beta:
  assumes B: "\<sigma> # \<Gamma> \<turnstile> B : Prop" and T: "\<Gamma> \<turnstile> T : \<sigma>"
  shows "beta_eta_equiv \<Gamma> Prop
    (App (App (C_UI_absorb_right \<sigma>) (Lam \<sigma> B)) T) (subst0 T B)"
proof -
  have body: "\<sigma> # pred_ty \<sigma> # \<Gamma> \<turnstile> App (Var 1) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have predicate_type: "\<Gamma> \<turnstile> Lam \<sigma> B : pred_ty \<sigma>"
    using has_type.Lam[OF B] by (simp only: pred_ty_def)
  have first: "beta_eta_equiv \<Gamma> Prop
    (App (App (C_UI_absorb_right \<sigma>) (Lam \<sigma> B)) T) (App (Lam \<sigma> B) T)"
    using C_A2_binary_application_beta[OF body predicate_type T]
    by (simp add: C_UI_absorb_right_def subst0_def C_subst_raised C_remove_inserted_operation)
  show ?thesis by (rule beta_eta_equiv.Trans[OF first C_UI_predicate_application_beta[OF B T]])
qed

subsection \<open>Source operation replacement under the full vector\<close>

lemma C_A2_remove_parameter_under_binder:
  "subst (lift_subst (C_vector_lift_subst n (case_nat F Var)))
    (rename (lift_ren (C_vector_lift_ren n Suc)) B) = B"
  using C_vector_remove_inserted_parameter[where n="Suc n" and F=F and A=B]
  by (simp only: C_vector_lift_subst.simps C_vector_lift_ren.simps)

lemma C_UI_vector_absorption_context:
  assumes B: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> B : Prop" and T: "\<Delta> @ \<Gamma> \<turnstile> T : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (Forall \<sigma> B) (Disj (subst0 T B) (Forall \<sigma> B))))
    (C_abstract_prefix \<Delta> (Imp (Forall \<sigma> B) (subst0 T B)))"
proof -
  let ?K = "pred_ty \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
  let ?r = "C_vector_lift_ren (length \<Delta>) Suc"
  let ?U = "Forall \<sigma> B"
  let ?F = "Lam \<sigma> B"
  let ?M = "Imp (rename ?r ?U) (App (App (Var (length \<Delta>)) (rename ?r ?F)) (rename ?r T))"
  have U: "\<Delta> @ \<Gamma> \<turnstile> ?U : Prop" by (rule has_type.Forall[OF B])
  have F: "\<Delta> @ \<Gamma> \<turnstile> ?F : pred_ty \<sigma>"
    using has_type.Lam[OF B] by (simp only: pred_ty_def)
  have U': "\<Delta> @ (?K # \<Gamma>) \<turnstile> rename ?r ?U : Prop" by (rule C_vector_insert_parameter_type[OF U])
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
  have body: "\<Delta> @ (?K # \<Gamma>) \<turnstile> ?M : Prop" by (rule has_type.Imp[OF U' second_app])
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp ?U (App (App (C_UI_absorb_left \<sigma>) ?F) T)))
    (C_abstract_prefix \<Delta> (Imp ?U (App (App (C_UI_absorb_right \<sigma>) ?F) T)))"
    using C_vector_identity_context[OF C_UI_absorb_types(1) C_UI_absorb_types(2) body C_UI_absorb_identity]
    by (simp add: C_vector_remove_inserted_parameter C_vector_lift_subst_slot
      C_UI_absorb_raised C_A2_remove_parameter_under_binder)
  have left_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (Imp ?U (App (App (C_UI_absorb_left \<sigma>) ?F) T))
    (Imp ?U (Disj (subst0 T B) ?U))"
    by (rule C_PC_beta_eta_Imp[OF beta_eta_equiv.Refl[OF U] C_UI_absorb_left_beta[OF B T]])
  have right_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (Imp ?U (App (App (C_UI_absorb_right \<sigma>) ?F) T)) (Imp ?U (subst0 T B))"
    by (rule C_PC_beta_eta_Imp[OF beta_eta_equiv.Refl[OF U] C_UI_absorb_right_beta[OF B T]])
  show ?thesis by (rule C_A1_transport[OF raw C_vector_conversion_identity[OF left_conversion]
    C_vector_conversion_identity[OF right_conversion]])
qed

theorem C_A2_UI_vector_truth:
  assumes B: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> B : Prop" and T: "\<Delta> @ \<Gamma> \<turnstile> T : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (Forall \<sigma> B) (subst0 T B))) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  have U: "\<Delta> @ \<Gamma> \<turnstile> Forall \<sigma> B : Prop" by (rule has_type.Forall[OF B])
  have instance_type: "\<Delta> @ \<Gamma> \<turnstile> subst0 T B : Prop" by (rule subst0_preserves_typing[OF B T])
  have formula_type: "\<Delta> @ \<Gamma> \<turnstile> Imp (Forall \<sigma> B)
    (Disj (subst0 T B) (Forall \<sigma> B)) : Prop"
    by (rule has_type.Imp[OF U has_type.Disj[OF instance_type U]])
  have PC: "prop_tautology (\<Delta> @ \<Gamma>)
    (Imp (Forall \<sigma> B) (Disj (subst0 T B) (Forall \<sigma> B)))"
    unfolding prop_tautology_def by (rule conjI[OF formula_type]) simp
  show ?thesis by (rule C_A1_trans[OF C_A1_sym[OF C_UI_vector_absorption_context[OF B T]]
    C_PC_vector_abstraction[OF PC]])
qed

end
