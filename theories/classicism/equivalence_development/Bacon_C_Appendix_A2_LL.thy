theory Bacon_C_Appendix_A2_LL
  imports Bacon_C_Appendix_A2_Ref_Vector Bacon_C_Appendix_A2_MP
begin

section \<open>Appendix A.2: Leibniz's law beneath an arbitrary vector\<close>

text \<open>
  Identity Identity represents M =σ N as ∀G:σ→t.(GM ↔ GN).
  UI with G := F gives the implication from that universal formula to
  FM ↔ FN.  Vector PC and the proved vector MP step then give
  ∀G.(GM ↔ GN) → (FM → FN).  Replacing the source identity operation
  in the antecedent yields the literal LL formula.
  Sources: Bacon--Dorr Figure 2 LL/UI, p.8; Figure 4 Identity Identity,
  p.13; the corresponding cases of Proposition A.2, pp.65–67.

  Isabelle representation.  M, N, and F may depend on all variables in Δ.
  The matrix below shifts M and N beneath the quantified predicate G.
  Status.  This is an axiom-based C derivation of LL-to-truth at vector
  generality, not an assumed Equivalence or theorem-to-truth principle.
\<close>

definition C_LL_matrix :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_LL_matrix M N = (App (Var 0) (shift M) \<longleftrightarrow>\<^sub>o App (Var 0) (shift N))"

lemma C_LL_matrix_type:
  assumes M: "\<Gamma> \<turnstile> M : \<sigma>" and N: "\<Gamma> \<turnstile> N : \<sigma>"
  shows "pred_ty \<sigma> # \<Gamma> \<turnstile> C_LL_matrix M N : Prop"
proof -
  have SM: "pred_ty \<sigma> # \<Gamma> \<turnstile> shift M : \<sigma>" by (rule weakening_front[OF M])
  have SN: "pred_ty \<sigma> # \<Gamma> \<turnstile> shift N : \<sigma>" by (rule weakening_front[OF N])
  have variable: "pred_ty \<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have GM: "pred_ty \<sigma> # \<Gamma> \<turnstile> App (Var 0) (shift M) : Prop"
    by (rule has_type.App[OF variable SM])
  have GN: "pred_ty \<sigma> # \<Gamma> \<turnstile> App (Var 0) (shift N) : Prop"
    by (rule has_type.App[OF variable SN])
  show ?thesis unfolding C_LL_matrix_def by (intro has_type.Conj has_type.Imp GM GN)
qed

lemma C_LL_identity_left_beta:
  assumes M: "\<Gamma> \<turnstile> M : \<sigma>" and N: "\<Gamma> \<turnstile> N : \<sigma>"
  shows "beta_eta_equiv \<Gamma> Prop
    (App (App (C_Ref_identity_left \<sigma>) M) N) (Eq \<sigma> M N)"
proof -
  have body: "\<sigma> # \<sigma> # \<Gamma> \<turnstile> Eq \<sigma> (Var 1) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  show ?thesis using C_A2_binary_application_beta[OF body M N]
    by (simp add: C_Ref_identity_left_def subst0_def C_subst_raised)
qed

lemma C_LL_identity_right_beta:
  assumes M: "\<Gamma> \<turnstile> M : \<sigma>" and N: "\<Gamma> \<turnstile> N : \<sigma>"
  shows "beta_eta_equiv \<Gamma> Prop
    (App (App (C_Ref_identity_right \<sigma>) M) N) (Forall (pred_ty \<sigma>) (C_LL_matrix M N))"
proof -
  have body: "\<sigma> # \<sigma> # \<Gamma> \<turnstile> Forall (pred_ty \<sigma>)
    (App (Var 0) (Var 2) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)) : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  show ?thesis using C_A2_binary_application_beta[OF body M N]
    by (simp add: C_Ref_identity_right_def C_LL_matrix_def subst0_def shift_def
      numeral_2_eq_2 C_subst_twice_raised C_subst_raised)
qed

subsection \<open>The quantified version follows from UI and propositional reasoning\<close>

lemma C_LL_quantified_vector_truth:
  assumes M: "\<Delta> @ \<Gamma> \<turnstile> M : \<sigma>" and N: "\<Delta> @ \<Gamma> \<turnstile> N : \<sigma>"
    and F: "\<Delta> @ \<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (Forall (pred_ty \<sigma>) (C_LL_matrix M N))
      (Imp (App F M) (App F N)))) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  let ?U = "Forall (pred_ty \<sigma>) (C_LL_matrix M N)"
  let ?P = "App F M"
  let ?Q = "App F N"
  have matrix: "pred_ty \<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> C_LL_matrix M N : Prop"
    by (rule C_LL_matrix_type[OF M N])
  have predicate_type: "\<Delta> @ \<Gamma> \<turnstile> F : pred_ty \<sigma>"
    using F by (simp only: pred_ty_def)
  have UI: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp ?U (?P \<longleftrightarrow>\<^sub>o ?Q))) (C_abstract_prefix \<Delta> ObjTrue)"
    using C_A2_UI_vector_truth[OF matrix predicate_type]
    by (simp add: C_LL_matrix_def subst0_def shift_def C_subst_raised)
  have U: "\<Delta> @ \<Gamma> \<turnstile> ?U : Prop" by (rule has_type.Forall[OF matrix])
  have P: "\<Delta> @ \<Gamma> \<turnstile> ?P : Prop" by (rule has_type.App[OF F M])
  have Q: "\<Delta> @ \<Gamma> \<turnstile> ?Q : Prop" by (rule has_type.App[OF F N])
  have formula_type: "\<Delta> @ \<Gamma> \<turnstile>
    Imp (Imp ?U (?P \<longleftrightarrow>\<^sub>o ?Q)) (Imp ?U (Imp ?P ?Q)) : Prop"
    by (intro has_type.Imp has_type.Conj U P Q)
  have PC: "prop_tautology (\<Delta> @ \<Gamma>)
    (Imp (Imp ?U (?P \<longleftrightarrow>\<^sub>o ?Q)) (Imp ?U (Imp ?P ?Q)))"
    unfolding prop_tautology_def by (rule conjI[OF formula_type]) auto
  show ?thesis by (rule C_A2_MP_vector[OF UI C_PC_vector_abstraction[OF PC]])
qed

subsection \<open>Replacing Identity Identity in the LL antecedent\<close>

lemma C_LL_vector_identity_context:
  assumes M: "\<Delta> @ \<Gamma> \<turnstile> M : \<sigma>" and N: "\<Delta> @ \<Gamma> \<turnstile> N : \<sigma>"
    and F: "\<Delta> @ \<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (Eq \<sigma> M N) (Imp (App F M) (App F N))))
    (C_abstract_prefix \<Delta> (Imp (Forall (pred_ty \<sigma>) (C_LL_matrix M N))
      (Imp (App F M) (App F N))))"
proof -
  let ?K = "\<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
  let ?r = "C_vector_lift_ren (length \<Delta>) Suc"
  let ?Q = "Imp (App F M) (App F N)"
  let ?body = "Imp (App (App (Var (length \<Delta>)) (rename ?r M)) (rename ?r N)) (rename ?r ?Q)"
  have FM: "\<Delta> @ \<Gamma> \<turnstile> App F M : Prop" by (rule has_type.App[OF F M])
  have FN: "\<Delta> @ \<Gamma> \<turnstile> App F N : Prop" by (rule has_type.App[OF F N])
  have Q: "\<Delta> @ \<Gamma> \<turnstile> ?Q : Prop" by (rule has_type.Imp[OF FM FN])
  have M': "\<Delta> @ (?K # \<Gamma>) \<turnstile> rename ?r M : \<sigma>" by (rule C_vector_insert_parameter_type[OF M])
  have N': "\<Delta> @ (?K # \<Gamma>) \<turnstile> rename ?r N : \<sigma>" by (rule C_vector_insert_parameter_type[OF N])
  have Q': "\<Delta> @ (?K # \<Gamma>) \<turnstile> rename ?r ?Q : Prop" by (rule C_vector_insert_parameter_type[OF Q])
  have base_index: "lookup (?K # \<Gamma>) 0 = Some ?K" by simp
  have index: "lookup (\<Delta> @ (?K # \<Gamma>)) (length \<Delta>) = Some ?K"
    using lookup_append_shift[OF base_index, where \<Delta>=\<Delta>] by simp
  have operator: "\<Delta> @ (?K # \<Gamma>) \<turnstile> Var (length \<Delta>) : ?K" by (rule has_type.Var[OF index])
  have first_app: "\<Delta> @ (?K # \<Gamma>) \<turnstile> App (Var (length \<Delta>)) (rename ?r M) : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.App[OF operator M'])
  have second_app: "\<Delta> @ (?K # \<Gamma>) \<turnstile>
    App (App (Var (length \<Delta>)) (rename ?r M)) (rename ?r N) : Prop"
    by (rule has_type.App[OF first_app N'])
  have body_type: "\<Delta> @ (?K # \<Gamma>) \<turnstile> ?body : Prop" by (rule has_type.Imp[OF second_app Q'])
  have left_raised: "C_vector_raise n (C_Ref_identity_left \<sigma>) = C_Ref_identity_left \<sigma>" for n
    by (induction n) (simp_all add: C_Ref_identity_rename)
  have right_raised: "C_vector_raise n (C_Ref_identity_right \<sigma>) = C_Ref_identity_right \<sigma>" for n
    by (induction n) (simp_all add: C_Ref_identity_rename)
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (App (App (C_Ref_identity_left \<sigma>) M) N) ?Q))
    (C_abstract_prefix \<Delta> (Imp (App (App (C_Ref_identity_right \<sigma>) M) N) ?Q))"
    using C_vector_identity_context[OF C_Ref_identity_types(1) C_Ref_identity_types(2)
      body_type C_Ref_identity_source]
    by (simp add: C_vector_remove_inserted_parameter C_vector_lift_subst_slot left_raised right_raised)
  have left_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (Imp (App (App (C_Ref_identity_left \<sigma>) M) N) ?Q) (Imp (Eq \<sigma> M N) ?Q)"
    by (rule C_PC_beta_eta_Imp[OF C_LL_identity_left_beta[OF M N] beta_eta_equiv.Refl[OF Q]])
  have right_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (Imp (App (App (C_Ref_identity_right \<sigma>) M) N) ?Q)
    (Imp (Forall (pred_ty \<sigma>) (C_LL_matrix M N)) ?Q)"
    by (rule C_PC_beta_eta_Imp[OF C_LL_identity_right_beta[OF M N] beta_eta_equiv.Refl[OF Q]])
  show ?thesis by (rule C_A1_transport[OF raw C_vector_conversion_identity[OF left_conversion]
    C_vector_conversion_identity[OF right_conversion]])
qed

theorem C_A2_LL_vector_truth:
  assumes M: "\<Delta> @ \<Gamma> \<turnstile> M : \<sigma>" and N: "\<Delta> @ \<Gamma> \<turnstile> N : \<sigma>"
    and F: "\<Delta> @ \<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Imp (Eq \<sigma> M N) (Imp (App F M) (App F N))))
    (C_abstract_prefix \<Delta> ObjTrue)"
  by (rule C_A1_trans[OF C_LL_vector_identity_context[OF M N F] C_LL_quantified_vector_truth[OF M N F]])

end
