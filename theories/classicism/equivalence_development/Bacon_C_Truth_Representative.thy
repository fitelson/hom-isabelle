theory Bacon_C_Truth_Representative
  imports Bacon_C_Boolean_Abstraction
begin

section \<open>Identifying the two truth representatives in axiom-based C\<close>

text \<open>
  Put ⊤₀ := ∀p.(p → p) and ⊤ᴮ := ⊤₀ ∨ ¬⊤₀.  We derive
  ⊢C ⊤ᴮ =ₜ ⊤₀.  Source use: Bacon--Dorr Figure 3 and Appendix
  A.2(i), p.65, together with Figure 4 distribution and Proposition A.1.
  This bridges the implementation's primitive-implication abbreviation
  with its Boolean truth representative; it is not a new source axiom.

  Isabelle representation.  ObjTrue and C_boolean_truth denote ⊤₀ and
  ⊤ᴮ.  Identities beneath λ come from closed operation identities and
  typed context replacement, never from an unrestricted abstraction rule.
  Status.  Only axiom-based C is used.  General PC/vector normalization
  and the remainder of Proposition A.2 are not asserted.
\<close>

subsection \<open>Reversed excluded middle and self-implication beneath λ\<close>

lemma C_boolean_lambda_disj_commutes:
  assumes A: "\<tau> # \<Gamma> \<turnstile> A : Prop" and B: "\<tau> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Disj A B)) (Lam \<tau> (Disj B A))"
proof -
  have P: "Prop # Prop # \<Gamma> \<turnstile> Disj (Var 1) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # \<Gamma> \<turnstile> Disj (Var 0) (Var 1) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have axiom: "\<Gamma> \<turnstile>\<^sub>C bool_comm_disj"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty
    (Lam Prop (Lam Prop (Disj (Var 1) (Var 0))))
    (Lam Prop (Lam Prop (Disj (Var 0) (Var 1))))"
    using axiom by (simp only: bool_comm_disj_def)
  show ?thesis using C_binary_lambda_identity_instance[OF P Q A B identity]
    by (simp add: subst0_def C_subst_raised)
qed

lemma C_boolean_reversed_excluded_middle_predicate_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq (Prop \<rightarrow>\<^sub>o Prop)
    (Lam Prop (Disj (Neg (Var 0)) (Var 0))) (Lam Prop (shift C_boolean_truth))"
proof -
  have variable: "Prop # \<Gamma> \<turnstile> Var 0 : Prop" by (rule has_type.Var) simp
  have negation: "Prop # \<Gamma> \<turnstile> Neg (Var 0) : Prop"
    by (rule has_type.Neg[OF variable])
  have comm: "\<Gamma> \<turnstile>\<^sub>C Eq (Prop \<rightarrow>\<^sub>o Prop)
    (Lam Prop (Disj (Neg (Var 0)) (Var 0)))
    (Lam Prop (Disj (Var 0) (Neg (Var 0))))"
    by (rule C_boolean_lambda_disj_commutes[OF negation variable])
  show ?thesis by (rule C_A1_trans[OF comm C_boolean_excluded_middle_predicate_truth])
qed

lemma C_boolean_lambda_self_implication_material:
  assumes A: "\<tau> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Imp A A)) (Lam \<tau> (Disj (Neg A) A))"
proof -
  have P: "Prop # Prop # \<Gamma> \<turnstile> Imp (Var 1) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # \<Gamma> \<turnstile> Disj (Neg (Var 1)) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  show ?thesis using C_binary_lambda_identity_instance[OF P Q A A
      C_closure_material_imp_operator]
    by (simp add: subst0_def C_subst_raised)
qed

lemma C_boolean_self_implication_predicate_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq (Prop \<rightarrow>\<^sub>o Prop)
    (Lam Prop (Imp (Var 0) (Var 0))) (Lam Prop (shift C_boolean_truth))"
proof -
  have variable: "Prop # \<Gamma> \<turnstile> Var 0 : Prop" by (rule has_type.Var) simp
  show ?thesis by (rule C_A1_trans[OF C_boolean_lambda_self_implication_material[OF variable]
    C_boolean_reversed_excluded_middle_predicate_truth])
qed

lemma C_ObjTrue_quantified_Boolean_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop ObjTrue (Forall Prop (shift C_boolean_truth))"
proof -
  have body: "Prop # \<Gamma> \<turnstile> Imp (Var 0) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have truth: "Prop # \<Gamma> \<turnstile> shift C_boolean_truth : Prop"
    by (rule weakening_front[OF C_boolean_truth_type])
  show ?thesis using C_forall_of_predicate_identity[OF body truth
      C_boolean_self_implication_predicate_truth]
    by (simp only: ObjTrue_def)
qed

subsection \<open>Distribution for the constant truth predicate\<close>

text \<open>
  Put U := ¬⊤₀ ∨ ⊤₀.  Distribution gives
  ¬⊤₀ ∨ (∀x:σ.⊤₀) =ₜ ∀x:σ.(¬⊤₀ ∨ ⊤₀).
  A.1 reduces the left side to U; hence ⊢C (∀x:σ.U) =ₜ U.

  Isabelle representation.  The source identity is first applied to
  λx:σ.⊤₀ and ¬⊤₀, with every application reduced by contextual β.
  Status.  This proves the constant Boolean-truth calculation without
  presupposing ⊤ᴮ =ₜ ⊤₀.
\<close>

lemma C_truth_representative_distribution:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Disj (Neg ObjTrue) (Forall \<sigma> (App (Lam \<sigma> ObjTrue) (Var 0))))
    (Forall \<sigma> (Disj (Neg ObjTrue) (App (Lam \<sigma> ObjTrue) (Var 0))))"
proof -
  let ?P = "Disj (Var 0) (Forall \<sigma> (App (Var 2) (Var 0)))"
  let ?Q = "Forall \<sigma> (Disj (Var 1) (App (Var 2) (Var 0)))"
  have P: "Prop # pred_ty \<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: lookup_def pred_ty_def)
  have Q: "Prop # pred_ty \<sigma> # \<Gamma> \<turnstile> ?Q : Prop"
    by (rule infer_type_sound) (simp add: lookup_def pred_ty_def)
  have X: "\<Gamma> \<turnstile> Lam \<sigma> ObjTrue : pred_ty \<sigma>"
    unfolding pred_ty_def by (intro has_type.Lam typed_ObjTrue)
  have negation: "\<Gamma> \<turnstile> Neg ObjTrue : Prop"
    by (rule has_type.Neg[OF typed_ObjTrue])
  have eq: "\<Gamma> \<turnstile>\<^sub>C Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
    (Lam (pred_ty \<sigma>) (Lam Prop ?P)) (Lam (pred_ty \<sigma>) (Lam Prop ?Q))"
    using C_proves.DistDisjForall[of \<Gamma> \<sigma>]
    by (simp add: classic_dist_disj_forall_def)
  show ?thesis using C_A1_binary_instance[OF P Q X negation eq]
    by (simp add: subst0_def numeral_2_eq_2 ObjTrue_def)
qed

lemma C_truth_representative_quantified_beta:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Forall \<sigma> (Disj (Neg ObjTrue) (App (Lam \<sigma> ObjTrue) (Var 0))))
    (Forall \<sigma> (Disj (Neg ObjTrue) ObjTrue))"
proof -
  have variable: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  have predicate: "\<sigma> # \<Gamma> \<turnstile> Lam \<sigma> ObjTrue : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (intro has_type.Lam typed_ObjTrue)
  have app: "\<sigma> # \<Gamma> \<turnstile> App (Lam \<sigma> ObjTrue) (Var 0) : Prop"
    by (rule has_type.App[OF predicate variable])
  have negation: "\<sigma> # \<Gamma> \<turnstile> Neg ObjTrue : Prop"
    by (rule has_type.Neg[OF typed_ObjTrue])
  have L: "\<sigma> # \<Gamma> \<turnstile> Disj (Neg ObjTrue) (App (Lam \<sigma> ObjTrue) (Var 0)) : Prop"
    by (rule has_type.Disj[OF negation app])
  have R: "\<sigma> # \<Gamma> \<turnstile> Disj (Neg ObjTrue) ObjTrue : Prop"
    by (rule has_type.Disj[OF negation typed_ObjTrue])
  have root: "compatible_step beta_contract
    (App (Lam \<sigma> ObjTrue) (Var 0)) ObjTrue"
  proof -
    have "compatible_step beta_contract (App (Lam \<sigma> ObjTrue) (Var 0))
      (subst0 (Var 0) ObjTrue)"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis by (simp add: subst0_def ObjTrue_def)
  qed
  have step: "compatible_step beta_contract
    (Disj (Neg ObjTrue) (App (Lam \<sigma> ObjTrue) (Var 0)))
    (Disj (Neg ObjTrue) ObjTrue)"
    by (rule compatible_step.Disj_right[OF root])
  show ?thesis by (rule C_forall_beta_step_identity[OF L R step])
qed

lemma C_forall_reversed_Boolean_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Forall \<sigma> (Disj (Neg ObjTrue) ObjTrue)) (Disj (Neg ObjTrue) ObjTrue)"
proof -
  let ?F = "Forall \<sigma> (App (Lam \<sigma> ObjTrue) (Var 0))"
  let ?U = "Disj (Neg ObjTrue) ObjTrue"
  have beta: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?F (Forall \<sigma> ObjTrue)"
    using C_forall_predicate_beta[OF typed_ObjTrue, where \<sigma> = \<sigma> and \<Gamma> = \<Gamma>]
    by (simp add: shift_def ObjTrue_def)
  have A1: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall \<sigma> ObjTrue) ObjTrue"
    using C_Appendix_A1_universal_truth[of \<Gamma> \<sigma>] by simp
  have F_truth: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?F ObjTrue"
    by (rule C_A1_trans[OF beta A1])
  have neg_ref: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Neg ObjTrue) (Neg ObjTrue)"
    by (intro C_proves.H H_proves.Ref has_type.Neg typed_ObjTrue)
  have left_norm: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj (Neg ObjTrue) ?F) ?U"
    by (rule C_A1_disj_congruence[OF neg_ref F_truth])
  have eq: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?U (Forall \<sigma> ?U)"
    by (rule C_A1_transport[OF C_truth_representative_distribution
      left_norm C_truth_representative_quantified_beta])
  show ?thesis by (rule C_A1_sym[OF eq])
qed

lemma C_forall_Boolean_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall \<sigma> (shift C_boolean_truth)) C_boolean_truth"
proof -
  have negation: "\<Gamma> \<turnstile> Neg ObjTrue : Prop"
    by (rule has_type.Neg[OF typed_ObjTrue])
  have comm: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj (Neg ObjTrue) ObjTrue) C_boolean_truth"
    using C_boolean_disj_commutes[OF negation typed_ObjTrue]
    by (simp only: C_boolean_truth_def)
  have quantified: "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Forall \<sigma> (Disj (Neg ObjTrue) ObjTrue)) (Forall \<sigma> (shift C_boolean_truth))"
    using C_A1_forall_constant_congruence[OF comm, where \<sigma> = \<sigma>]
    by (simp add: shift_def ObjTrue_def)
  show ?thesis by (rule C_A1_transport[OF C_forall_reversed_Boolean_truth quantified comm])
qed

text \<open>
  Since ⊢C (λp.p → p) = (λp.⊤ᴮ), predicate congruence gives
  ⊢C ⊤₀ =ₜ ∀p.⊤ᴮ.  The constant calculation yields ⊤₀ =ₜ ⊤ᴮ.
  Source location: the Boolean normalization obligation in Appendix A.2(i).
  Status.  This closes the particular truth-representative bridge only;
  it does not prove arbitrary tautologies identical to truth beneath λv̄.
\<close>

theorem C_boolean_truth_eq_ObjTrue:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop C_boolean_truth ObjTrue"
proof -
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ObjTrue C_boolean_truth"
    by (rule C_A1_trans[OF C_ObjTrue_quantified_Boolean_truth C_forall_Boolean_truth])
  show ?thesis by (rule C_A1_sym[OF identity])
qed

end
