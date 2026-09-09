theory Bacon_C_Boolean_Idempotence
  imports Bacon_C_PC_Material_Normalization
begin

section \<open>Distribution and idempotence beneath one abstraction\<close>

text \<open>
  Figure 3 distribution and dissolution yield
  ⊢C (λv.A ∧ A) = (λv.A) and ⊢C (λv.A ∨ A) = (λv.A).
  Source use: Bacon--Dorr Figure 3, p.10, and Appendix A.2(i), p.65.
  Isabelle representation.  Three-argument operation identities are
  replaced beneath λ, then reduced by typed contextual β conversion.
  Status.  These are C-only normalization laws, not full Boolean
  equational completeness or an unrestricted abstraction rule.
\<close>

lemma C_ternary_beta_equiv:
  assumes P: "Prop # Prop # Prop # \<Gamma> \<turnstile> P : Prop"
    and A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and C: "\<Gamma> \<turnstile> C : Prop"
  shows "beta_eta_equiv \<Gamma> Prop
    (App (App (App (Lam Prop (Lam Prop (Lam Prop P))) A) B) C)
    (subst0 C (subst (lift_subst (case_nat B Var))
      (subst (lift_subst (lift_subst (case_nat A Var))) P)))"
proof -
  let ?F = "Lam Prop (Lam Prop (Lam Prop P))"
  let ?Q = "subst (lift_subst (lift_subst (case_nat A Var))) P"
  let ?X = "Lam Prop (Lam Prop ?Q)"
  let ?L = "App (App (App ?F A) B) C"
  let ?M = "App (App ?X B) C"
  have inner: "Prop # \<Gamma> \<turnstile> Lam Prop (Lam Prop P) :
    Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop" by (intro has_type.Lam P)
  have F: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Lam[OF inner])
  have FA: "\<Gamma> \<turnstile> App ?F A : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (rule has_type.App[OF F A])
  have FAB: "\<Gamma> \<turnstile> App (App ?F A) B : Prop \<rightarrow>\<^sub>o Prop"
    by (rule has_type.App[OF FA B])
  have L: "\<Gamma> \<turnstile> ?L : Prop" by (rule has_type.App[OF FAB C])
  have X: "\<Gamma> \<turnstile> ?X : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    using subst0_preserves_typing[OF inner A] by (simp add: subst0_def)
  have Q: "Prop # Prop # \<Gamma> \<turnstile> ?Q : Prop"
    using X by (auto elim: has_type.cases)
  have XB: "\<Gamma> \<turnstile> App ?X B : Prop \<rightarrow>\<^sub>o Prop"
    by (rule has_type.App[OF X B])
  have M: "\<Gamma> \<turnstile> ?M : Prop" by (rule has_type.App[OF XB C])
  have root_step: "compatible_step beta_contract (App ?F A) ?X"
  proof -
    have "compatible_step beta_contract (App ?F A)
      (subst0 A (Lam Prop (Lam Prop P)))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis by (simp add: subst0_def)
  qed
  have step: "compatible_step beta_contract ?L ?M"
    by (rule compatible_step.App_left[OF compatible_step.App_left[OF root_step]])
  show ?thesis by (rule beta_eta_equiv.Trans[OF beta_eta_equiv.Beta[OF L M step]
    C_binary_beta_equiv[OF Q B C]])
qed

lemma C_ternary_lambda_beta:
  assumes P: "Prop # Prop # Prop # \<Gamma> \<turnstile> P : Prop"
    and A: "\<tau> # \<Gamma> \<turnstile> A : Prop" and B: "\<tau> # \<Gamma> \<turnstile> B : Prop"
    and C: "\<tau> # \<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (App (App (App (shift (Lam Prop (Lam Prop (Lam Prop P)))) A) B) C))
    (Lam \<tau> (subst0 C (subst (lift_subst (case_nat B Var))
      (subst (lift_subst (lift_subst (case_nat A Var)))
        (rename (lift_ren (lift_ren (lift_ren Suc))) P)))))"
proof -
  let ?F = "Lam Prop (Lam Prop (Lam Prop P))"
  let ?P = "rename (lift_ren (lift_ren (lift_ren Suc))) P"
  have F: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (intro has_type.Lam P)
  have shifted: "\<tau> # \<Gamma> \<turnstile> shift ?F :
    Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (rule weakening_front[OF F])
  have body: "Prop # Prop # Prop # \<tau> # \<Gamma> \<turnstile> ?P : Prop"
    using shifted unfolding shift_def by (auto elim: has_type.cases)
  have conversion: "beta_eta_equiv (\<tau> # \<Gamma>) Prop
    (App (App (App (shift ?F) A) B) C)
    (subst0 C (subst (lift_subst (case_nat B Var))
      (subst (lift_subst (lift_subst (case_nat A Var))) ?P)))"
    using C_ternary_beta_equiv[OF body A B C] by (simp add: shift_def)
  show ?thesis by (rule C_closure_beta_eta_identity[OF C_beta_eta_Lam[OF conversion]])
qed

lemma C_ternary_lambda_identity_instance:
  assumes P: "Prop # Prop # Prop # \<Gamma> \<turnstile> P : Prop"
    and Q: "Prop # Prop # Prop # \<Gamma> \<turnstile> Q : Prop"
    and A: "\<tau> # \<Gamma> \<turnstile> A : Prop" and B: "\<tau> # \<Gamma> \<turnstile> B : Prop"
    and C: "\<tau> # \<Gamma> \<turnstile> C : Prop"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq
      (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
      (Lam Prop (Lam Prop (Lam Prop P))) (Lam Prop (Lam Prop (Lam Prop Q)))"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (subst0 C (subst (lift_subst (case_nat B Var))
      (subst (lift_subst (lift_subst (case_nat A Var)))
        (rename (lift_ren (lift_ren (lift_ren Suc))) P)))))
    (Lam \<tau> (subst0 C (subst (lift_subst (case_nat B Var))
      (subst (lift_subst (lift_subst (case_nat A Var)))
        (rename (lift_ren (lift_ren (lift_ren Suc))) Q)))))"
proof -
  let ?ty = "Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
  let ?F = "Lam Prop (Lam Prop (Lam Prop P))"
  let ?G = "Lam Prop (Lam Prop (Lam Prop Q))"
  let ?A = "rename (lift_ren Suc) A"
  let ?B = "rename (lift_ren Suc) B"
  let ?C = "rename (lift_ren Suc) C"
  let ?K = "Lam \<tau> (App (App (App (Var 1) ?A) ?B) ?C)"
  have F: "\<Gamma> \<turnstile> ?F : ?ty" by (intro has_type.Lam P)
  have G: "\<Gamma> \<turnstile> ?G : ?ty" by (intro has_type.Lam Q)
  have A': "\<tau> # ?ty # \<Gamma> \<turnstile> ?A : Prop" by (rule C_insert_after_binder_type[OF A])
  have B': "\<tau> # ?ty # \<Gamma> \<turnstile> ?B : Prop" by (rule C_insert_after_binder_type[OF B])
  have C': "\<tau> # ?ty # \<Gamma> \<turnstile> ?C : Prop" by (rule C_insert_after_binder_type[OF C])
  have operator: "\<tau> # ?ty # \<Gamma> \<turnstile> Var 1 : ?ty" by (rule has_type.Var) simp
  have first: "\<tau> # ?ty # \<Gamma> \<turnstile> App (Var 1) ?A : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (rule has_type.App[OF operator A'])
  have second: "\<tau> # ?ty # \<Gamma> \<turnstile> App (App (Var 1) ?A) ?B : Prop \<rightarrow>\<^sub>o Prop"
    by (rule has_type.App[OF first B'])
  have third: "\<tau> # ?ty # \<Gamma> \<turnstile> App (App (App (Var 1) ?A) ?B) ?C : Prop"
    by (rule has_type.App[OF second C'])
  have K: "?ty # \<Gamma> \<turnstile> ?K : \<tau> \<rightarrow>\<^sub>o Prop" by (rule has_type.Lam[OF third])
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop) (subst0 ?F ?K) (subst0 ?G ?K)"
    by (rule C_closure_congruence[OF F G K identity])
  have replaced: "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (App (App (App (shift ?F) A) B) C))
    (Lam \<tau> (App (App (App (shift ?G) A) B) C))"
    using raw by (simp add: subst0_def C_remove_inserted_operation shift_def)
  show ?thesis by (rule C_A1_transport[OF replaced C_ternary_lambda_beta[OF P A B C]
    C_ternary_lambda_beta[OF Q A B C]])
qed

subsection \<open>Figure 3 distribution and dual dissolution\<close>

lemma C_boolean_lambda_conj_distributes:
  assumes A: "\<tau> # \<Gamma> \<turnstile> A : Prop" and B: "\<tau> # \<Gamma> \<turnstile> B : Prop"
    and C: "\<tau> # \<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Conj A (Disj B C))) (Lam \<tau> (Disj (Conj A B) (Conj A C)))"
proof -
  let ?P = "Conj (Var 2) (Disj (Var 1) (Var 0))"
  let ?Q = "Disj (Conj (Var 2) (Var 1)) (Conj (Var 2) (Var 0))"
  have P: "Prop # Prop # Prop # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # Prop # \<Gamma> \<turnstile> ?Q : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have axiom: "\<Gamma> \<turnstile>\<^sub>C bool_dist_conj_disj"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq
    (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
    (Lam Prop (Lam Prop (Lam Prop ?P))) (Lam Prop (Lam Prop (Lam Prop ?Q)))"
    using axiom by (simp only: bool_dist_conj_disj_def)
  show ?thesis using C_ternary_lambda_identity_instance[OF P Q A B C identity]
    by (simp add: subst0_def numeral_2_eq_2 C_lifted_subst_var_two
      C_ternary_subst_first C_subst_twice_raised C_subst_raised)
qed

lemma C_boolean_lambda_disj_distributes:
  assumes A: "\<tau> # \<Gamma> \<turnstile> A : Prop" and B: "\<tau> # \<Gamma> \<turnstile> B : Prop"
    and C: "\<tau> # \<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Disj A (Conj B C))) (Lam \<tau> (Conj (Disj A B) (Disj A C)))"
proof -
  let ?P = "Disj (Var 2) (Conj (Var 1) (Var 0))"
  let ?Q = "Conj (Disj (Var 2) (Var 1)) (Disj (Var 2) (Var 0))"
  have P: "Prop # Prop # Prop # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # Prop # \<Gamma> \<turnstile> ?Q : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have axiom: "\<Gamma> \<turnstile>\<^sub>C bool_dist_disj_conj"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq
    (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
    (Lam Prop (Lam Prop (Lam Prop ?P))) (Lam Prop (Lam Prop (Lam Prop ?Q)))"
    using axiom by (simp only: bool_dist_disj_conj_def)
  show ?thesis using C_ternary_lambda_identity_instance[OF P Q A B C identity]
    by (simp add: subst0_def numeral_2_eq_2 C_lifted_subst_var_two
      C_ternary_subst_first C_subst_twice_raised C_subst_raised)
qed

lemma C_boolean_lambda_disj_dissolves:
  assumes A: "\<tau> # \<Gamma> \<turnstile> A : Prop" and B: "\<tau> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Disj A (Conj B (Neg B)))) (Lam \<tau> A)"
proof -
  let ?P = "Disj (Var 1) (Conj (Var 0) (Neg (Var 0)))"
  have P: "Prop # Prop # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # \<Gamma> \<turnstile> Var 1 : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have axiom: "\<Gamma> \<turnstile>\<^sub>C bool_dissolve_disj_conj"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty
    (Lam Prop (Lam Prop ?P)) (Lam Prop (Lam Prop (Var 1)))"
    using axiom by (simp only: bool_dissolve_disj_conj_def)
  show ?thesis using C_binary_lambda_identity_instance[OF P Q A B identity]
    by (simp add: subst0_def C_subst_raised)
qed

subsection \<open>Repeated-branch normalization\<close>

text \<open>
  A ∧ (A ∨ ¬A) = A, while distribution and dissolution identify
  the same left side with A ∧ A.  The dual calculation gives A ∨ A = A.
  Isabelle representation.  Every intermediate equation is at σ → t.
  Status.  The full six Figure 3 identities are now available beneath
  one λ; associativity, negation normalization, and general PC
  equational completeness still require proofs.
\<close>

theorem C_boolean_lambda_conj_idempotent:
  assumes A: "\<tau> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Conj A A)) (Lam \<tau> A)"
proof -
  have negation: "\<tau> # \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have repeated: "\<tau> # \<Gamma> \<turnstile> Conj A A : Prop" by (rule has_type.Conj[OF A A])
  have distribution: "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Conj A (Disj A (Neg A))))
    (Lam \<tau> (Disj (Conj A A) (Conj A (Neg A))))"
    by (rule C_boolean_lambda_conj_distributes[OF A A negation])
  have to_repeat: "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Conj A (Disj A (Neg A)))) (Lam \<tau> (Conj A A))"
    by (rule C_A1_trans[OF distribution C_boolean_lambda_disj_dissolves[OF repeated A]])
  show ?thesis by (rule C_A1_trans[OF C_A1_sym[OF to_repeat]
    C_boolean_lambda_conj_dissolves[OF A A]])
qed

theorem C_boolean_lambda_disj_idempotent:
  assumes A: "\<tau> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Disj A A)) (Lam \<tau> A)"
proof -
  have negation: "\<tau> # \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have repeated: "\<tau> # \<Gamma> \<turnstile> Disj A A : Prop" by (rule has_type.Disj[OF A A])
  have distribution: "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Disj A (Conj A (Neg A))))
    (Lam \<tau> (Conj (Disj A A) (Disj A (Neg A))))"
    by (rule C_boolean_lambda_disj_distributes[OF A A negation])
  have to_repeat: "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Disj A (Conj A (Neg A)))) (Lam \<tau> (Disj A A))"
    by (rule C_A1_trans[OF distribution C_boolean_lambda_conj_dissolves[OF repeated A]])
  show ?thesis by (rule C_A1_trans[OF C_A1_sym[OF to_repeat]
    C_boolean_lambda_disj_dissolves[OF A A]])
qed

end
