theory Bacon_C_Boolean_Normalization
  imports Bacon_C_Boolean_Completeness
begin

section \<open>Concrete Boolean basis for Appendix A.2\<close>

text \<open>
  Figure 3 supplies operation identities whose applications yield
  A ∧ (B ∨ C) =ₜ (A ∧ B) ∨ (A ∧ C) and their duals, together with
  A ∧ (B ∨ ¬B) =ₜ A and A ∨ (B ∧ ¬B) =ₜ A.
  Source: Bacon--Dorr Figure 3, p.10; intended use: Appendix A.2(i), p.65.

  Isabelle representation.  The binary and ternary identities are
  instantiated by congruence and explicit β reductions.  We distinguish
  ⊤₀ := ∀p.(p → p), represented by ObjTrue, from
  ⊤ᴮ := ⊤₀ ∨ ¬⊤₀, represented by C_boolean_truth.

  Status.  These concrete equations are derived in C.  They are not a
  general normalization theorem, and ⊤ᴮ =ₜ ⊤₀ is not proved here.
\<close>

subsection \<open>Explicit substitution cancellation for three arguments\<close>

text \<open>
  The reductions of (λxλyλz.P) A B C must substitute A, B, and C
  without capturing variables.  Source use: Bacon--Dorr Figure 3, p.10,
  the two distribution operations.

  Isabelle representation.  These equalities concern rename, lift_subst,
  and subst0 on syntax trees, not object-language =σ.
  Status.  They justify the subsequent concrete β calculations.
\<close>

lemma C_subst_two_renamings:
  assumes "\<And>n. s (r (t n)) = Var (q n)"
  shows "subst s (rename r (rename t M)) = rename q M"
  using assms
proof (induction M arbitrary: s r t q)
  case (Lam \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren r) (rename (lift_ren t) M)) =
    rename (lift_ren q) M"
    by (rule Lam.IH) (case_tac n; simp add: Lam.prems)
  then show ?case by simp
next
  case (Forall \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren r) (rename (lift_ren t) M)) =
    rename (lift_ren q) M"
    by (rule Forall.IH) (case_tac n; simp add: Forall.prems)
  then show ?case by simp
next
  case (Exists \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren r) (rename (lift_ren t) M)) =
    rename (lift_ren q) M"
    by (rule Exists.IH) (case_tac n; simp add: Exists.prems)
  then show ?case by simp
qed (simp_all add: assms)

lemma C_subst_twice_raised:
  "subst (lift_subst (case_nat B Var)) (rename Suc (rename Suc A)) = rename Suc A"
  by (rule C_subst_two_renamings) simp

lemma C_subst_raised:
  "subst (case_nat B Var) (rename Suc A) = A"
  using subst0_shift[of B A] by (simp only: subst0_def shift_def)

lemma C_lifted_subst_var_two:
  "lift_subst (lift_subst (case_nat A Var)) 2 = rename Suc (rename Suc A)"
  by (simp add: numeral_2_eq_2)

lemma C_ternary_subst_first:
  "subst (case_nat C Var)
    (subst (lift_subst (case_nat B Var))
      (lift_subst (lift_subst (case_nat A Var)) 2)) = A"
  by (simp only: C_lifted_subst_var_two C_subst_twice_raised C_subst_raised)

subsection \<open>Three-argument operation identities\<close>

text \<open>
  From ⊢C (λpqr.P) = (λpqr.Q), derive
  ⊢C P[A/p,B/q,C/r] =ₜ Q[A/p,B/q,C/r].
  Source: Bacon--Dorr Figure 3, p.10, distribution.

  Isabelle representation.  The theorem applies the ternary operations and
  invokes the preceding substitution cancellations.
  Status.  The hypothesis is an operation identity, not pointwise equivalence.
\<close>

lemma C_ternary_operator_identity_instance:
  assumes P_type: "Prop # Prop # Prop # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "Prop # Prop # Prop # \<Gamma> \<turnstile> Q : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
    and identity: "\<Gamma> \<turnstile>\<^sub>C
      Eq (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
        (Lam Prop (Lam Prop (Lam Prop P))) (Lam Prop (Lam Prop (Lam Prop Q)))"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (subst0 C (subst (lift_subst (case_nat B Var))
      (subst (lift_subst (lift_subst (case_nat A Var))) P)))
    (subst0 C (subst (lift_subst (case_nat B Var))
      (subst (lift_subst (lift_subst (case_nat A Var))) Q)))"
proof -
  let ?PA = "subst (lift_subst (lift_subst (case_nat A Var))) P"
  let ?QA = "subst (lift_subst (lift_subst (case_nat A Var))) Q"
  let ?F = "Lam Prop (Lam Prop (Lam Prop P))"
  let ?G = "Lam Prop (Lam Prop (Lam Prop Q))"
  let ?X = "Lam Prop (Lam Prop ?PA)"
  let ?Y = "Lam Prop (Lam Prop ?QA)"
  have FP: "Prop # \<Gamma> \<turnstile> Lam Prop (Lam Prop P) : prop_bin_ty"
    unfolding prop_bin_ty_def by (intro has_type.Lam P_type)
  have GQ: "Prop # \<Gamma> \<turnstile> Lam Prop (Lam Prop Q) : prop_bin_ty"
    unfolding prop_bin_ty_def by (intro has_type.Lam Q_type)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o prop_bin_ty"
    by (rule has_type.Lam[OF FP])
  have G_type: "\<Gamma> \<turnstile> ?G : Prop \<rightarrow>\<^sub>o prop_bin_ty"
    by (rule has_type.Lam[OF GQ])
  have FA: "\<Gamma> \<turnstile> App ?F A : prop_bin_ty"
    using F_type A_type by auto
  have GA: "\<Gamma> \<turnstile> App ?G A : prop_bin_ty"
    using G_type A_type by auto
  have X_type: "\<Gamma> \<turnstile> ?X : prop_bin_ty"
    using subst0_preserves_typing[OF FP A_type] by (simp add: subst0_def)
  have Y_type: "\<Gamma> \<turnstile> ?Y : prop_bin_ty"
    using subst0_preserves_typing[OF GQ A_type] by (simp add: subst0_def)
  have PA_type: "Prop # Prop # \<Gamma> \<turnstile> ?PA : Prop"
    using X_type unfolding prop_bin_ty_def by (auto elim: has_type.cases)
  have QA_type: "Prop # Prop # \<Gamma> \<turnstile> ?QA : Prop"
    using Y_type unfolding prop_bin_ty_def by (auto elim: has_type.cases)
  have FG: "\<Gamma> \<turnstile>\<^sub>C Eq (Prop \<rightarrow>\<^sub>o prop_bin_ty) ?F ?G"
    using identity by (simp add: prop_bin_ty_def)
  have FA_GA: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty (App ?F A) (App ?G A)"
    by (rule C_closure_app_congruence_left[OF F_type G_type A_type FG])
  have step_F: "compatible_step beta_contract (App ?F A) ?X"
  proof -
    have "compatible_step beta_contract (App ?F A)
      (subst0 A (Lam Prop (Lam Prop P)))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis by (simp add: subst0_def)
  qed
  have step_G: "compatible_step beta_contract (App ?G A) ?Y"
  proof -
    have "compatible_step beta_contract (App ?G A)
      (subst0 A (Lam Prop (Lam Prop Q)))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis by (simp add: subst0_def)
  qed
  have FA_X: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty (App ?F A) ?X"
    by (rule C_closure_beta_identity[OF FA X_type step_F])
  have GA_Y: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty (App ?G A) ?Y"
    by (rule C_closure_beta_identity[OF GA Y_type step_G])
  have X_FA: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty ?X (App ?F A)"
    by (rule C_closure_eq_sym_from[OF FA X_type FA_X])
  have X_GA: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty ?X (App ?G A)"
    by (rule C_closure_eq_trans_from[OF X_type FA GA X_FA FA_GA])
  have XY: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty ?X ?Y"
    by (rule C_closure_eq_trans_from[OF X_type GA Y_type X_GA GA_Y])
  show ?thesis
    by (rule C_binary_operator_identity_instance[OF PA_type QA_type B_type C_type XY])
qed

subsection \<open>Figure 3: distribution\<close>

text \<open>
  ⊢C A ∧ (B ∨ C) =ₜ (A ∧ B) ∨ (A ∧ C), and
  ⊢C A ∨ (B ∧ C) =ₜ (A ∨ B) ∧ (A ∨ C).
  Source: Bacon--Dorr Figure 3, p.10, Distribution-∧∨ and Distribution-∨∧.

  Isabelle representation.  The closed BooleanIdentity members are applied
  to three typed propositions.
  Status.  Both conclusions are identities in C.
\<close>

lemma C_boolean_conj_distributes:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and C: "\<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Conj A (Disj B C))
    (Disj (Conj A B) (Conj A C))"
proof -
  let ?P = "Conj (Var 2) (Disj (Var 1) (Var 0))"
  let ?Q = "Disj (Conj (Var 2) (Var 1)) (Conj (Var 2) (Var 0))"
  have P: "Prop # Prop # Prop # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # Prop # \<Gamma> \<turnstile> ?Q : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have ax: "\<Gamma> \<turnstile>\<^sub>C bool_dist_conj_disj"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  have eq: "\<Gamma> \<turnstile>\<^sub>C
    Eq (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
      (Lam Prop (Lam Prop (Lam Prop ?P))) (Lam Prop (Lam Prop (Lam Prop ?Q)))"
    using ax by (simp add: bool_dist_conj_disj_def)
  show ?thesis using C_ternary_operator_identity_instance[OF P Q A B C eq]
    by (simp add: subst0_def C_lifted_subst_var_two C_ternary_subst_first
        C_subst_twice_raised C_subst_raised)
qed

lemma C_boolean_disj_distributes:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    and C: "\<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj A (Conj B C))
    (Conj (Disj A B) (Disj A C))"
proof -
  let ?P = "Disj (Var 2) (Conj (Var 1) (Var 0))"
  let ?Q = "Conj (Disj (Var 2) (Var 1)) (Disj (Var 2) (Var 0))"
  have P: "Prop # Prop # Prop # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # Prop # \<Gamma> \<turnstile> ?Q : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have ax: "\<Gamma> \<turnstile>\<^sub>C bool_dist_disj_conj"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  have eq: "\<Gamma> \<turnstile>\<^sub>C
    Eq (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
      (Lam Prop (Lam Prop (Lam Prop ?P))) (Lam Prop (Lam Prop (Lam Prop ?Q)))"
    using ax by (simp add: bool_dist_disj_conj_def)
  show ?thesis using C_ternary_operator_identity_instance[OF P Q A B C eq]
    by (simp add: subst0_def C_lifted_subst_var_two C_ternary_subst_first
        C_subst_twice_raised C_subst_raised)
qed

subsection \<open>Figure 3: dissolution\<close>

text \<open>
  ⊢C A ∧ (B ∨ ¬B) =ₜ A and ⊢C A ∨ (B ∧ ¬B) =ₜ A.
  Source: Bacon--Dorr Figure 3, p.10, Dissolution-∧∨ and Dissolution-∨∧.

  Isabelle representation.  Each binary operation identity is instantiated
  using C_binary_operator_identity_instance.
  Status.  No general theorem-to-truth rule is used.
\<close>

lemma C_boolean_conj_dissolves:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Conj A (Disj B (Neg B))) A"
proof -
  let ?P = "Conj (Var 1) (Disj (Var 0) (Neg (Var 0)))"
  have P: "Prop # Prop # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # \<Gamma> \<turnstile> Var 1 : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have ax: "\<Gamma> \<turnstile>\<^sub>C bool_dissolve_conj_disj"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  have eq: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty
    (Lam Prop (Lam Prop ?P)) (Lam Prop (Lam Prop (Var 1)))"
    using ax by (simp add: bool_dissolve_conj_disj_def)
  show ?thesis using C_binary_operator_identity_instance[OF P Q A B eq]
    by (simp add: subst0_def C_subst_raised)
qed

lemma C_boolean_disj_dissolves:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj A (Conj B (Neg B))) A"
proof -
  let ?P = "Disj (Var 1) (Conj (Var 0) (Neg (Var 0)))"
  have P: "Prop # Prop # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # \<Gamma> \<turnstile> Var 1 : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have ax: "\<Gamma> \<turnstile>\<^sub>C bool_dissolve_disj_conj"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  have eq: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty
    (Lam Prop (Lam Prop ?P)) (Lam Prop (Lam Prop (Var 1)))"
    using ax by (simp add: bool_dissolve_disj_conj_def)
  show ?thesis using C_binary_operator_identity_instance[OF P Q A B eq]
    by (simp add: subst0_def C_subst_raised)
qed

subsection \<open>A fixed Boolean truth representative\<close>

text \<open>
  Put ⊤ᴮ := ⊤₀ ∨ ¬⊤₀.  The results show
  ⊢C (A ∨ ¬A) =ₜ (B ∨ ¬B), ⊢C (A ∨ ¬A) =ₜ ⊤ᴮ,
  and ⊢C (A → A) =ₜ ⊤ᴮ.
  Sources: Bacon--Dorr Figure 3, p.10; intended use A.2(i), p.65.

  Isabelle representation.  C_boolean_truth names this fixed excluded middle.
  Status.  These are pointwise proposition identities.  ⊤ᴮ =ₜ ⊤₀ remains unproved.
\<close>

definition C_boolean_truth :: oterm where
  "C_boolean_truth = Disj ObjTrue (Neg ObjTrue)"

lemma C_boolean_truth_type:
  "\<Gamma> \<turnstile> C_boolean_truth : Prop"
  unfolding C_boolean_truth_def by (intro has_type.Disj has_type.Neg typed_ObjTrue)

lemma C_boolean_excluded_middle_identity:
  assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj A (Neg A)) (Disj B (Neg B))"
proof -
  have T_type: "\<Gamma> \<turnstile> Disj A (Neg A) : Prop" using A by auto
  have U_type: "\<Gamma> \<turnstile> Disj B (Neg B) : Prop" using B by auto
  have TU_type: "\<Gamma> \<turnstile> Conj (Disj A (Neg A)) (Disj B (Neg B)) : Prop"
    using T_type U_type by auto
  have UT_type: "\<Gamma> \<turnstile> Conj (Disj B (Neg B)) (Disj A (Neg A)) : Prop"
    using T_type U_type by auto
  have left_identity: "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Conj (Disj A (Neg A)) (Disj B (Neg B))) (Disj A (Neg A))"
    by (rule C_boolean_conj_dissolves[OF T_type B])
  have right_identity: "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Conj (Disj B (Neg B)) (Disj A (Neg A))) (Disj B (Neg B))"
    by (rule C_boolean_conj_dissolves[OF U_type A])
  have comm_identity: "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Conj (Disj A (Neg A)) (Disj B (Neg B)))
    (Conj (Disj B (Neg B)) (Disj A (Neg A)))"
    by (rule C_boolean_conj_commutes[OF T_type U_type])
  have left_inverse: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj A (Neg A))
    (Conj (Disj A (Neg A)) (Disj B (Neg B)))"
    by (rule C_closure_eq_sym_from[OF TU_type T_type left_identity])
  have middle_identity: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj A (Neg A))
    (Conj (Disj B (Neg B)) (Disj A (Neg A)))"
    by (rule C_closure_eq_trans_from
      [OF T_type TU_type UT_type left_inverse comm_identity])
  show ?thesis
    by (rule C_closure_eq_trans_from
      [OF T_type UT_type U_type middle_identity right_identity])
qed

lemma C_boolean_excluded_middle_to_truth:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj A (Neg A)) C_boolean_truth"
  unfolding C_boolean_truth_def
  by (rule C_boolean_excluded_middle_identity[OF assms typed_ObjTrue])

lemma C_boolean_self_implication_to_truth:
  assumes A: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Imp A A) C_boolean_truth"
proof -
  have I: "\<Gamma> \<turnstile> Imp A A : Prop" using A by auto
  have N: "\<Gamma> \<turnstile> Neg A : Prop" using A by auto
  have D: "\<Gamma> \<turnstile> Disj (Neg A) A : Prop" using A N by auto
  have E: "\<Gamma> \<turnstile> Disj A (Neg A) : Prop" using A N by auto
  have material: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Imp A A) (Disj (Neg A) A)"
    by (rule C_closure_material_imp_instance[OF A A])
  have comm: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj (Neg A) A) (Disj A (Neg A))"
    by (rule C_boolean_disj_commutes[OF N A])
  have IE: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Imp A A) (Disj A (Neg A))"
    by (rule C_closure_eq_trans_from[OF I D E material comm])
  have ET: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj A (Neg A)) C_boolean_truth"
    by (rule C_boolean_excluded_middle_to_truth[OF A])
  show ?thesis
    by (rule C_closure_eq_trans_from[OF I E C_boolean_truth_type IE ET])
qed

text \<open>
  ⊤ᴮ is the particular excluded middle ⊤₀ ∨ ¬⊤₀; it is not
  definitionally the quantified formula ⊤₀ := ∀p.(p → p).
  Sources: Bacon--Dorr Figure 1, p.6, for the source's separate choice of
  truth term; Appendix A.2(i), p.65, for the required identity-to-truth case.

  Representation and status.  C_boolean_truth names ⊤ᴮ and ObjTrue
  names ⊤₀.  Their identity still needs operation-level quantified
  reasoning.  A proof-producing Boolean normalization theorem beneath
  λv̄ also remains open; the displayed families do not establish it.
\<close>

end
