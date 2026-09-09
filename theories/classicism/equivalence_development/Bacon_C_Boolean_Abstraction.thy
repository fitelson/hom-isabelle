theory Bacon_C_Boolean_Abstraction
  imports Bacon_C_Appendix_A2_Ref
begin

section \<open>Boolean operation identities beneath a binder\<close>

text \<open>
  Appendix A.2 requires identities of λv̄.P, not merely identities of
  P at each assignment.  We start with a proved identity F = G between
  binary operations and replace F by G inside λv.F(A(v))(B(v)).
  Contextual β conversion then exposes the corresponding Boolean formulas.

  Isabelle representation: a fresh operation slot is inserted behind the
  bound variable and removed by typed Leibniz congruence.  The conversion
  proofs below use the syntactic βη relation, not CE/CEV Equivalence.
  Status: one-binder Boolean normalization ingredients, not full PC
  normalization or Proposition A.2.
\<close>

lemma C_beta_eta_Lam_aux:
  assumes conversion: "beta_eta_equiv \<Delta> \<rho> A B"
  shows "\<Delta> = \<tau> # \<Gamma> \<Longrightarrow>
    beta_eta_equiv \<Gamma> (\<tau> \<rightarrow>\<^sub>o \<rho>) (Lam \<tau> A) (Lam \<tau> B)"
  using conversion
proof (induction arbitrary: \<tau> \<Gamma> rule: beta_eta_equiv.induct)
  case (Refl \<Delta> M \<rho>)
  have M: "\<tau> # \<Gamma> \<turnstile> M : \<rho>"
    using Refl.hyps by (simp only: Refl.prems)
  show ?case by (rule beta_eta_equiv.Refl[OF has_type.Lam[OF M]])
next
  case (Beta \<Delta> M \<rho> N)
  have M: "\<tau> # \<Gamma> \<turnstile> M : \<rho>"
    using Beta.hyps(1) by (simp only: Beta.prems)
  have N: "\<tau> # \<Gamma> \<turnstile> N : \<rho>"
    using Beta.hyps(2) by (simp only: Beta.prems)
  show ?case by (rule beta_eta_equiv.Beta[OF has_type.Lam[OF M]
    has_type.Lam[OF N] compatible_step.Lam_body[OF Beta.hyps(3)]])
next
  case (Eta \<Delta> M \<rho> N)
  have M: "\<tau> # \<Gamma> \<turnstile> M : \<rho>"
    using Eta.hyps(1) by (simp only: Eta.prems)
  have N: "\<tau> # \<Gamma> \<turnstile> N : \<rho>"
    using Eta.hyps(2) by (simp only: Eta.prems)
  show ?case by (rule beta_eta_equiv.Eta[OF has_type.Lam[OF M]
    has_type.Lam[OF N] compatible_step.Lam_body[OF Eta.hyps(3)]])
next
  case (Sym \<Delta> \<rho> M N)
  show ?case by (rule beta_eta_equiv.Sym[OF Sym.IH[OF Sym.prems]])
next
  case (Trans \<Delta> \<rho> M N P)
  show ?case by (rule beta_eta_equiv.Trans[OF Trans.IH(1)[OF Trans.prems]
    Trans.IH(2)[OF Trans.prems]])
qed

lemma C_beta_eta_Lam:
  assumes conversion: "beta_eta_equiv (\<tau> # \<Gamma>) \<rho> A B"
  shows "beta_eta_equiv \<Gamma> (\<tau> \<rightarrow>\<^sub>o \<rho>) (Lam \<tau> A) (Lam \<tau> B)"
  by (rule C_beta_eta_Lam_aux[OF conversion]) (rule refl)

lemma C_binary_beta_equiv:
  assumes P: "Prop # Prop # \<Gamma> \<turnstile> P : Prop"
    and A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
  shows "beta_eta_equiv \<Gamma> Prop (App (App (Lam Prop (Lam Prop P)) A) B)
    (subst0 B (subst (lift_subst (case_nat A Var)) P))"
proof -
  let ?F = "Lam Prop (Lam Prop P)"
  let ?Q = "subst (lift_subst (case_nat A Var)) P"
  let ?L = "App (App ?F A) B"
  let ?M = "App (Lam Prop ?Q) B"
  let ?R = "subst0 B ?Q"
  have inner: "Prop # \<Gamma> \<turnstile> Lam Prop P : Prop \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Lam[OF P])
  have F: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Lam[OF inner])
  have FA: "\<Gamma> \<turnstile> App ?F A : Prop \<rightarrow>\<^sub>o Prop" by (rule has_type.App[OF F A])
  have QL: "\<Gamma> \<turnstile> Lam Prop ?Q : Prop \<rightarrow>\<^sub>o Prop"
    using subst0_preserves_typing[OF inner A] by (simp add: subst0_def)
  have Q: "Prop # \<Gamma> \<turnstile> ?Q : Prop" using QL by (auto elim: has_type.cases)
  have L: "\<Gamma> \<turnstile> ?L : Prop" by (rule has_type.App[OF FA B])
  have M: "\<Gamma> \<turnstile> ?M : Prop" by (rule has_type.App[OF QL B])
  have R: "\<Gamma> \<turnstile> ?R : Prop" by (rule subst0_preserves_typing[OF Q B])
  have first: "compatible_step beta_contract ?L ?M"
  proof -
    have "compatible_step beta_contract (App ?F A) (subst0 A (Lam Prop P))"
      by (intro compatible_step.root beta_contract.beta)
    then have "compatible_step beta_contract (App ?F A) (Lam Prop ?Q)"
      by (simp add: subst0_def)
    then show ?thesis by (rule compatible_step.App_left)
  qed
  have second: "compatible_step beta_contract ?M ?R"
    by (intro compatible_step.root beta_contract.beta)
  show ?thesis by (rule beta_eta_equiv.Trans[OF beta_eta_equiv.Beta[OF L M first]
    beta_eta_equiv.Beta[OF M R second]])
qed

subsection \<open>Fresh operation-slot bookkeeping\<close>

lemma C_insert_after_binder_type:
  assumes A: "\<tau> # \<Gamma> \<turnstile> A : \<rho>"
  shows "\<tau> # \<nu> # \<Gamma> \<turnstile> rename (lift_ren Suc) A : \<rho>"
proof (rule renaming_preserves_typing[OF A])
  fix n \<sigma>
  assume index: "lookup (\<tau> # \<Gamma>) n = Some \<sigma>"
  show "lookup (\<tau> # \<nu> # \<Gamma>) (lift_ren Suc n) = Some \<sigma>"
    using index by (cases n) simp_all
qed

lemma C_remove_inserted_operation:
  "subst (lift_subst (case_nat F Var)) (rename (lift_ren Suc) A) = A"
  by (rule subst_rename_inverse) (case_tac n; simp)

lemma C_binary_lambda_operator_congruence:
  assumes F: "\<Gamma> \<turnstile> F : prop_bin_ty" and G: "\<Gamma> \<turnstile> G : prop_bin_ty"
    and A: "\<tau> # \<Gamma> \<turnstile> A : Prop" and B: "\<tau> # \<Gamma> \<turnstile> B : Prop"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty F G"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (App (App (shift F) A) B)) (Lam \<tau> (App (App (shift G) A) B))"
proof -
  let ?A = "rename (lift_ren Suc) A"
  let ?B = "rename (lift_ren Suc) B"
  let ?P = "Lam \<tau> (App (App (Var 1) ?A) ?B)"
  have A': "\<tau> # prop_bin_ty # \<Gamma> \<turnstile> ?A : Prop" by (rule C_insert_after_binder_type[OF A])
  have B': "\<tau> # prop_bin_ty # \<Gamma> \<turnstile> ?B : Prop" by (rule C_insert_after_binder_type[OF B])
  have operator_type: "\<tau> # prop_bin_ty # \<Gamma> \<turnstile> Var 1 :
    Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: lookup_def prop_bin_ty_def)
  have first_app: "\<tau> # prop_bin_ty # \<Gamma> \<turnstile> App (Var 1) ?A : Prop \<rightarrow>\<^sub>o Prop"
    by (rule has_type.App[OF operator_type A'])
  have second_app: "\<tau> # prop_bin_ty # \<Gamma> \<turnstile> App (App (Var 1) ?A) ?B : Prop"
    by (rule has_type.App[OF first_app B'])
  have pattern_type: "prop_bin_ty # \<Gamma> \<turnstile> ?P : \<tau> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Lam[OF second_app])
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop) (subst0 F ?P) (subst0 G ?P)"
    by (rule C_closure_congruence[OF F G pattern_type identity])
  show ?thesis using raw
    by (simp add: subst0_def C_remove_inserted_operation shift_def)
qed

lemma C_binary_lambda_beta:
  assumes P: "Prop # Prop # \<Gamma> \<turnstile> P : Prop"
    and A: "\<tau> # \<Gamma> \<turnstile> A : Prop" and B: "\<tau> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (App (App (shift (Lam Prop (Lam Prop P))) A) B))
    (Lam \<tau> (subst0 B (subst (lift_subst (case_nat A Var))
      (rename (lift_ren (lift_ren Suc)) P))))"
proof -
  let ?F = "Lam Prop (Lam Prop P)"
  let ?P = "rename (lift_ren (lift_ren Suc)) P"
  have F: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (intro has_type.Lam P)
  have shifted: "\<tau> # \<Gamma> \<turnstile> shift ?F : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (rule weakening_front[OF F])
  have body: "Prop # Prop # \<tau> # \<Gamma> \<turnstile> ?P : Prop"
    using shifted unfolding shift_def by (auto elim: has_type.cases)
  have conversion: "beta_eta_equiv (\<tau> # \<Gamma>) Prop
    (App (App (shift ?F) A) B) (subst0 B (subst (lift_subst (case_nat A Var)) ?P))"
    using C_binary_beta_equiv[OF body A B] by (simp add: shift_def)
  show ?thesis by (rule C_closure_beta_eta_identity[OF C_beta_eta_Lam[OF conversion]])
qed

lemma C_binary_lambda_identity_instance:
  assumes P: "Prop # Prop # \<Gamma> \<turnstile> P : Prop"
    and Q: "Prop # Prop # \<Gamma> \<turnstile> Q : Prop"
    and A: "\<tau> # \<Gamma> \<turnstile> A : Prop" and B: "\<tau> # \<Gamma> \<turnstile> B : Prop"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty
      (Lam Prop (Lam Prop P)) (Lam Prop (Lam Prop Q))"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (subst0 B (subst (lift_subst (case_nat A Var))
      (rename (lift_ren (lift_ren Suc)) P))))
    (Lam \<tau> (subst0 B (subst (lift_subst (case_nat A Var))
      (rename (lift_ren (lift_ren Suc)) Q))))"
proof -
  have F: "\<Gamma> \<turnstile> Lam Prop (Lam Prop P) : prop_bin_ty"
    unfolding prop_bin_ty_def by (intro has_type.Lam P)
  have G: "\<Gamma> \<turnstile> Lam Prop (Lam Prop Q) : prop_bin_ty"
    unfolding prop_bin_ty_def by (intro has_type.Lam Q)
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (App (App (shift (Lam Prop (Lam Prop P))) A) B))
    (Lam \<tau> (App (App (shift (Lam Prop (Lam Prop Q))) A) B))"
    by (rule C_binary_lambda_operator_congruence[OF F G A B identity])
  show ?thesis by (rule C_A1_transport[OF raw C_binary_lambda_beta[OF P A B]
    C_binary_lambda_beta[OF Q A B]])
qed

subsection \<open>First Boolean equations at predicate type\<close>

text \<open>
  From the closed Figure 3 operation identities we obtain
  ⊢C (λv.A ∧ B) = (λv.B ∧ A) and
  ⊢C (λv.A ∧ (B ∨ ¬B)) = (λv.A).
  These use one typed context replacement; they do not abstract an arbitrary
  open equation.  Together they identify all excluded-middle predicates.
\<close>

lemma C_boolean_lambda_conj_commutes:
  assumes A: "\<tau> # \<Gamma> \<turnstile> A : Prop" and B: "\<tau> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Conj A B)) (Lam \<tau> (Conj B A))"
proof -
  have P: "Prop # Prop # \<Gamma> \<turnstile> Conj (Var 1) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # \<Gamma> \<turnstile> Conj (Var 0) (Var 1) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have axiom: "\<Gamma> \<turnstile>\<^sub>C bool_comm_conj"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty
    (Lam Prop (Lam Prop (Conj (Var 1) (Var 0)))) (Lam Prop (Lam Prop (Conj (Var 0) (Var 1))))"
    using axiom by (simp only: bool_comm_conj_def)
  show ?thesis using C_binary_lambda_identity_instance[OF P Q A B identity]
    by (simp add: subst0_def C_subst_raised)
qed

lemma C_boolean_lambda_conj_dissolves:
  assumes A: "\<tau> # \<Gamma> \<turnstile> A : Prop" and B: "\<tau> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Conj A (Disj B (Neg B)))) (Lam \<tau> A)"
proof -
  let ?P = "Conj (Var 1) (Disj (Var 0) (Neg (Var 0)))"
  have P: "Prop # Prop # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # \<Gamma> \<turnstile> Var 1 : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have axiom: "\<Gamma> \<turnstile>\<^sub>C bool_dissolve_conj_disj"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty
    (Lam Prop (Lam Prop ?P)) (Lam Prop (Lam Prop (Var 1)))"
    using axiom by (simp only: bool_dissolve_conj_disj_def)
  show ?thesis using C_binary_lambda_identity_instance[OF P Q A B identity]
    by (simp add: subst0_def C_subst_raised)
qed

theorem C_boolean_lambda_excluded_middle_identity:
  assumes A: "\<tau> # \<Gamma> \<turnstile> A : Prop" and B: "\<tau> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop)
    (Lam \<tau> (Disj A (Neg A))) (Lam \<tau> (Disj B (Neg B)))"
proof -
  let ?T = "Disj A (Neg A)"
  let ?U = "Disj B (Neg B)"
  have T: "\<tau> # \<Gamma> \<turnstile> ?T : Prop" by (intro has_type.Disj has_type.Neg A)
  have U: "\<tau> # \<Gamma> \<turnstile> ?U : Prop" by (intro has_type.Disj has_type.Neg B)
  have left: "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop) (Lam \<tau> (Conj ?T ?U)) (Lam \<tau> ?T)"
    by (rule C_boolean_lambda_conj_dissolves[OF T B])
  have right: "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop) (Lam \<tau> (Conj ?U ?T)) (Lam \<tau> ?U)"
    by (rule C_boolean_lambda_conj_dissolves[OF U A])
  have comm: "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop) (Lam \<tau> (Conj ?T ?U)) (Lam \<tau> (Conj ?U ?T))"
    by (rule C_boolean_lambda_conj_commutes[OF T U])
  show ?thesis by (rule C_A1_trans[OF C_A1_trans[OF C_A1_sym[OF left] comm] right])
qed

corollary C_boolean_excluded_middle_predicate_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq (Prop \<rightarrow>\<^sub>o Prop)
    (Lam Prop (Disj (Var 0) (Neg (Var 0)))) (Lam Prop (shift C_boolean_truth))"
proof -
  have variable: "Prop # \<Gamma> \<turnstile> Var 0 : Prop" by (rule has_type.Var) simp
  have truth: "Prop # \<Gamma> \<turnstile> ObjTrue : Prop" by (rule typed_ObjTrue)
  show ?thesis using C_boolean_lambda_excluded_middle_identity[OF variable truth]
    by (simp add: C_boolean_truth_def shift_def ObjTrue_def)
qed

text \<open>
  The final equation supplies the positive-order excluded-middle predicate
  identity with the Boolean representative ⊤ᴮ.  Reversing the disjunction,
  handling self-implication and conjunction idempotence under λ, identifying
  ⊤ᴮ with ⊤₀, and completing general PC/vector normalization remain separate
  steps.  No C = CE = CEV result is claimed here.
\<close>

end
