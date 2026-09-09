theory Bacon_C_Predicate_Context
  imports Bacon_C_Truth_Representative
begin

section \<open>Typed context replacement beneath one abstraction\<close>

text \<open>
  From ⊢C (λv.A) = (λv.B), derive
  ⊢C (λv.P[A/x]) = (λv.P[B/x]), where P has a typed parameter x.
  This is the compositional replacement step needed for Boolean
  normalization in Bacon--Dorr Appendix A.2(i), p.65.

  Isabelle representation.  P has context τ # σ # Γ, with x in slot
  zero and v in slot one.  The proof replaces the function λv.A itself
  in a typed context, then performs two contextual β reductions.
  Status.  This is derived from Ref, LL, and β in axiom-based C.
  Its hypothesis is identity of abstractions, not an open identity A = B.
  No Functionality, CE/CEV rule, or full PC normalization is assumed.
\<close>

lemma C_insert_after_two_binders_type:
  assumes P: "\<tau> # \<sigma> # \<Gamma> \<turnstile> P : \<rho>"
  shows "\<tau> # \<sigma> # \<nu> # \<Gamma> \<turnstile>
    rename (lift_ren (lift_ren Suc)) P : \<rho>"
proof (rule renaming_preserves_typing[OF P])
  fix n \<upsilon>
  assume index: "lookup (\<tau> # \<sigma> # \<Gamma>) n = Some \<upsilon>"
  show "lookup (\<tau> # \<sigma> # \<nu> # \<Gamma>) (lift_ren (lift_ren Suc) n) = Some \<upsilon>"
  proof (cases n)
    case 0
    then show ?thesis using index by simp
  next
    case (Suc m)
    then show ?thesis using index by (cases m) simp_all
  qed
qed

lemma C_remove_inserted_two_binder_parameter:
  "subst (lift_subst (lift_subst (case_nat F Var)))
    (rename (lift_ren (lift_ren Suc)) P) = P"
proof (rule subst_rename_inverse)
  fix n
  show "lift_subst (lift_subst (case_nat F Var)) (lift_ren (lift_ren Suc) n) = Var n"
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    then show ?thesis by (cases m) simp_all
  qed
qed

lemma C_abstraction_argument_beta_step:
  "compatible_step beta_contract (App (shift (Lam \<sigma> A)) (Var 0)) A"
proof -
  have "compatible_step beta_contract
    (App (Lam \<sigma> (rename (lift_ren Suc) A)) (Var 0))
    (subst0 (Var 0) (rename (lift_ren Suc) A))"
    by (intro compatible_step.root beta_contract.beta)
  then show ?thesis by (simp add: shift_def C_subst0_lifted_shift)
qed

lemma C_predicate_context_beta:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : \<tau>"
    and P: "\<tau> # \<sigma> # \<Gamma> \<turnstile> P : \<rho>"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o \<rho>)
    (Lam \<sigma> (App (Lam \<tau> P) (App (shift (Lam \<sigma> A)) (Var 0))))
    (Lam \<sigma> (subst0 A P))"
proof -
  let ?L = "App (Lam \<tau> P) (App (shift (Lam \<sigma> A)) (Var 0))"
  let ?M = "App (Lam \<tau> P) A"
  have abstraction: "\<Gamma> \<turnstile> Lam \<sigma> A : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    by (rule has_type.Lam[OF A])
  have shifted: "\<sigma> # \<Gamma> \<turnstile> shift (Lam \<sigma> A) : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    by (rule weakening_front[OF abstraction])
  have variable: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  have argument: "\<sigma> # \<Gamma> \<turnstile> App (shift (Lam \<sigma> A)) (Var 0) : \<tau>"
    by (rule has_type.App[OF shifted variable])
  have function_type: "\<sigma> # \<Gamma> \<turnstile> Lam \<tau> P : \<tau> \<rightarrow>\<^sub>o \<rho>"
    by (rule has_type.Lam[OF P])
  have L: "\<sigma> # \<Gamma> \<turnstile> ?L : \<rho>" by (rule has_type.App[OF function_type argument])
  have M: "\<sigma> # \<Gamma> \<turnstile> ?M : \<rho>" by (rule has_type.App[OF function_type A])
  have R: "\<sigma> # \<Gamma> \<turnstile> subst0 A P : \<rho>"
    by (rule subst0_preserves_typing[OF P A])
  have first_step: "compatible_step beta_contract ?L ?M"
    by (rule compatible_step.App_right[OF C_abstraction_argument_beta_step])
  have second_step: "compatible_step beta_contract ?M (subst0 A P)"
    by (intro compatible_step.root beta_contract.beta)
  have first: "beta_eta_equiv (\<sigma> # \<Gamma>) \<rho> ?L ?M"
    by (rule beta_eta_equiv.Beta[OF L M first_step])
  have second: "beta_eta_equiv (\<sigma> # \<Gamma>) \<rho> ?M (subst0 A P)"
    by (rule beta_eta_equiv.Beta[OF M R second_step])
  have conversion: "beta_eta_equiv (\<sigma> # \<Gamma>) \<rho> ?L (subst0 A P)"
    by (rule beta_eta_equiv.Trans[OF first second])
  show ?thesis by (rule C_closure_beta_eta_identity[OF C_beta_eta_Lam[OF conversion]])
qed

theorem C_predicate_context_replacement:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : \<tau>"
    and B: "\<sigma> # \<Gamma> \<turnstile> B : \<tau>"
    and P: "\<tau> # \<sigma> # \<Gamma> \<turnstile> P : \<rho>"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Lam \<sigma> A) (Lam \<sigma> B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o \<rho>)
    (Lam \<sigma> (subst0 A P)) (Lam \<sigma> (subst0 B P))"
proof -
  let ?F = "Lam \<sigma> A"
  let ?G = "Lam \<sigma> B"
  let ?T = "rename (lift_ren (lift_ren Suc)) P"
  let ?K = "Lam \<sigma> (App (Lam \<tau> ?T) (App (Var 1) (Var 0)))"
  have F: "\<Gamma> \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o \<tau>" by (rule has_type.Lam[OF A])
  have G: "\<Gamma> \<turnstile> ?G : \<sigma> \<rightarrow>\<^sub>o \<tau>" by (rule has_type.Lam[OF B])
  have T: "\<tau> # \<sigma> # (\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile> ?T : \<rho>"
    by (rule C_insert_after_two_binders_type[OF P])
  have function_type: "\<sigma> # (\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile> Lam \<tau> ?T : \<tau> \<rightarrow>\<^sub>o \<rho>"
    by (rule has_type.Lam[OF T])
  have operator: "\<sigma> # (\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile> Var 1 : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    by (rule has_type.Var) simp
  have variable: "\<sigma> # (\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by (rule has_type.Var) simp
  have argument: "\<sigma> # (\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile> App (Var 1) (Var 0) : \<tau>"
    by (rule has_type.App[OF operator variable])
  have body: "\<sigma> # (\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile>
    App (Lam \<tau> ?T) (App (Var 1) (Var 0)) : \<rho>"
    by (rule has_type.App[OF function_type argument])
  have context_type: "(\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile> ?K : \<sigma> \<rightarrow>\<^sub>o \<rho>"
    by (rule has_type.Lam[OF body])
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o \<rho>) (subst0 ?F ?K) (subst0 ?G ?K)"
    by (rule C_closure_congruence[OF F G context_type identity])
  have replaced: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o \<rho>)
    (Lam \<sigma> (App (Lam \<tau> P) (App (shift ?F) (Var 0))))
    (Lam \<sigma> (App (Lam \<tau> P) (App (shift ?G) (Var 0))))"
    using raw by (simp add: subst0_def C_remove_inserted_two_binder_parameter shift_def)
  show ?thesis by (rule C_A1_transport[OF replaced C_predicate_context_beta[OF A P]
    C_predicate_context_beta[OF B P]])
qed

subsection \<open>Boolean congruence instances\<close>

text \<open>
  Predicate identity is preserved by ¬ and by a conjunction with a
  fixed typed body D(v).  Thus normalization may replace a subformula
  recursively while retaining identity of the surrounding abstraction.
  Isabelle representation.  P is respectively ¬x or x ∧ D(v).
  Status.  These are instances of the typed context theorem, not a
  completeness theorem for the Boolean equations.
\<close>

lemma C_boolean_lambda_neg_congruence:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> (Neg A)) (Lam \<sigma> (Neg B))"
proof -
  have P: "Prop # \<sigma> # \<Gamma> \<turnstile> Neg (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  show ?thesis using C_predicate_context_replacement[OF A B P identity]
    by (simp add: subst0_def)
qed

lemma C_boolean_lambda_conj_right_context:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and D: "\<sigma> # \<Gamma> \<turnstile> D : Prop"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A D)) (Lam \<sigma> (Conj B D))"
proof -
  have shifted: "Prop # \<sigma> # \<Gamma> \<turnstile> shift D : Prop"
    by (rule weakening_front[OF D])
  have variable: "Prop # \<sigma> # \<Gamma> \<turnstile> Var 0 : Prop" by (rule has_type.Var) simp
  have P: "Prop # \<sigma> # \<Gamma> \<turnstile> Conj (Var 0) (shift D) : Prop"
    by (rule has_type.Conj[OF variable shifted])
  show ?thesis using C_predicate_context_replacement[OF A B P identity]
    by (simp add: subst0_def)
qed

lemma C_boolean_lambda_constant_congruence:
  assumes identity: "\<Gamma> \<turnstile>\<^sub>C Eq Prop M N"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (shift M)) (Lam \<sigma> (shift N))"
proof -
  have M: "\<Gamma> \<turnstile> M : Prop" and N: "\<Gamma> \<turnstile> N : Prop"
    using C_proves_formula[OF identity] by (auto elim: has_type.cases)
  have P: "Prop # \<Gamma> \<turnstile> Lam \<sigma> (Var 1) : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  show ?thesis using C_closure_congruence[OF M N P identity]
    by (simp add: subst0_def shift_def)
qed

corollary C_boolean_lambda_excluded_middle_ObjTrue:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A (Neg A))) (Lam \<sigma> ObjTrue)"
proof -
  have boolean: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A (Neg A))) (Lam \<sigma> (shift C_boolean_truth))"
    using C_boolean_lambda_excluded_middle_identity[OF A typed_ObjTrue]
    by (simp add: C_boolean_truth_def shift_def ObjTrue_def)
  have representative: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (shift C_boolean_truth)) (Lam \<sigma> ObjTrue)"
    using C_boolean_lambda_constant_congruence[OF C_boolean_truth_eq_ObjTrue,
      where \<sigma> = \<sigma> and \<Gamma> = \<Gamma>] by simp
  show ?thesis by (rule C_A1_trans[OF boolean representative])
qed

end
