theory Bacon_C_Primitive_Basis
  imports Bacon_C_Congruence
begin

section \<open>Material implication in the source primitive basis\<close>

text \<open>
  The source defines → by λpq.(¬p ∨ q).  In the implemented primitive
  basis the corresponding closed identity is
  ⊢C (λpq.p → q) = (λpq.¬p ∨ q).
  Sources: Bacon--Dorr Figure 1, p.6, and Appendix A.2(i), p.65.

  Isabelle representation.  Imp is a separate constructor.  The supplied
  Boolean-basis member bool_material_imp records its operation identity;
  this file extracts that member and derives its applied instances.

  Status.  This is an explicit basis bridge in C, not a claim that H
  identifies every truth-functionally equivalent pair.  The general PC
  case of A.2 and Equivalence closure remain unproved here.
\<close>

subsection \<open>Primitive-basis bridge for Appendix A.2, PC case\<close>

text \<open>
  The closed operation identity yields ⊢C (A → B) =ₜ (¬A ∨ B) for
  propositions A and B.  Sources: Bacon--Dorr Figure 1, p.6; Figure 2,
  p.8, LL and β; Appendix A.2(i), p.65.

  Isabelle representation.  The first result has type t → t → t.
  Congruence supplies two applications, and two capture-avoiding β steps
  then yield the proposition identity.

  Status.  Equality of propositions is proved, not merely A → B ↔ ¬A ∨ B.
  This prerequisite does not settle arbitrary Boolean normalization.
\<close>

lemma C_closure_material_imp_operator:
  "\<Gamma> \<turnstile>\<^sub>C
    Eq prop_bin_ty
      (Lam Prop (Lam Prop (Imp (Var 1) (Var 0))))
      (Lam Prop (Lam Prop (Disj (Neg (Var 1)) (Var 0))))"
proof -
  have "\<Gamma> \<turnstile>\<^sub>C bool_material_imp"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  then show ?thesis by (simp add: bool_material_imp_def)
qed

lemma C_closure_material_imp_applied:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (App (App (Lam Prop (Lam Prop (Imp (Var 1) (Var 0)))) A) B)
    (App (App (Lam Prop (Lam Prop (Disj (Neg (Var 1)) (Var 0)))) A) B)"
proof -
  let ?F = "Lam Prop (Lam Prop (Imp (Var 1) (Var 0)))"
  let ?G = "Lam Prop (Lam Prop (Disj (Neg (Var 1)) (Var 0)))"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have G_type: "\<Gamma> \<turnstile> ?G : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have FG: "\<Gamma> \<turnstile>\<^sub>C Eq
    (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop) ?F ?G"
    using C_closure_material_imp_operator[of \<Gamma>]
    by (simp add: prop_bin_ty_def)
  have FA_GA: "\<Gamma> \<turnstile>\<^sub>C
    Eq (Prop \<rightarrow>\<^sub>o Prop) (App ?F A) (App ?G A)"
    by (rule C_closure_app_congruence_left[OF F_type G_type A_type FG])
  have FA_type: "\<Gamma> \<turnstile> App ?F A : Prop \<rightarrow>\<^sub>o Prop"
    using F_type A_type by auto
  have GA_type: "\<Gamma> \<turnstile> App ?G A : Prop \<rightarrow>\<^sub>o Prop"
    using G_type A_type by auto
  show ?thesis
    by (rule C_closure_app_congruence_left[OF FA_type GA_type B_type FA_GA])
qed


text \<open>
  ⊢C ((λx:σ.λy:τ.P) A) B =υ P[A/x,B/y].
  Source: Bacon--Dorr Figure 2, p.8, contextual β; its use in A.2, p.65.

  Isabelle representation.  The nested lift_subst and subst0 terms record
  capture avoidance and removal of the two binder slots.
  Status.  This is typed β identity, not Functionality.
\<close>

lemma C_closure_binary_beta_identity:
  assumes P_type: "\<tau> # \<sigma> # \<Gamma> \<turnstile> P : \<upsilon>"
    and A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and B_type: "\<Gamma> \<turnstile> B : \<tau>"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq \<upsilon>
    (App (App (Lam \<sigma> (Lam \<tau> P)) A) B)
    (subst0 B (subst (lift_subst (case_nat A Var)) P))"
proof -
  let ?F = "Lam \<sigma> (Lam \<tau> P)"
  let ?Q = "subst (lift_subst (case_nat A Var)) P"
  have inner_type: "\<sigma> # \<Gamma> \<turnstile> Lam \<tau> P : \<tau> \<rightarrow>\<^sub>o \<upsilon>"
    using P_type by auto
  have F_type: "\<Gamma> \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o \<tau> \<rightarrow>\<^sub>o \<upsilon>"
    using inner_type by auto
  have FA_type: "\<Gamma> \<turnstile> App ?F A : \<tau> \<rightarrow>\<^sub>o \<upsilon>"
    using F_type A_type by auto
  have LQ_type: "\<Gamma> \<turnstile> Lam \<tau> ?Q : \<tau> \<rightarrow>\<^sub>o \<upsilon>"
  proof -
    have "\<Gamma> \<turnstile> subst0 A (Lam \<tau> P) : \<tau> \<rightarrow>\<^sub>o \<upsilon>"
      using inner_type A_type by (rule subst0_preserves_typing)
    then show ?thesis by (simp add: subst0_def)
  qed
  have Q_type: "\<tau> # \<Gamma> \<turnstile> ?Q : \<upsilon>"
    using LQ_type by (auto elim: has_type.cases)
  have FAB_type: "\<Gamma> \<turnstile> App (App ?F A) B : \<upsilon>"
    using FA_type B_type by auto
  have LQB_type: "\<Gamma> \<turnstile> App (Lam \<tau> ?Q) B : \<upsilon>"
    using LQ_type B_type by auto
  have result_type: "\<Gamma> \<turnstile> subst0 B ?Q : \<upsilon>"
    using Q_type B_type by (rule subst0_preserves_typing)
  have first_step: "compatible_step beta_contract (App ?F A) (Lam \<tau> ?Q)"
  proof -
    have "compatible_step beta_contract (App ?F A) (subst0 A (Lam \<tau> P))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis by (simp add: subst0_def)
  qed
  have first_identity: "\<Gamma> \<turnstile>\<^sub>C
    Eq (\<tau> \<rightarrow>\<^sub>o \<upsilon>) (App ?F A) (Lam \<tau> ?Q)"
    using FA_type LQ_type first_step by (rule C_closure_beta_identity)
  have applied_identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<upsilon>
    (App (App ?F A) B) (App (Lam \<tau> ?Q) B)"
    by (rule C_closure_app_congruence_left[OF FA_type LQ_type B_type first_identity])
  have second_step: "compatible_step beta_contract
    (App (Lam \<tau> ?Q) B) (subst0 B ?Q)"
    by (intro compatible_step.root beta_contract.beta)
  have second_identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<upsilon>
    (App (Lam \<tau> ?Q) B) (subst0 B ?Q)"
    using LQB_type result_type second_step by (rule C_closure_beta_identity)
  show ?thesis
    by (rule C_closure_eq_trans_from
      [OF FAB_type LQB_type result_type applied_identity second_identity])
qed

text \<open>
  ⊢C (A → B) =ₜ (¬A ∨ B).
  Source: Bacon--Dorr Figure 1, p.6, interpreted through the explicitly
  supplied primitive-basis operation identity.

  Isabelle representation.  The previous two applications and β
  identities are composed by equality transitivity.
  Status.  The conclusion remains in axiom-based C.
\<close>

lemma C_closure_material_imp_instance:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Imp A B) (Disj (Neg A) B)"
proof -
  let ?F = "Lam Prop (Lam Prop (Imp (Var 1) (Var 0)))"
  let ?G = "Lam Prop (Lam Prop (Disj (Neg (Var 1)) (Var 0)))"
  let ?L = "App (App ?F A) B"
  let ?R = "App (App ?G A) B"
  have F_body: "Prop # Prop # \<Gamma> \<turnstile> Imp (Var 1) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have G_body: "Prop # Prop # \<Gamma> \<turnstile> Disj (Neg (Var 1)) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (intro has_type.Lam F_body)
  have G_type: "\<Gamma> \<turnstile> ?G : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (intro has_type.Lam G_body)
  have L_type: "\<Gamma> \<turnstile> ?L : Prop"
    using F_type A_type B_type by auto
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using G_type A_type B_type by auto
  have imp_type: "\<Gamma> \<turnstile> Imp A B : Prop"
    using A_type B_type by auto
  have disj_type: "\<Gamma> \<turnstile> Disj (Neg A) B : Prop"
    using A_type B_type by auto
  have cancel_raised_A: "subst (case_nat B Var) (rename Suc A) = A"
    using subst0_shift[of B A]
    by (simp only: subst0_def shift_def)
  have L_imp: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?L (Imp A B)"
    using C_closure_binary_beta_identity[OF F_body A_type B_type]
    by (simp add: subst0_def cancel_raised_A)
  have R_disj: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?R (Disj (Neg A) B)"
    using C_closure_binary_beta_identity[OF G_body A_type B_type]
    by (simp add: subst0_def cancel_raised_A)
  have imp_L: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Imp A B) ?L"
    by (rule C_closure_eq_sym_from[OF L_type imp_type L_imp])
  have L_R: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?L ?R"
    using A_type B_type by (rule C_closure_material_imp_applied)
  have imp_R: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Imp A B) ?R"
    by (rule C_closure_eq_trans_from[OF imp_type L_type R_type imp_L L_R])
  show ?thesis
    by (rule C_closure_eq_trans_from[OF imp_type R_type disj_type imp_R R_disj])
qed

end
