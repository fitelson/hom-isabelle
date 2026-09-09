theory Bacon_C_Quantified_Truth
  imports Bacon_C_Boolean_Normalization
begin

section \<open>Quantified preparation for Bacon--Dorr Appendix A.1\<close>

text \<open>
  The preparation establishes predicate congruence for ∀ and the basis
  bridge ⊢C ⊤₀ =ₜ ∀p.(¬p ∨ p), where ⊤₀ := ∀p.(p → p).
  Sources: Bacon--Dorr Figure 1, p.6, and Proposition A.1, p.65.

  Isabelle representation.  ObjTrue names ⊤₀.  Forall is a binder
  constructor; its body uses slot zero.  Quantifier congruence is obtained
  from identity of the predicates themselves, not from pointwise
  equations at a free variable.

  Status.  This file supplies preparation, not A.1.  The subsequent
  Bacon_C_Appendix_A1 proves the represented A.1 result.  The independent
  bridge from C_boolean_truth to ObjTrue remains unresolved.
\<close>

subsection \<open>Predicate identity and universal quantification\<close>

text \<open>
  From ⊢C F =σ→t G obtain ⊢C (∀x:σ.Fx) =ₜ (∀x:σ.Gx).
  Sources: Bacon--Dorr Figure 2, p.8, LL and β; A.1, p.65.

  Isabelle representation.  Predicates are shifted before application to
  the new slot zero.  C_forall_of_predicate_identity also removes the
  β redexes of two displayed predicate abstractions.
  Status.  The premise is predicate identity, not merely ∀x.(Fx =ₜ Gx).
\<close>

lemma C_forall_predicate_congruence:
  assumes F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
    and G: "\<Gamma> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o Prop"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) F G"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Forall \<sigma> (App (shift F) (Var 0)))
    (Forall \<sigma> (App (shift G) (Var 0)))"
proof -
  have body: "(\<sigma> \<rightarrow>\<^sub>o Prop) # \<Gamma> \<turnstile>
    Forall \<sigma> (App (Var 1) (Var 0)) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (subst0 F (Forall \<sigma> (App (Var 1) (Var 0))))
    (subst0 G (Forall \<sigma> (App (Var 1) (Var 0))))"
    by (rule C_closure_congruence[OF F G body identity])
  then show ?thesis by (simp add: subst0_def shift_def)
qed

lemma C_forall_beta_step_identity:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and step: "compatible_step beta_contract A B"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall \<sigma> A) (Forall \<sigma> B)"
proof -
  have FA: "\<Gamma> \<turnstile> Forall \<sigma> A : Prop" by (rule has_type.Forall[OF A])
  have FB: "\<Gamma> \<turnstile> Forall \<sigma> B : Prop" by (rule has_type.Forall[OF B])
  have outer: "compatible_step beta_contract (Forall \<sigma> A) (Forall \<sigma> B)"
    by (rule compatible_step.Forall_body[OF step])
  show ?thesis by (rule C_closure_beta_identity[OF FA FB outer])
qed

lemma C_subst0_lifted_shift:
  "subst0 (Var 0) (rename (lift_ren Suc) A) = A"
  unfolding subst0_def
  by (rule subst_rename_inverse) (case_tac n; simp)

lemma C_forall_predicate_beta:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Forall \<sigma> (App (shift (Lam \<sigma> A)) (Var 0))) (Forall \<sigma> A)"
proof -
  have pred: "\<Gamma> \<turnstile> Lam \<sigma> A : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Lam[OF A])
  have shifted: "\<sigma> # \<Gamma> \<turnstile> shift (Lam \<sigma> A) :
    \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule weakening_front[OF pred])
  have var: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by auto
  have app: "\<sigma> # \<Gamma> \<turnstile> App (shift (Lam \<sigma> A)) (Var 0) : Prop"
    by (rule has_type.App[OF shifted var])
  have step: "compatible_step beta_contract (App (shift (Lam \<sigma> A)) (Var 0)) A"
  proof -
    have "compatible_step beta_contract
      (App (Lam \<sigma> (rename (lift_ren Suc) A)) (Var 0))
      (subst0 (Var 0) (rename (lift_ren Suc) A))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis by (simp add: shift_def C_subst0_lifted_shift)
  qed
  show ?thesis by (rule C_forall_beta_step_identity[OF app A step])
qed

lemma C_forall_of_predicate_identity:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and identity: "\<Gamma> \<turnstile>\<^sub>C
      Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall \<sigma> A) (Forall \<sigma> B)"
proof -
  let ?L = "Forall \<sigma> (App (shift (Lam \<sigma> A)) (Var 0))"
  let ?R = "Forall \<sigma> (App (shift (Lam \<sigma> B)) (Var 0))"
  have pred_A: "\<Gamma> \<turnstile> Lam \<sigma> A : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Lam[OF A])
  have pred_B: "\<Gamma> \<turnstile> Lam \<sigma> B : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Lam[OF B])
  have LR: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?L ?R"
    by (rule C_forall_predicate_congruence[OF pred_A pred_B identity])
  have LA: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?L (Forall \<sigma> A)"
    by (rule C_forall_predicate_beta[OF A])
  have RB: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?R (Forall \<sigma> B)"
    by (rule C_forall_predicate_beta[OF B])
  have L: "\<Gamma> \<turnstile> ?L : Prop"
    using C_proves_formula[OF LA] by (auto elim: has_type.cases)
  have R: "\<Gamma> \<turnstile> ?R : Prop"
    using C_proves_formula[OF RB] by (auto elim: has_type.cases)
  have FA: "\<Gamma> \<turnstile> Forall \<sigma> A : Prop" by (rule has_type.Forall[OF A])
  have FB: "\<Gamma> \<turnstile> Forall \<sigma> B : Prop" by (rule has_type.Forall[OF B])
  have AL: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall \<sigma> A) ?L"
    by (rule C_closure_eq_sym_from[OF L FA LA])
  have AR: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall \<sigma> A) ?R"
    by (rule C_closure_eq_trans_from[OF FA L R AL LR])
  show ?thesis by (rule C_closure_eq_trans_from[OF FA R FB AR RB])
qed

subsection \<open>Binary operations beneath a universal diagonal\<close>

text \<open>
  From ⊢C F =t→t→t G derive ⊢C (∀p.Fpp) =ₜ (∀p.Gpp).
  Source use: Bacon--Dorr Figure 1, p.6, and A.1, p.65,
  for the material-implication truth representative.

  Isabelle representation.  The same new slot is supplied to both arguments;
  C_binary_forall_diagonal_beta verifies the two β reductions.
  Status.  No pointwise-to-operation identity inference is introduced.
\<close>

lemma C_binary_forall_diagonal_congruence:
  assumes F: "\<Gamma> \<turnstile> F : prop_bin_ty"
    and G: "\<Gamma> \<turnstile> G : prop_bin_ty"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty F G"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Forall Prop (App (App (shift F) (Var 0)) (Var 0)))
    (Forall Prop (App (App (shift G) (Var 0)) (Var 0)))"
proof -
  have body: "prop_bin_ty # \<Gamma> \<turnstile>
    Forall Prop (App (App (Var 1) (Var 0)) (Var 0)) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def prop_bin_ty_def)
  have "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (subst0 F (Forall Prop (App (App (Var 1) (Var 0)) (Var 0))))
    (subst0 G (Forall Prop (App (App (Var 1) (Var 0)) (Var 0))))"
    by (rule C_closure_congruence[OF F G body identity])
  then show ?thesis by (simp add: subst0_def shift_def)
qed

lemma C_binary_forall_diagonal_beta:
  assumes P: "Prop # Prop # \<Gamma> \<turnstile> P : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Forall Prop (App (App (shift (Lam Prop (Lam Prop P))) (Var 0)) (Var 0)))
    (Forall Prop (subst0 (Var 0)
      (subst (lift_subst (case_nat (Var 0) Var))
        (rename (lift_ren (lift_ren Suc)) P))))"
proof -
  let ?F = "Lam Prop (Lam Prop P)"
  let ?P' = "rename (lift_ren (lift_ren Suc)) P"
  let ?Q = "subst (lift_subst (case_nat (Var 0) Var)) ?P'"
  let ?L = "App (App (shift ?F) (Var 0)) (Var 0)"
  let ?M = "App (Lam Prop ?Q) (Var 0)"
  let ?R = "subst0 (Var 0) ?Q"
  have F: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (intro has_type.Lam P)
  have shifted: "Prop # \<Gamma> \<turnstile> shift ?F :
    Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (rule weakening_front[OF F])
  have inner: "Prop # Prop # \<Gamma> \<turnstile> Lam Prop ?P' : Prop \<rightarrow>\<^sub>o Prop"
    using shifted unfolding shift_def by (auto elim: has_type.cases)
  have var: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule has_type.Var) simp
  have Q_lam: "Prop # \<Gamma> \<turnstile> Lam Prop ?Q : Prop \<rightarrow>\<^sub>o Prop"
    using subst0_preserves_typing[OF inner var] by (simp add: subst0_def)
  have Q: "Prop # Prop # \<Gamma> \<turnstile> ?Q : Prop"
    using Q_lam by (auto elim: has_type.cases)
  have first_app: "Prop # \<Gamma> \<turnstile> App (shift ?F) (Var 0) :
    Prop \<rightarrow>\<^sub>o Prop"
    by (rule has_type.App[OF shifted var])
  have L: "Prop # \<Gamma> \<turnstile> ?L : Prop"
    by (rule has_type.App[OF first_app var])
  have M: "Prop # \<Gamma> \<turnstile> ?M : Prop"
    by (rule has_type.App[OF Q_lam var])
  have R: "Prop # \<Gamma> \<turnstile> ?R : Prop"
    by (rule subst0_preserves_typing[OF Q var])
  have first: "compatible_step beta_contract ?L ?M"
  proof -
    have "compatible_step beta_contract
      (App (Lam Prop (Lam Prop ?P')) (Var 0))
      (subst0 (Var 0) (Lam Prop ?P'))"
      by (intro compatible_step.root beta_contract.beta)
    then have "compatible_step beta_contract (App (shift ?F) (Var 0)) (Lam Prop ?Q)"
      by (simp add: shift_def subst0_def)
    then show ?thesis by (rule compatible_step.App_left)
  qed
  have second: "compatible_step beta_contract ?M ?R"
    by (intro compatible_step.root beta_contract.beta)
  have LM: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall Prop ?L) (Forall Prop ?M)"
    by (rule C_forall_beta_step_identity[OF L M first])
  have MR: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall Prop ?M) (Forall Prop ?R)"
    by (rule C_forall_beta_step_identity[OF M R second])
  have FL: "\<Gamma> \<turnstile> Forall Prop ?L : Prop" by (rule has_type.Forall[OF L])
  have FM: "\<Gamma> \<turnstile> Forall Prop ?M : Prop" by (rule has_type.Forall[OF M])
  have FR: "\<Gamma> \<turnstile> Forall Prop ?R : Prop" by (rule has_type.Forall[OF R])
  show ?thesis by (rule C_closure_eq_trans_from[OF FL FM FR LM MR])
qed

subsection \<open>Primitive-basis bridge for the truth in Appendix A.1\<close>

text \<open>
  ⊢C ⊤₀ =ₜ ∀p.(¬p ∨ p).
  Source convention: Bacon--Dorr Figure 1, p.6; intended use A.1, p.65.

  Isabelle representation.  C_ObjTrue_material_basis applies the supplied
  material-implication operation identity beneath the quantified diagonal.
  Status.  This does not identify the result with ⊤ᴮ.
\<close>

lemma C_ObjTrue_material_basis:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop ObjTrue
    (Forall Prop (Disj (Neg (Var 0)) (Var 0)))"
proof -
  let ?F = "Lam Prop (Lam Prop (Imp (Var 1) (Var 0)))"
  let ?G = "Lam Prop (Lam Prop (Disj (Neg (Var 1)) (Var 0)))"
  let ?L = "Forall Prop (App (App (shift ?F) (Var 0)) (Var 0))"
  let ?R = "Forall Prop (App (App (shift ?G) (Var 0)) (Var 0))"
  let ?T = "Forall Prop (Disj (Neg (Var 0)) (Var 0))"
  have P: "Prop # Prop # \<Gamma> \<turnstile> Imp (Var 1) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # \<Gamma> \<turnstile> Disj (Neg (Var 1)) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have F: "\<Gamma> \<turnstile> ?F : prop_bin_ty"
    unfolding prop_bin_ty_def by (intro has_type.Lam P)
  have G: "\<Gamma> \<turnstile> ?G : prop_bin_ty"
    unfolding prop_bin_ty_def by (intro has_type.Lam Q)
  have FG: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty ?F ?G"
    by (rule C_closure_material_imp_operator)
  have LR: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?L ?R"
    by (rule C_binary_forall_diagonal_congruence[OF F G FG])
  have LU: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?L ObjTrue"
    using C_binary_forall_diagonal_beta[OF P]
    by (simp add: subst0_def ObjTrue_def)
  have RT: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?R ?T"
    using C_binary_forall_diagonal_beta[OF Q]
    by (simp add: subst0_def)
  have L: "\<Gamma> \<turnstile> ?L : Prop"
    using C_proves_formula[OF LU] by (auto elim: has_type.cases)
  have R: "\<Gamma> \<turnstile> ?R : Prop"
    using C_proves_formula[OF RT] by (auto elim: has_type.cases)
  have T: "\<Gamma> \<turnstile> ?T : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have UL: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ObjTrue ?L"
    by (rule C_closure_eq_sym_from[OF L typed_ObjTrue LU])
  have UR: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ObjTrue ?R"
    by (rule C_closure_eq_trans_from[OF typed_ObjTrue L R UL LR])
  show ?thesis by (rule C_closure_eq_trans_from[OF typed_ObjTrue R T UR RT])
qed

text \<open>
  The remaining Boolean-truth bridge is ⊢C ∀p.(¬p ∨ p) =ₜ ⊤ᴮ,
  where ⊤ᴮ := ⊤₀ ∨ ¬⊤₀.  Together with the theorem above it would give
  ⊢C ⊤₀ =ₜ ⊤ᴮ.  Locator: Bacon--Dorr Appendix A.2(i), p.65.

  Isabelle representation.  The left side is the Forall term in
  C_ObjTrue_material_basis; the right side is C_boolean_truth.
  Predicate-operation identities are needed to pass through ∀.

  Status.  Pointwise excluded-middle identities alone do not establish
  the required predicate identity.  The separate formula
  ⊢C (∀x:σ.⊤₀) =ₜ ⊤₀ is proved in Bacon_C_Appendix_A1 and should no
  longer be listed as an outstanding result of the development.
\<close>

end
