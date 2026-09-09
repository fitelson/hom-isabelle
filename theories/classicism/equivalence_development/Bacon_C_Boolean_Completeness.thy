theory Bacon_C_Boolean_Completeness
  imports Bacon_C_Primitive_Basis
begin

section \<open>Preparation for Appendix A.2: Boolean equations under abstraction\<close>

text \<open>
  The target PC case is: if P is a propositional tautology, then
  ⊢C (λv̄.P) = (λv̄.⊤₀), for every typed abstraction vector v̄.
  Sources: Bacon--Dorr Appendix A.2(i), p.65; Bacon, Theorem 6.1,
  printed p.126.  Here ⊤₀ := ∀p.(p → p).

  Isabelle representation.  C_lam_vec [σ₁,…,σₙ] P represents
  λx₁:σ₁.…λxₙ:σₙ.P.  Its body context lists the innermost type first.
  C_abstract_prefix reverses a context prefix before abstraction.

  Status.  This file establishes typing and replacement of supplied
  operation identities beneath vectors.  Despite the filename, it does
  not prove general Boolean equational completeness or the entire PC case.
\<close>

subsection \<open>Iterated abstraction and its type\<close>

text \<open>
  If P:τ under v̄ of types σ₁,…,σₙ, then
  λv̄.P : σ₁ → ⋯ → σₙ → τ.
  Source convention: Bacon--Dorr A.2, p.65, and §1.1, p.5.

  Isabelle representation.  C_lam_vec follows outer-to-inner binder order;
  C_abstract_prefix uses the reverse of the context prefix.
  Status.  These equations and lemmas establish syntax, types, and free-slot bookkeeping only.
\<close>

fun C_lam_vec :: "otype list \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_lam_vec [] M = M"
| "C_lam_vec (\<sigma> # \<sigma>s) M = Lam \<sigma> (C_lam_vec \<sigma>s M)"

definition C_abstract_prefix :: "ctx \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_abstract_prefix \<Delta> M = C_lam_vec (rev \<Delta>) M"

lemma C_lam_vec_append:
  "C_lam_vec (\<sigma>s @ \<tau>s) M = C_lam_vec \<sigma>s (C_lam_vec \<tau>s M)"
  by (induction \<sigma>s) simp_all

lemma C_arrow_type_append:
  "arrow_type (\<sigma>s @ \<tau>s) \<upsilon> =
    arrow_type \<sigma>s (arrow_type \<tau>s \<upsilon>)"
  by (induction \<sigma>s) simp_all

lemma C_lam_vec_type:
  assumes "rev \<sigma>s @ \<Gamma> \<turnstile> M : \<tau>"
  shows "\<Gamma> \<turnstile> C_lam_vec \<sigma>s M : arrow_type \<sigma>s \<tau>"
  using assms
proof (induction \<sigma>s arbitrary: \<Gamma>)
  case Nil
  then show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  have body: "rev \<sigma>s @ (\<sigma> # \<Gamma>) \<turnstile> M : \<tau>"
    using Cons.prems by (simp add: append_assoc)
  have inner: "\<sigma> # \<Gamma> \<turnstile> C_lam_vec \<sigma>s M : arrow_type \<sigma>s \<tau>"
    using Cons.IH[OF body] .
  have "\<Gamma> \<turnstile> Lam \<sigma> (C_lam_vec \<sigma>s M) :
    \<sigma> \<rightarrow>\<^sub>o arrow_type \<sigma>s \<tau>"
    by (rule has_type.Lam[OF inner])
  then show ?case by simp
qed

lemma C_abstract_prefix_type:
  assumes "\<Delta> @ \<Gamma> \<turnstile> M : \<tau>"
  shows "\<Gamma> \<turnstile> C_abstract_prefix \<Delta> M : arrow_type (rev \<Delta>) \<tau>"
  unfolding C_abstract_prefix_def
  by (rule C_lam_vec_type) (simp add: assms)

lemma C_abstract_context_type:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
  shows "[] \<turnstile> C_abstract_prefix \<Gamma> M : arrow_type (rev \<Gamma>) \<tau>"
  using C_abstract_prefix_type[where \<Delta> = \<Gamma> and \<Gamma> = "[]" and M = M and \<tau> = \<tau>]
    assms by simp

lemma C_abstract_truth_type:
  "[] \<turnstile> C_abstract_prefix \<Gamma> ObjTrue : arrow_type (rev \<Gamma>) Prop"
  by (rule C_abstract_context_type) (rule typed_ObjTrue)

lemma C_abstract_prefix_empty[simp]:
  "C_abstract_prefix [] M = M"
  by (simp add: C_abstract_prefix_def)

lemma C_abstract_prefix_cons:
  "C_abstract_prefix (\<sigma> # \<Delta>) M =
    C_abstract_prefix \<Delta> (Lam \<sigma> M)"
  by (simp add: C_abstract_prefix_def C_lam_vec_append)

lemma C_abstract_prefix_append:
  "C_abstract_prefix (\<Delta> @ \<Xi>) M =
    C_abstract_prefix \<Xi> (C_abstract_prefix \<Delta> M)"
  by (simp add: C_abstract_prefix_def C_lam_vec_append)

lemma C_lam_vec_free_in:
  "free_in n (C_lam_vec \<sigma>s M) = free_in (n + length \<sigma>s) M"
  by (induction \<sigma>s arbitrary: n) simp_all

lemma C_abstract_prefix_free_in:
  "free_in n (C_abstract_prefix \<Delta> M) = free_in (n + length \<Delta>) M"
  by (simp add: C_abstract_prefix_def C_lam_vec_free_in)

subsection \<open>Typed vector application\<close>

text \<open>
  Applying λv̄.P to a matching argument vector yields a term of type τ.
  Source convention: Bacon--Dorr A.2, pp.65–66, applications to v̄.

  Isabelle representation.  app_vec and fresh_vars build the successive
  applications in the extended context.
  Status.  These are typing lemmas, not an abstraction-congruence principle.
\<close>

lemma C_lam_vec_application_type:
  assumes body: "rev \<sigma>s @ \<Gamma> \<turnstile> M : \<tau>"
    and args: "list_all2 (\<lambda>A \<sigma>. \<Gamma> \<turnstile> A : \<sigma>) As \<sigma>s"
  shows "\<Gamma> \<turnstile> app_vec (C_lam_vec \<sigma>s M) As : \<tau>"
  by (rule typed_app_vec[OF C_lam_vec_type[OF body] args])

lemma C_abstract_prefix_application_type:
  assumes body: "\<Delta> @ \<Gamma> \<turnstile> M : \<tau>"
    and args: "list_all2 (\<lambda>A \<sigma>. \<Gamma> \<turnstile> A : \<sigma>) As (rev \<Delta>)"
  shows "\<Gamma> \<turnstile> app_vec (C_abstract_prefix \<Delta> M) As : \<tau>"
  by (rule typed_app_vec[OF C_abstract_prefix_type[OF body] args])

lemma C_abstract_prefix_fresh_application_type:
  assumes "\<Delta> @ \<Gamma> \<turnstile> M : \<tau>"
  shows "rev \<Delta> @ \<Gamma> \<turnstile>
    app_vec (shift_by (length \<Delta>) (C_abstract_prefix \<Delta> M))
      (fresh_vars (length \<Delta>)) : \<tau>"
proof -
  have abstract_type: "\<Gamma> \<turnstile> C_abstract_prefix \<Delta> M :
    arrow_type (rev \<Delta>) \<tau>"
    using assms by (rule C_abstract_prefix_type)
  have "rev \<Delta> @ \<Gamma> \<turnstile>
    app_vec (shift_by (length (rev \<Delta>)) (C_abstract_prefix \<Delta> M))
      (fresh_vars (length (rev \<Delta>))) : \<tau>"
    by (rule typed_app_fresh_vars[OF abstract_type])
  then show ?thesis by simp
qed

subsection \<open>Boolean operation replacement beneath abstraction\<close>

text \<open>
  From ⊢C F =ν G we may replace the operation parameter X beneath a
  vector: ⊢C (λv̄.M)[F/X] = (λv̄.M)[G/X].
  Sources: Bacon--Dorr Figure 2, p.8, LL and β; Appendix A.2, pp.65–66,
  where the Boolean operation identities are used beneath λv̄.

  Isabelle representation.  The body has an extra ν-typed slot outside
  the prefix Δ.  C_abstract_prefix abstracts Δ while leaving that slot
  available for subst0.  The result type is arrow_type (rev Δ) τ.

  Status.  This replaces identical operations in one fixed context.
  It is not the inference from an arbitrary open equation P = Q to
  (λx.P) = (λx.Q).  No Functionality or Equivalence rule is assumed.
\<close>

lemma C_identity_under_abstraction:
  assumes F_type: "\<Gamma> \<turnstile> F : \<nu>"
    and G_type: "\<Gamma> \<turnstile> G : \<nu>"
    and body: "\<Delta> @ (\<nu> # \<Gamma>) \<turnstile> M : \<tau>"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<nu> F G"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) \<tau>)
    (subst0 F (C_abstract_prefix \<Delta> M))
    (subst0 G (C_abstract_prefix \<Delta> M))"
proof -
  have abstract_type: "\<nu> # \<Gamma> \<turnstile> C_abstract_prefix \<Delta> M :
    arrow_type (rev \<Delta>) \<tau>"
    using body by (rule C_abstract_prefix_type)
  show ?thesis
    by (rule C_closure_congruence[OF F_type G_type abstract_type identity])
qed

lemma C_boolean_axiom_under_abstraction:
  assumes axiom: "Eq \<nu> F G \<in> set all_boolean_identities"
    and body: "\<Delta> @ (\<nu> # \<Gamma>) \<turnstile> M : \<tau>"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) \<tau>)
    (subst0 F (C_abstract_prefix \<Delta> M))
    (subst0 G (C_abstract_prefix \<Delta> M))"
proof -
  have eq_type: "\<Gamma> \<turnstile> Eq \<nu> F G : Prop"
    using axiom by (rule typed_boolean_identity)
  have F_type: "\<Gamma> \<turnstile> F : \<nu>"
    using eq_type by (auto elim: has_type.cases)
  have G_type: "\<Gamma> \<turnstile> G : \<nu>"
    using eq_type by (auto elim: has_type.cases)
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<nu> F G"
    by (rule C_proves.BooleanIdentity[OF axiom])
  show ?thesis
    by (rule C_identity_under_abstraction[OF F_type G_type body identity])
qed

subsection \<open>Binary Boolean identities at arbitrary propositions\<close>

text \<open>
  An operation identity (λpq.P) = (λpq.Q) yields
  ⊢C P[A/p,B/q] =ₜ Q[A/p,B/q].  In particular,
  ⊢C A ∧ B =ₜ B ∧ A and ⊢C A ∨ B =ₜ B ∨ A.
  Source: Bacon--Dorr Figure 3, p.10.

  Isabelle representation.  C_binary_operator_identity_instance carries out
  two applications and their β reductions.
  Status.  These instances do not constitute the full PC case of A.2.
\<close>

lemma C_binary_operator_identity_instance:
  assumes P_type: "Prop # Prop # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "Prop # Prop # \<Gamma> \<turnstile> Q : Prop"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty
      (Lam Prop (Lam Prop P)) (Lam Prop (Lam Prop Q))"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (subst0 B (subst (lift_subst (case_nat A Var)) P))
    (subst0 B (subst (lift_subst (case_nat A Var)) Q))"
proof -
  let ?F = "Lam Prop (Lam Prop P)"
  let ?G = "Lam Prop (Lam Prop Q)"
  let ?L = "App (App ?F A) B"
  let ?R = "App (App ?G A) B"
  let ?U = "subst0 B (subst (lift_subst (case_nat A Var)) P)"
  let ?V = "subst0 B (subst (lift_subst (case_nat A Var)) Q)"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (intro has_type.Lam P_type)
  have G_type: "\<Gamma> \<turnstile> ?G : Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
    by (intro has_type.Lam Q_type)
  have FG: "\<Gamma> \<turnstile>\<^sub>C
    Eq (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop) ?F ?G"
    using identity by (simp add: prop_bin_ty_def)
  have FA_type: "\<Gamma> \<turnstile> App ?F A : Prop \<rightarrow>\<^sub>o Prop"
    using F_type A_type by auto
  have GA_type: "\<Gamma> \<turnstile> App ?G A : Prop \<rightarrow>\<^sub>o Prop"
    using G_type A_type by auto
  have FA_GA: "\<Gamma> \<turnstile>\<^sub>C
    Eq (Prop \<rightarrow>\<^sub>o Prop) (App ?F A) (App ?G A)"
    by (rule C_closure_app_congruence_left[OF F_type G_type A_type FG])
  have LR: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?L ?R"
    by (rule C_closure_app_congruence_left[OF FA_type GA_type B_type FA_GA])
  have LU: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?L ?U"
    by (rule C_closure_binary_beta_identity[OF P_type A_type B_type])
  have RV: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?R ?V"
    by (rule C_closure_binary_beta_identity[OF Q_type A_type B_type])
  have L_type: "\<Gamma> \<turnstile> ?L : Prop"
    using FA_type B_type by auto
  have R_type: "\<Gamma> \<turnstile> ?R : Prop"
    using GA_type B_type by auto
  have U_type: "\<Gamma> \<turnstile> ?U : Prop"
    using C_proves_formula[OF LU] by (auto elim: has_type.cases)
  have V_type: "\<Gamma> \<turnstile> ?V : Prop"
    using C_proves_formula[OF RV] by (auto elim: has_type.cases)
  have UL: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?U ?L"
    by (rule C_closure_eq_sym_from[OF L_type U_type LU])
  have UR: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?U ?R"
    by (rule C_closure_eq_trans_from[OF U_type L_type R_type UL LR])
  show ?thesis by (rule C_closure_eq_trans_from[OF U_type R_type V_type UR RV])
qed

lemma C_boolean_conj_commutes:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Conj A B) (Conj B A)"
proof -
  have P_type: "Prop # Prop # \<Gamma> \<turnstile> Conj (Var 1) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q_type: "Prop # Prop # \<Gamma> \<turnstile> Conj (Var 0) (Var 1) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have axiom: "\<Gamma> \<turnstile>\<^sub>C bool_comm_conj"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty
    (Lam Prop (Lam Prop (Conj (Var 1) (Var 0))))
    (Lam Prop (Lam Prop (Conj (Var 0) (Var 1))))"
    using axiom by (simp add: bool_comm_conj_def)
  have cancel_A: "subst (case_nat B Var) (rename Suc A) = A"
    using subst0_shift[of B A] by (simp only: subst0_def shift_def)
  show ?thesis
    using C_binary_operator_identity_instance[OF P_type Q_type A_type B_type identity]
    by (simp add: subst0_def cancel_A)
qed

lemma C_boolean_disj_commutes:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj A B) (Disj B A)"
proof -
  have P_type: "Prop # Prop # \<Gamma> \<turnstile> Disj (Var 1) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q_type: "Prop # Prop # \<Gamma> \<turnstile> Disj (Var 0) (Var 1) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have axiom: "\<Gamma> \<turnstile>\<^sub>C bool_comm_disj"
    by (rule C_proves.BooleanIdentity) (simp add: all_boolean_identities_def)
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq prop_bin_ty
    (Lam Prop (Lam Prop (Disj (Var 1) (Var 0))))
    (Lam Prop (Lam Prop (Disj (Var 0) (Var 1))))"
    using axiom by (simp add: bool_comm_disj_def)
  have cancel_A: "subst (case_nat B Var) (rename Suc A) = A"
    using subst0_shift[of B A] by (simp only: subst0_def shift_def)
  show ?thesis
    using C_binary_operator_identity_instance[OF P_type Q_type A_type B_type identity]
    by (simp add: subst0_def cancel_A)
qed

text \<open>
  Remaining source obligation: for every propositional tautology P,
  prove ⊢C (λv̄.P) = (λv̄.⊤₀).
  Locator: Bacon--Dorr Appendix A.2(i), p.65.

  Representation and status.  C_abstract_prefix supplies the required
  vectors, but the commutativity instances below do not supply a general
  normalization theorem.  The chosen Boolean truth representative must
  also be identified with ObjTrue rather than silently substituted for it.
\<close>

end
