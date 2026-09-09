theory Bacon_C_Forall_Distribution_Vector
  imports Bacon_C_Vector_Quantifier_Congruence Bacon_C_Appendix_A2_UI
begin

section \<open>Source distribution beneath arbitrary vectors\<close>

text \<open>
  ⊢C (λv̄.(P ∨ ∀x:σ.B)) = (λv̄.∀x:σ.(P ∨ B)), where x
  does not occur free in P.  Source: Bacon–Dorr Figure 4, p.13,
  Distribution-∨∀; used in the Gen step of Appendix A.2, pp.65–66.
  Isabelle makes the proviso explicit by writing shift P beneath ∀.

  The proof replaces the closed source distribution operations inside a
  typed two-argument context and β-reduces their applications.  It does
  not abstract an arbitrary open C equation or use CE/CEV Equivalence.
\<close>

lemma C_vector_binary_function_congruence_beta:
  assumes F: "\<Gamma> \<turnstile> F : \<alpha> \<rightarrow>\<^sub>o \<beta> \<rightarrow>\<^sub>o \<rho>"
    and G: "\<Gamma> \<turnstile> G : \<alpha> \<rightarrow>\<^sub>o \<beta> \<rightarrow>\<^sub>o \<rho>"
    and X: "\<Delta> @ \<Gamma> \<turnstile> X : \<alpha>" and Y: "\<Delta> @ \<Gamma> \<turnstile> Y : \<beta>"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<alpha> \<rightarrow>\<^sub>o \<beta> \<rightarrow>\<^sub>o \<rho>) F G"
    and left: "beta_eta_equiv (\<Delta> @ \<Gamma>) \<rho>
      (App (App (C_vector_raise (length \<Delta>) F) X) Y) A"
    and right: "beta_eta_equiv (\<Delta> @ \<Gamma>) \<rho>
      (App (App (C_vector_raise (length \<Delta>) G) X) Y) B"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) \<rho>)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> B)"
proof -
  let ?n = "length \<Delta>"
  let ?K = "\<alpha> \<rightarrow>\<^sub>o \<beta> \<rightarrow>\<^sub>o \<rho>"
  let ?r = "C_vector_lift_ren ?n Suc"
  let ?M = "App (App (Var ?n) (rename ?r X)) (rename ?r Y)"
  have X': "\<Delta> @ (?K # \<Gamma>) \<turnstile> rename ?r X : \<alpha>" by (rule C_vector_insert_parameter_type[OF X])
  have Y': "\<Delta> @ (?K # \<Gamma>) \<turnstile> rename ?r Y : \<beta>" by (rule C_vector_insert_parameter_type[OF Y])
  have zero: "lookup (?K # \<Gamma>) 0 = Some ?K" by simp
  have index: "lookup (\<Delta> @ (?K # \<Gamma>)) ?n = Some ?K"
    using lookup_append_shift[OF zero, where \<Delta>=\<Delta>] by simp
  have variable: "\<Delta> @ (?K # \<Gamma>) \<turnstile> Var ?n : ?K" by (rule has_type.Var[OF index])
  have body: "\<Delta> @ (?K # \<Gamma>) \<turnstile> ?M : \<rho>"
    by (rule has_type.App[OF has_type.App[OF variable X'] Y'])
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) \<rho>)
    (C_abstract_prefix \<Delta> (App (App (C_vector_raise ?n F) X) Y))
    (C_abstract_prefix \<Delta> (App (App (C_vector_raise ?n G) X) Y))"
    using C_vector_identity_context[OF F G body identity]
    by (simp only: subst.simps C_vector_lift_subst_slot C_vector_remove_inserted_parameter)
  show ?thesis by (rule C_A1_transport[OF raw C_vector_conversion_identity[OF left]
    C_vector_conversion_identity[OF right]])
qed

definition C_Gen_dist_left :: "otype \<Rightarrow> oterm" where
  "C_Gen_dist_left \<sigma> = Lam (pred_ty \<sigma>) (Lam Prop
    (Disj (Var 0) (Forall \<sigma> (App (Var 2) (Var 0)))))"

definition C_Gen_dist_right :: "otype \<Rightarrow> oterm" where
  "C_Gen_dist_right \<sigma> = Lam (pred_ty \<sigma>) (Lam Prop
    (Forall \<sigma> (Disj (Var 1) (App (Var 2) (Var 0)))))"

lemma C_Gen_dist_types:
  "\<Gamma> \<turnstile> C_Gen_dist_left \<sigma> : pred_ty \<sigma> \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
  "\<Gamma> \<turnstile> C_Gen_dist_right \<sigma> : pred_ty \<sigma> \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"
  by (rule infer_type_sound; simp add: C_Gen_dist_left_def C_Gen_dist_right_def pred_ty_def lookup_def)+

lemma C_Gen_dist_identity:
  "\<Gamma> \<turnstile>\<^sub>C Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
    (C_Gen_dist_left \<sigma>) (C_Gen_dist_right \<sigma>)"
  using C_proves.DistDisjForall[of \<Gamma> \<sigma>]
  by (simp only: classic_dist_disj_forall_def C_Gen_dist_left_def C_Gen_dist_right_def)

lemma C_Gen_dist_closed:
  "C_vector_raise n (C_Gen_dist_left \<sigma>) = C_Gen_dist_left \<sigma>"
  "C_vector_raise n (C_Gen_dist_right \<sigma>) = C_Gen_dist_right \<sigma>"
  by (simp_all add: C_vector_raise_as_rename C_Gen_dist_left_def C_Gen_dist_right_def numeral_2_eq_2)

lemma C_Gen_predicate_body_beta:
  assumes B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "beta_eta_equiv (\<sigma> # \<Gamma>) Prop (App (shift (Lam \<sigma> B)) (Var 0)) B"
proof -
  have predicate: "\<Gamma> \<turnstile> Lam \<sigma> B : pred_ty \<sigma>"
    using has_type.Lam[OF B] by (simp only: pred_ty_def)
  have shifted: "\<sigma> # \<Gamma> \<turnstile> shift (Lam \<sigma> B) : \<sigma> \<rightarrow>\<^sub>o Prop"
    using weakening_front[OF predicate] by (simp only: pred_ty_def)
  have variable: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  have source: "\<sigma> # \<Gamma> \<turnstile> App (shift (Lam \<sigma> B)) (Var 0) : Prop"
    by (rule has_type.App[OF shifted variable])
  show ?thesis by (rule beta_eta_equiv.Beta[OF source B C_abstraction_argument_beta_step])
qed

lemma C_Gen_dist_left_beta:
  assumes B: "\<sigma> # \<Gamma> \<turnstile> B : Prop" and P: "\<Gamma> \<turnstile> P : Prop"
  shows "beta_eta_equiv \<Gamma> Prop (App (App (C_Gen_dist_left \<sigma>) (Lam \<sigma> B)) P)
    (Disj P (Forall \<sigma> B))"
proof -
  let ?body = "Disj (Var 0) (Forall \<sigma> (App (Var 2) (Var 0)))"
  have body: "Prop # pred_ty \<sigma> # \<Gamma> \<turnstile> ?body : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have predicate: "\<Gamma> \<turnstile> Lam \<sigma> B : pred_ty \<sigma>" using has_type.Lam[OF B] by (simp only: pred_ty_def)
  have first: "beta_eta_equiv \<Gamma> Prop (App (App (C_Gen_dist_left \<sigma>) (Lam \<sigma> B)) P)
    (Disj P (Forall \<sigma> (App (shift (Lam \<sigma> B)) (Var 0))))"
    using C_A2_binary_application_beta[OF body predicate P]
    by (simp add: C_Gen_dist_left_def subst0_def numeral_2_eq_2 C_subst_twice_raised
      C_subst_raised C_remove_inserted_operation C_A2_subst_twice_lifted shift_def)
  have second: "beta_eta_equiv \<Gamma> Prop
    (Disj P (Forall \<sigma> (App (shift (Lam \<sigma> B)) (Var 0)))) (Disj P (Forall \<sigma> B))"
    by (rule C_PC_beta_eta_Disj[OF beta_eta_equiv.Refl[OF P] C_UI_quantified_predicate_beta[OF B]])
  show ?thesis by (rule beta_eta_equiv.Trans[OF first second])
qed

lemma C_Gen_dist_right_beta:
  assumes B: "\<sigma> # \<Gamma> \<turnstile> B : Prop" and P: "\<Gamma> \<turnstile> P : Prop"
  shows "beta_eta_equiv \<Gamma> Prop (App (App (C_Gen_dist_right \<sigma>) (Lam \<sigma> B)) P)
    (Forall \<sigma> (Disj (shift P) B))"
proof -
  let ?body = "Forall \<sigma> (Disj (Var 1) (App (Var 2) (Var 0)))"
  have body: "Prop # pred_ty \<sigma> # \<Gamma> \<turnstile> ?body : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have predicate: "\<Gamma> \<turnstile> Lam \<sigma> B : pred_ty \<sigma>" using has_type.Lam[OF B] by (simp only: pred_ty_def)
  have first: "beta_eta_equiv \<Gamma> Prop (App (App (C_Gen_dist_right \<sigma>) (Lam \<sigma> B)) P)
    (Forall \<sigma> (Disj (shift P) (App (shift (Lam \<sigma> B)) (Var 0))))"
    using C_A2_binary_application_beta[OF body predicate P]
    by (simp add: C_Gen_dist_right_def subst0_def numeral_2_eq_2 C_subst_twice_raised
      C_subst_raised C_remove_inserted_operation C_A2_subst_twice_lifted shift_def)
  have shifted_P: "\<sigma> # \<Gamma> \<turnstile> shift P : Prop" by (rule weakening_front[OF P])
  have second: "beta_eta_equiv \<Gamma> Prop
    (Forall \<sigma> (Disj (shift P) (App (shift (Lam \<sigma> B)) (Var 0)))) (Forall \<sigma> (Disj (shift P) B))"
    by (rule C_PC_beta_eta_Forall[OF C_PC_beta_eta_Disj[
      OF beta_eta_equiv.Refl[OF shifted_P] C_Gen_predicate_body_beta[OF B]]])
  show ?thesis by (rule beta_eta_equiv.Trans[OF first second])
qed

theorem C_vector_disj_forall_distribution:
  assumes P: "\<Delta> @ \<Gamma> \<turnstile> P : Prop" and B: "\<sigma> # (\<Delta> @ \<Gamma>) \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Disj P (Forall \<sigma> B)))
    (C_abstract_prefix \<Delta> (Forall \<sigma> (Disj (shift P) B)))"
proof -
  have predicate: "\<Delta> @ \<Gamma> \<turnstile> Lam \<sigma> B : pred_ty \<sigma>"
    using has_type.Lam[OF B] by (simp only: pred_ty_def)
  have left: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (App (App (C_vector_raise (length \<Delta>) (C_Gen_dist_left \<sigma>)) (Lam \<sigma> B)) P)
    (Disj P (Forall \<sigma> B))"
    using C_Gen_dist_left_beta[OF B P] by (simp only: C_Gen_dist_closed)
  have right: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (App (App (C_vector_raise (length \<Delta>) (C_Gen_dist_right \<sigma>)) (Lam \<sigma> B)) P)
    (Forall \<sigma> (Disj (shift P) B))"
    using C_Gen_dist_right_beta[OF B P] by (simp only: C_Gen_dist_closed)
  show ?thesis by (rule C_vector_binary_function_congruence_beta[
    OF C_Gen_dist_types(1) C_Gen_dist_types(2) predicate P C_Gen_dist_identity left right])
qed

subsection \<open>Closed universal truth under a vector\<close>

lemma C_vector_raised_identity:
  assumes F: "\<Gamma> \<turnstile> F : \<tau>" and G: "\<Gamma> \<turnstile> G : \<tau>"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> F G"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) \<tau>)
    (C_abstract_prefix \<Delta> (C_vector_raise (length \<Delta>) F))
    (C_abstract_prefix \<Delta> (C_vector_raise (length \<Delta>) G))"
proof -
  have zero: "lookup (\<tau> # \<Gamma>) 0 = Some \<tau>" by simp
  have index: "lookup (\<Delta> @ (\<tau> # \<Gamma>)) (length \<Delta>) = Some \<tau>"
    using lookup_append_shift[OF zero, where \<Delta>=\<Delta>] by simp
  have body: "\<Delta> @ (\<tau> # \<Gamma>) \<turnstile> Var (length \<Delta>) : \<tau>" by (rule has_type.Var[OF index])
  show ?thesis using C_vector_identity_context[OF F G body identity]
    by (simp only: subst.simps C_vector_lift_subst_slot)
qed

lemma C_vector_forall_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Forall \<sigma> ObjTrue)) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall \<sigma> ObjTrue) ObjTrue"
    using C_Appendix_A1_universal_truth[where \<Gamma>=\<Gamma> and \<sigma>=\<sigma>] by (simp add: shift_def ObjTrue_def)
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (C_vector_raise (length \<Delta>) (Forall \<sigma> ObjTrue)))
    (C_abstract_prefix \<Delta> (C_vector_raise (length \<Delta>) ObjTrue))"
    by (rule C_vector_raised_identity[OF has_type.Forall[OF typed_ObjTrue] typed_ObjTrue identity])
  show ?thesis using raw by (simp add: C_vector_raise_as_rename ObjTrue_def)
qed

end
