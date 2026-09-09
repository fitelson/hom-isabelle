theory Bacon_C_Appendix_A2_MP
  imports Bacon_C_Vector_Beta_Evaluation Bacon_C_PC_Vector_Boolean_Equivalence
begin

section \<open>Modus ponens preserves vector truth identities\<close>

text \<open>
  From ⊢C (λv̄.A) = (λv̄.⊤₀) and
  ⊢C (λv̄.(A → B)) = (λv̄.⊤₀), derive
  ⊢C (λv̄.B) = (λv̄.⊤₀).
  Source: the MP induction step of Bacon–Dorr Appendix A.2, pp.65–66.

  Isabelle representation.  Supplied identities of ambient operations
  are replaced inside an explicitly typed evaluation context.  Applying
  the operations to the reversed fresh-variable vector β-reduces to
  their bodies.  Boolean equivalence identifies A ∧ (A → B) with A ∧ B.
  The unit ⊤₀ ∧ B = B is obtained from a proved closed one-variable
  operation identity, not from treating ObjTrue as a fixed-true PC atom.

  Status.  The final theorem has exactly the two vector-identity premises;
  their typing is recovered below.  No arbitrary open-equation abstraction,
  C Equivalence, CE/CEV rule, or semantic completeness premise is used.
\<close>

lemma C_vector_lift_subst_below:
  "i < n \<Longrightarrow> C_vector_lift_subst n s i = Var i"
proof (induction n arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (cases i) simp_all
qed

lemma C_vector_subst_reverse_fresh_vars:
  "map (subst (C_vector_lift_subst n s)) (rev (fresh_vars n)) = rev (fresh_vars n)"
proof -
  have fixed: "map (subst (C_vector_lift_subst n s)) (map Var [0..<n]) = map Var [0..<n]"
  proof (unfold map_map comp_def, rule map_cong[OF refl])
    fix i
    assume member: "i \<in> set [0..<n]"
    have bound: "i < n" using member by simp
    show "subst (C_vector_lift_subst n s) (Var i) = Var i"
      by (simp only: subst.simps C_vector_lift_subst_below[OF bound])
  qed
  show ?thesis using fixed by (simp only: fresh_vars_def rev_map[symmetric])
qed

lemma C_vector_conj_evaluation_subst:
  "subst (C_vector_lift_subst n (case_nat F Var))
    (Conj (app_vec (Var n) (rev (fresh_vars n))) (rename (C_vector_lift_ren n Suc) B)) =
    Conj (app_vec (C_vector_raise n F) (rev (fresh_vars n))) B"
  by (simp only: subst.simps C_Church_subst_app_vec C_vector_lift_subst_slot
    C_vector_subst_reverse_fresh_vars C_vector_remove_inserted_parameter)

lemma C_vector_conj_congruence_left:
  assumes A: "\<Delta> @ \<Gamma> \<turnstile> A : Prop" and A': "\<Delta> @ \<Gamma> \<turnstile> A' : Prop"
    and B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
      (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> A')"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj A B)) (C_abstract_prefix \<Delta> (Conj A' B))"
proof -
  let ?n = "length \<Delta>"
  let ?\<nu> = "arrow_type (rev \<Delta>) Prop"
  let ?F = "C_abstract_prefix \<Delta> A"
  let ?G = "C_abstract_prefix \<Delta> A'"
  let ?eval = "app_vec (Var ?n) (rev (fresh_vars ?n))"
  let ?body = "Conj ?eval (rename (C_vector_lift_ren ?n Suc) B)"
  have F: "\<Gamma> \<turnstile> ?F : ?\<nu>" by (rule C_abstract_prefix_type[OF A])
  have G: "\<Gamma> \<turnstile> ?G : ?\<nu>" by (rule C_abstract_prefix_type[OF A'])
  have zero: "lookup (?\<nu> # \<Gamma>) 0 = Some ?\<nu>" by simp
  have index: "lookup (\<Delta> @ (?\<nu> # \<Gamma>)) ?n = Some ?\<nu>"
    using lookup_append_shift[OF zero, where \<Delta>=\<Delta>] by simp
  have operator: "\<Delta> @ (?\<nu> # \<Gamma>) \<turnstile> Var ?n : ?\<nu>" by (rule has_type.Var[OF index])
  have eval_type: "\<Delta> @ (?\<nu> # \<Gamma>) \<turnstile> ?eval : Prop"
    by (rule typed_app_vec[OF operator C_vector_reverse_fresh_vars_type])
  have inserted_B: "\<Delta> @ (?\<nu> # \<Gamma>) \<turnstile> rename (C_vector_lift_ren ?n Suc) B : Prop"
    by (rule C_vector_insert_parameter_type[OF B])
  have body_type: "\<Delta> @ (?\<nu> # \<Gamma>) \<turnstile> ?body : Prop"
    by (rule has_type.Conj[OF eval_type inserted_B])
  have raw: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj (app_vec (C_vector_raise ?n ?F) (rev (fresh_vars ?n))) B))
    (C_abstract_prefix \<Delta> (Conj (app_vec (C_vector_raise ?n ?G) (rev (fresh_vars ?n))) B))"
    using C_vector_identity_context[OF F G body_type identity]
    by (simp only: C_vector_conj_evaluation_subst)
  have left: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (Conj (app_vec (C_vector_raise ?n ?F) (rev (fresh_vars ?n))) B) (Conj A B)"
    by (rule C_PC_beta_eta_Conj[OF C_vector_deabstract_beta_eta[OF A] beta_eta_equiv.Refl[OF B]])
  have right: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop
    (Conj (app_vec (C_vector_raise ?n ?G) (rev (fresh_vars ?n))) B) (Conj A' B)"
    by (rule C_PC_beta_eta_Conj[OF C_vector_deabstract_beta_eta[OF A'] beta_eta_equiv.Refl[OF B]])
  show ?thesis by (rule C_A1_transport[OF raw C_vector_conversion_identity[OF left]
    C_vector_conversion_identity[OF right]])
qed

subsection \<open>The vector truth unit comes from a closed operation identity\<close>

lemma C_vector_conj_true_left:
  assumes B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj ObjTrue B)) (C_abstract_prefix \<Delta> B)"
proof -
  let ?F = "Lam Prop (Conj ObjTrue (Var 0))"
  let ?G = "Lam Prop (Var 0)"
  have variable: "Prop # \<Gamma> \<turnstile> Var 0 : Prop" by (rule has_type.Var) simp
  have F: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop"
    by (rule has_type.Lam[OF has_type.Conj[OF typed_ObjTrue variable]])
  have G: "\<Gamma> \<turnstile> ?G : Prop \<rightarrow>\<^sub>o Prop" by (rule has_type.Lam[OF variable])
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq (Prop \<rightarrow>\<^sub>o Prop) ?F ?G"
    by (rule C_boolean_lambda_conj_true_left[OF variable])
  have raised_F: "C_vector_raise (length \<Delta>) ?F = ?F"
    and raised_G: "C_vector_raise (length \<Delta>) ?G = ?G"
    by (simp_all add: C_vector_raise_as_rename ObjTrue_def)
  have source_F: "\<Delta> @ \<Gamma> \<turnstile> App (C_vector_raise (length \<Delta>) ?F) B : Prop"
    by (rule has_type.App[OF C_vector_raise_type[OF F] B])
  have source_G: "\<Delta> @ \<Gamma> \<turnstile> App (C_vector_raise (length \<Delta>) ?G) B : Prop"
    by (rule has_type.App[OF C_vector_raise_type[OF G] B])
  have target_F: "\<Delta> @ \<Gamma> \<turnstile> Conj ObjTrue B : Prop" by (rule has_type.Conj[OF typed_ObjTrue B])
  have raw_F: "compatible_step beta_contract (App ?F B) (subst0 B (Conj ObjTrue (Var 0)))"
    by (rule compatible_step.root[where R=beta_contract]) (rule beta_contract.beta)
  have step_F: "compatible_step beta_contract (App (C_vector_raise (length \<Delta>) ?F) B) (Conj ObjTrue B)"
    using raw_F by (simp only: raised_F; simp add: subst0_def ObjTrue_def)
  have raw_G: "compatible_step beta_contract (App ?G B) (subst0 B (Var 0))"
    by (rule compatible_step.root[where R=beta_contract]) (rule beta_contract.beta)
  have step_G: "compatible_step beta_contract (App (C_vector_raise (length \<Delta>) ?G) B) B"
    using raw_G by (simp only: raised_G; simp add: subst0_def)
  have left: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop (App (C_vector_raise (length \<Delta>) ?F) B) (Conj ObjTrue B)"
    by (rule beta_eta_equiv.Beta[OF source_F target_F step_F])
  have right: "beta_eta_equiv (\<Delta> @ \<Gamma>) Prop (App (C_vector_raise (length \<Delta>) ?G) B) B"
    by (rule beta_eta_equiv.Beta[OF source_G B step_G])
  show ?thesis by (rule C_vector_function_congruence_beta[OF F G B identity left right])
qed

subsection \<open>Recovering body typing from the supplied identities\<close>

lemma C_lam_vec_type_reflect:
  assumes typed: "\<Gamma> \<turnstile> C_lam_vec \<sigma>s A : arrow_type \<sigma>s \<tau>"
  shows "rev \<sigma>s @ \<Gamma> \<turnstile> A : \<tau>"
  using typed
proof (induction \<sigma>s arbitrary: \<Gamma>)
  case Nil
  then show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  have body: "\<sigma> # \<Gamma> \<turnstile> C_lam_vec \<sigma>s A : arrow_type \<sigma>s \<tau>"
    using Cons.prems by (auto elim: has_type.cases)
  have tail: "rev \<sigma>s @ (\<sigma> # \<Gamma>) \<turnstile> A : \<tau>" by (rule Cons.IH[OF body])
  show ?case using tail by (simp add: append_assoc)
qed

lemma C_vector_truth_identity_body_type:
  assumes identity: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> ObjTrue)"
  shows "\<Delta> @ \<Gamma> \<turnstile> A : Prop"
proof -
  have formula: "\<Gamma> \<turnstile> Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> ObjTrue) : Prop"
    by (rule C_proves_formula[OF identity])
  have abstract_type: "\<Gamma> \<turnstile> C_abstract_prefix \<Delta> A : arrow_type (rev \<Delta>) Prop"
    using formula by (auto elim: has_type.cases)
  have body: "rev (rev \<Delta>) @ \<Gamma> \<turnstile> A : Prop"
    by (rule C_lam_vec_type_reflect[OF abstract_type[unfolded C_abstract_prefix_def]])
  show ?thesis using body by simp
qed

theorem C_A2_MP_vector:
  assumes A_truth: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
      (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> ObjTrue)"
    and implication_truth: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
      (C_abstract_prefix \<Delta> (Imp A B)) (C_abstract_prefix \<Delta> ObjTrue)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> B) (C_abstract_prefix \<Delta> ObjTrue)"
proof -
  have I: "\<Delta> @ \<Gamma> \<turnstile> Imp A B : Prop" by (rule C_vector_truth_identity_body_type[OF implication_truth])
  have A: "\<Delta> @ \<Gamma> \<turnstile> A : Prop" and B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop"
    using I by (auto elim: has_type.cases)
  have L_truth: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj A (Imp A B))) (C_abstract_prefix \<Delta> ObjTrue)"
    by (rule C_A1_trans[OF C_vector_conj_congruence_left[OF A typed_ObjTrue I A_truth]
      C_A1_trans[OF C_vector_conj_true_left[OF I] implication_truth]])
  have R_B: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj A B)) (C_abstract_prefix \<Delta> B)"
    by (rule C_A1_trans[OF C_vector_conj_congruence_left[OF A typed_ObjTrue B A_truth]
      C_vector_conj_true_left[OF B]])
  have boolean: "prop_tautology (\<Delta> @ \<Gamma>) (Conj A (Imp A B) \<longleftrightarrow>\<^sub>o Conj A B)"
    unfolding prop_tautology_def using A B I by auto
  have equivalent: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> (Conj A (Imp A B))) (C_abstract_prefix \<Delta> (Conj A B))"
    by (rule C_PC_boolean_equivalence_vector_abstraction[OF boolean])
  have truth_B: "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> ObjTrue) (C_abstract_prefix \<Delta> B)"
    by (rule C_A1_transport[OF equivalent L_truth R_B])
  show ?thesis by (rule C_A1_sym[OF truth_B])
qed

end
