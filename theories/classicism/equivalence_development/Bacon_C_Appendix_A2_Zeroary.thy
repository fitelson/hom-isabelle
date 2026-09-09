theory Bacon_C_Appendix_A2_Zeroary
  imports Bacon_C_Appendix_A1
begin

section \<open>Appendix A.2: verified zeroary reductions and remaining prerequisites\<close>

text \<open>
  The zero-vector target is: from ⊢C P, infer ⊢C P =ₜ ⊤₀.
  The source proves the stronger vector statement
  ⊢C (λv̄.P) = (λv̄.⊤).
  Locator: Bacon--Dorr Proposition A.2, pp.65–67.

  Isabelle representation.  The formulas below use ObjTrue, denoted
  ⊤₀ := ∀p.(p → p), and retain the C derivability subscript.  An
  assumption named truth_bridge or reflexive_case is a displayed premise,
  not a new constructor or axiom of C.

  Status.  This file supplies small base cases and conditional reductions.
  It does not prove the general PC case, the complete Ref case, or the
  vector induction needed by Gen and Inst.
\<close>

subsection \<open>Immediate truth cases\<close>

text \<open>
  ⊢C ⊤₀ =ₜ ⊤₀ and ⊢C (∀x:σ.⊤₀) =ₜ ⊤₀.
  Sources: Bacon--Dorr Figure 2, p.8, Ref; A.1, p.65.

  Isabelle representation.  The second lemma reuses C_Appendix_A1_universal_truth.
  Status.  These are genuine completed zero-vector cases.
\<close>

lemma C_A2_ObjTrue_case:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop ObjTrue ObjTrue"
  by (intro C_proves.H H_proves.Ref typed_ObjTrue)

lemma C_A2_universal_truth_case:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall \<sigma> (shift ObjTrue)) ObjTrue"
  by (rule C_Appendix_A1_universal_truth)

subsection \<open>Appendix A.2(i): two PC families, with the truth bridge explicit\<close>

text \<open>
  Assuming ⊢C ⊤ᴮ =ₜ ⊤₀, derive
  ⊢C (A ∨ ¬A) =ₜ ⊤₀ and ⊢C (A → A) =ₜ ⊤₀.
  Locator: Bacon--Dorr A.2(i), p.65.

  Isabelle representation.  truth_bridge is the stated identity premise.
  Status.  Its proof is not supplied by these two conditional lemmas.
\<close>

lemma C_A2_excluded_middle_assuming_truth_bridge:
  assumes A: "\<Gamma> \<turnstile> A : Prop"
    and truth_bridge: "\<Gamma> \<turnstile>\<^sub>C Eq Prop C_boolean_truth ObjTrue"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj A (Neg A)) ObjTrue"
  by (rule C_A1_trans[OF C_boolean_excluded_middle_to_truth[OF A] truth_bridge])

lemma C_A2_self_implication_assuming_truth_bridge:
  assumes A: "\<Gamma> \<turnstile> A : Prop"
    and truth_bridge: "\<Gamma> \<turnstile>\<^sub>C Eq Prop C_boolean_truth ObjTrue"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Imp A A) ObjTrue"
  by (rule C_A1_trans[OF C_boolean_self_implication_to_truth[OF A] truth_bridge])

text \<open>
  These establish two families, A ∨ ¬A and A → A, conditional on
  ⊢C ⊤ᴮ =ₜ ⊤₀.  Locator: Bacon--Dorr Appendix A.2(i), p.65.

  Representation and status.  truth_bridge is still an assumption.
  These conditional results are not the general PC case and do not
  discharge the identity of C_boolean_truth with ObjTrue.
\<close>

subsection \<open>Appendix A.2(ix): identity axioms reduce to reflexive identity\<close>

text \<open>
  From ⊢C M =σ N derive ⊢C (M =σ N) =ₜ (M =σ M).
  If ⊢C (M =σ M) =ₜ ⊤₀ is also available, conclude
  ⊢C (M =σ N) =ₜ ⊤₀.
  Locator: Bacon--Dorr A.2(ix), p.66.

  Isabelle representation.  The final specializations inspect the Boolean
  and Classicist axiom constructors and retain reflexive_case explicitly.
  Status.  Proving ⊢C M =σ M alone does not discharge that premise.
\<close>

lemma C_A2_identity_reduces_to_reflexivity:
  assumes identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> M N"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Eq \<sigma> M N) (Eq \<sigma> M M)"
proof -
  have M: "\<Gamma> \<turnstile> M : \<sigma>" and N: "\<Gamma> \<turnstile> N : \<sigma>"
    using C_proves_formula[OF identity] by (auto elim: has_type.cases)
  have shifted_M: "\<sigma> # \<Gamma> \<turnstile> shift M : \<sigma>"
    by (rule weakening_front[OF M])
  have var: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  have body: "\<sigma> # \<Gamma> \<turnstile> Eq \<sigma> (shift M) (Var 0) : Prop"
    by (rule has_type.Eq[OF shifted_M var])
  have reverse_identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> N M"
    by (rule C_A1_sym[OF identity])
  have "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (subst0 N (Eq \<sigma> (shift M) (Var 0)))
    (subst0 M (Eq \<sigma> (shift M) (Var 0)))"
    by (rule C_closure_congruence[OF N M body reverse_identity])
  then show ?thesis by (simp add: subst0_def)
qed

lemma C_A2_identity_case_assuming_reflexive_case:
  assumes identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> M N"
    and reflexive_case: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Eq \<sigma> M M) ObjTrue"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Eq \<sigma> M N) ObjTrue"
  by (rule C_A1_trans
    [OF C_A2_identity_reduces_to_reflexivity[OF identity] reflexive_case])

lemma C_A2_boolean_identity_shape:
  assumes "A \<in> set all_boolean_identities"
  obtains \<sigma> M N where "A = Eq \<sigma> M N"
  using assms
  by (auto simp: all_boolean_identities_def
    bool_comm_conj_def bool_comm_disj_def bool_dist_conj_disj_def
    bool_dist_disj_conj_def bool_dissolve_conj_disj_def
    bool_dissolve_disj_conj_def bool_material_imp_def)

lemma C_A2_boolean_axiom_assuming_reflexive_case:
  assumes axiom: "A \<in> set all_boolean_identities"
    and reflexive_case:
      "\<And>\<sigma> M. \<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow>
        \<Gamma> \<turnstile>\<^sub>C Eq Prop (Eq \<sigma> M M) ObjTrue"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop A ObjTrue"
proof -
  obtain \<sigma> M N where A: "A = Eq \<sigma> M N"
    by (rule C_A2_boolean_identity_shape[OF axiom])
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> M N"
    using C_proves.BooleanIdentity[OF axiom] by (simp add: A)
  have M: "\<Gamma> \<turnstile> M : \<sigma>"
    using C_proves_formula[OF identity] by (auto elim: has_type.cases)
  have "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Eq \<sigma> M N) ObjTrue"
    by (rule C_A2_identity_case_assuming_reflexive_case[OF identity reflexive_case[OF M]])
  then show ?thesis by (simp add: A)
qed

lemma C_A2_classic_axiom_assuming_reflexive_case:
  assumes axiom: "A \<in> set
      [classic_identity_identity \<sigma>, classic_absorb_disj_forall \<sigma>,
       classic_dist_disj_forall \<sigma>, classic_absorb_conj_exists \<sigma>,
       classic_dist_conj_exists \<sigma>]"
    and reflexive_case:
      "\<And>\<tau> M. \<Gamma> \<turnstile> M : \<tau> \<Longrightarrow>
        \<Gamma> \<turnstile>\<^sub>C Eq Prop (Eq \<tau> M M) ObjTrue"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop A ObjTrue"
proof -
  have axiom_theorem: "\<Gamma> \<turnstile>\<^sub>C A"
    using axiom by (auto intro: C_proves.IdentityIdentity C_proves.AbsorbDisjForall
      C_proves.DistDisjForall C_proves.AbsorbConjExists C_proves.DistConjExists)
  obtain \<tau> M N where A: "A = Eq \<tau> M N"
    using axiom by (auto simp: classic_identity_identity_def
      classic_absorb_disj_forall_def classic_dist_disj_forall_def
      classic_absorb_conj_exists_def classic_dist_conj_exists_def)
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> M N"
    using axiom_theorem by (simp add: A)
  have M: "\<Gamma> \<turnstile> M : \<tau>"
    using C_proves_formula[OF identity] by (auto elim: has_type.cases)
  have "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Eq \<tau> M N) ObjTrue"
    by (rule C_A2_identity_case_assuming_reflexive_case[OF identity reflexive_case[OF M]])
  then show ?thesis by (simp add: A)
qed

subsection \<open>Exact remaining constructor obligations\<close>

text \<open>
  The general target remains: ⊢C P entails
  ⊢C (λv̄.P) = (λv̄.⊤₀).
  Locators: Bacon--Dorr A.2, pp.65–67, especially its Gen and Inst
  induction steps; Bacon, Theorem 6.1, printed pp.126–127.

  Isabelle representation.  Gen moves from a derivation of P → Q(x)
  in an extended type context to P → ∀x.Q(x).  Its required induction
  hypothesis abstracts x as well as v̄.  The zero-vector equation in
  the extended context does not supply that stronger hypothesis.
  Inst, with conclusion (∃x.P(x)) → Q, has the dual requirement.

  Status.  General PC, Individual Existence, UI, EG, Ref, LL, β, η,
  and the MP/Gen/Inst induction steps remain to be completed at the
  required vector generality.  Given the Ref-to-truth result, the
  displayed identity-axiom reduction handles the C axiom constructors.
  No unrestricted theorem-to-truth result or C = CE = CEV is asserted.
\<close>

end
