theory Bacon_C_Appendix_A2_Ref
  imports Bacon_C_Appendix_A2_Zeroary
begin

section \<open>Appendix A.2(iv): reflexive identity and the Boolean-operation boundary\<close>

text \<open>
  The Ref case follows the source's chain
  (M =σ M) =ₜ ∀F:σ→t.(FM ↔ FM) =ₜ ∀F:σ→t.⊤₀ =ₜ ⊤₀.
  Locator: Bacon--Dorr Appendix A.2(iv), pp.65–66.

  Isabelle representation.  C_A2_reflexive_body is FM ↔ FM, with F in
  slot zero.  C_A2_reflexive_predicate_identity names the predicate
  identity (λF.FM ↔ FM) = (λF.⊤₀), and pred_ty σ denotes σ → t.

  Status.  Identity Identity and β prove the first equality.  The
  second requires the displayed Boolean predicate identity.  The final
  Ref-to-truth result is conditional on that premise; A.1 supplies its
  final quantified-truth step.  No Equivalence rule is used.
\<close>

definition C_A2_reflexive_body :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_A2_reflexive_body \<sigma> M =
    (App (Var 0) (shift M) \<longleftrightarrow>\<^sub>o App (Var 0) (shift M))"

definition C_A2_reflexive_predicate_identity :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_A2_reflexive_predicate_identity \<sigma> M =
    Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam (pred_ty \<sigma>) (C_A2_reflexive_body \<sigma> M))
      (Lam (pred_ty \<sigma>) (shift ObjTrue))"

lemma C_A2_reflexive_body_type:
  assumes M: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "pred_ty \<sigma> # \<Gamma> \<turnstile> C_A2_reflexive_body \<sigma> M : Prop"
proof -
  have shifted: "pred_ty \<sigma> # \<Gamma> \<turnstile> shift M : \<sigma>"
    by (rule weakening_front[OF M])
  have F: "pred_ty \<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have app: "pred_ty \<sigma> # \<Gamma> \<turnstile> App (Var 0) (shift M) : Prop"
    by (rule has_type.App[OF F shifted])
  show ?thesis unfolding C_A2_reflexive_body_def
    by (intro has_type.Conj has_type.Imp app)
qed

lemma C_A2_reflexive_predicate_identity_type:
  assumes M: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> \<turnstile> C_A2_reflexive_predicate_identity \<sigma> M : Prop"
proof -
  have body: "pred_ty \<sigma> # \<Gamma> \<turnstile> C_A2_reflexive_body \<sigma> M : Prop"
    by (rule C_A2_reflexive_body_type[OF M])
  have truth: "pred_ty \<sigma> # \<Gamma> \<turnstile> shift ObjTrue : Prop"
    by (rule weakening_front[OF typed_ObjTrue])
  show ?thesis unfolding C_A2_reflexive_predicate_identity_def
    by (intro has_type.Eq has_type.Lam body truth)
qed

subsection \<open>Identity Identity followed by two beta contractions\<close>

text \<open>
  ⊢C (M =σ M) =ₜ ∀F:σ→t.(FM ↔ FM).
  Sources: Bacon--Dorr Figure 4, p.13, Identity Identity;
  A.2(iv), pp.65–66.

  Isabelle representation.  The closed identity operation is applied twice
  to M and reduced using C_closure_binary_beta_identity.
  Status.  This first equality is proved without the remaining Boolean premise.
\<close>

lemma C_A2_Ref_unfolded:
  assumes M: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Eq \<sigma> M M)
    (Forall (pred_ty \<sigma>) (C_A2_reflexive_body \<sigma> M))"
proof -
  let ?P = "Eq \<sigma> (Var 1) (Var 0)"
  let ?Q = "Forall (pred_ty \<sigma>)
    (App (Var 0) (Var 2) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))"
  have P: "\<sigma> # \<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "\<sigma> # \<sigma> # \<Gamma> \<turnstile> ?Q : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have source_identity: "\<Gamma> \<turnstile>\<^sub>C
    Eq (\<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Lam \<sigma> ?P)) (Lam \<sigma> (Lam \<sigma> ?Q))"
    using C_proves.IdentityIdentity[of \<Gamma> \<sigma>]
    by (simp add: classic_identity_identity_def identity_ty_def)
  show ?thesis using C_A1_binary_instance[OF P Q M M source_identity]
    by (simp add: C_A2_reflexive_body_def subst0_def shift_def
        numeral_2_eq_2 C_subst_twice_raised C_subst_raised)
qed

subsection \<open>Appendix A.2(iv), conditional completion through A.1\<close>

text \<open>
  Assuming ⊢C (λF.FM ↔ FM) = (λF.⊤₀), derive
  ⊢C (M =σ M) =ₜ ⊤₀.
  Locator: Bacon--Dorr A.2(iv), pp.65–66.

  Isabelle representation.  Predicate congruence moves the premise through
  ∀F; C_Appendix_A1_universal_truth completes the chain.
  Status.  The Boolean predicate identity is still an explicit assumption.
\<close>

lemma C_A2_Ref_assuming_boolean_predicate_identity:
  assumes M: "\<Gamma> \<turnstile> M : \<sigma>"
    and boolean_predicate_identity:
      "\<Gamma> \<turnstile>\<^sub>C C_A2_reflexive_predicate_identity \<sigma> M"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Eq \<sigma> M M) ObjTrue"
proof -
  have body: "pred_ty \<sigma> # \<Gamma> \<turnstile> C_A2_reflexive_body \<sigma> M : Prop"
    by (rule C_A2_reflexive_body_type[OF M])
  have truth: "pred_ty \<sigma> # \<Gamma> \<turnstile> shift ObjTrue : Prop"
    by (rule weakening_front[OF typed_ObjTrue])
  have predicate_identity: "\<Gamma> \<turnstile>\<^sub>C
    Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam (pred_ty \<sigma>) (C_A2_reflexive_body \<sigma> M))
      (Lam (pred_ty \<sigma>) (shift ObjTrue))"
    using boolean_predicate_identity
    by (simp add: C_A2_reflexive_predicate_identity_def)
  have quantified_identity: "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Forall (pred_ty \<sigma>) (C_A2_reflexive_body \<sigma> M))
    (Forall (pred_ty \<sigma>) (shift ObjTrue))"
    by (rule C_forall_of_predicate_identity[OF body truth predicate_identity])
  have to_universal_truth: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Eq \<sigma> M M)
    (Forall (pred_ty \<sigma>) (shift ObjTrue))"
    by (rule C_A1_trans[OF C_A2_Ref_unfolded[OF M] quantified_identity])
  show ?thesis
    by (rule C_A1_trans[OF to_universal_truth C_Appendix_A1_universal_truth])
qed

subsection \<open>The source identity can already be transported under arbitrary vectors\<close>

text \<open>
  The given Identity Identity may replace its operation parameter
  beneath λv̄ in any typed context.
  Sources: Bacon--Dorr Figure 4, p.13; A.2(iv), pp.65–66.

  Isabelle representation.  C_identity_under_abstraction supplies transport
  at arrow_type (rev Δ) τ.
  Status.  This transports the supplied axiom; it does not prove the whole
  vector Ref case of A.2.
\<close>

lemma C_A2_IdentityIdentity_under_abstraction:
  assumes body: "\<Delta> @ (identity_ty \<sigma> # \<Gamma>) \<turnstile> P : \<tau>"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) \<tau>)
    (subst0 (Lam \<sigma> (Lam \<sigma> (Eq \<sigma> (Var 1) (Var 0))))
      (C_abstract_prefix \<Delta> P))
    (subst0 (Lam \<sigma> (Lam \<sigma>
        (Forall (pred_ty \<sigma>)
          (App (Var 0) (Var 2) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)))))
      (C_abstract_prefix \<Delta> P))"
proof -
  let ?F = "Lam \<sigma> (Lam \<sigma> (Eq \<sigma> (Var 1) (Var 0)))"
  let ?G = "Lam \<sigma> (Lam \<sigma> (Forall (pred_ty \<sigma>)
    (App (Var 0) (Var 2) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))))"
  have F: "\<Gamma> \<turnstile> ?F : identity_ty \<sigma>"
    by (rule infer_type_sound) (simp add: identity_ty_def lookup_def)
  have G: "\<Gamma> \<turnstile> ?G : identity_ty \<sigma>"
    by (rule infer_type_sound) (simp add: identity_ty_def pred_ty_def lookup_def)
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq (identity_ty \<sigma>) ?F ?G"
    using C_proves.IdentityIdentity[of \<Gamma> \<sigma>]
    by (simp add: classic_identity_identity_def)
  show ?thesis by (rule C_identity_under_abstraction[OF F G body identity])
qed

text \<open>
  The remaining equation is ⊢C (λF.FM ↔ FM) = (λF.⊤₀).
  Locator: Bacon--Dorr A.2(iv), pp.65–66.

  Isabelle representation.  Its precise formula is
  C_A2_reflexive_predicate_identity σ M.  A uniform Boolean
  normalization proof beneath abstraction would supply it.

  Status.  The weaker theorem ⊢C FM ↔ FM does not supply predicate
  identity.  The final vector transport result above concerns the
  given Identity Identity, not the full Ref-to-truth result beneath
  λv̄.  That stronger result still requires the Boolean predicate
  step and the quantified-truth step beneath the entire vector.
\<close>

end
