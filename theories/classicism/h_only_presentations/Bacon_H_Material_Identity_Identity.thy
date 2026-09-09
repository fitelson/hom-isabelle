theory Bacon_H_Material_Identity_Identity
  imports Bacon_H_Identity_Local
begin

section \<open>The material Identity Identity is already a theorem of H\<close>

text \<open>
  For a,b:σ, H proves a =σ b ↔ ∀F:σ→t.(Fa ↔ Fb).
  Left to right, LL and symmetry give predicate agreement; Gen quantifies
  the fresh predicate after the identity assumption has been discharged.
  Right to left, UI with F := λx.a =σ x and β reduce the conclusion
  to a =σ a ↔ a =σ b, and Ref supplies its left side.
  Source: the material counterpart of Bacon--Dorr Figure 4 Identity
  Identity, p.13, using only the Figure 2 H rules, p.8.

  Isabelle representation.  H_material_identity_matrix uses Var 0 for F
  and shifts a,b beneath it.  No C, CE, or CEV inference occurs.
  Status.  The conclusion is a material biconditional theorem of H,
  not identity of the two binary operations.  It can supply the H premise
  for an independently defined Logical-Equivalence presentation.
\<close>

definition H_material_identity_matrix :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "H_material_identity_matrix a b =
    (App (Var 0) (shift a) \<longleftrightarrow>\<^sub>o App (Var 0) (shift b))"

lemma H_material_identity_matrix_type:
  assumes a: "\<Gamma> \<turnstile> a : \<sigma>" and b: "\<Gamma> \<turnstile> b : \<sigma>"
  shows "pred_ty \<sigma> # \<Gamma> \<turnstile> H_material_identity_matrix a b : Prop"
proof -
  have sa: "pred_ty \<sigma> # \<Gamma> \<turnstile> shift a : \<sigma>" by (rule weakening_front[OF a])
  have sb: "pred_ty \<sigma> # \<Gamma> \<turnstile> shift b : \<sigma>" by (rule weakening_front[OF b])
  have predicate: "pred_ty \<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have Fa: "pred_ty \<sigma> # \<Gamma> \<turnstile> App (Var 0) (shift a) : Prop"
    by (rule has_type.App[OF predicate sa])
  have Fb: "pred_ty \<sigma> # \<Gamma> \<turnstile> App (Var 0) (shift b) : Prop"
    by (rule has_type.App[OF predicate sb])
  show ?thesis unfolding H_material_identity_matrix_def by (intro has_type.Conj has_type.Imp Fa Fb)
qed

lemma H_material_identity_forward:
  assumes a: "\<Gamma> \<turnstile> a : \<sigma>" and b: "\<Gamma> \<turnstile> b : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp (Eq \<sigma> a b) (Forall (pred_ty \<sigma>) (H_material_identity_matrix a b))"
proof -
  have identity_type: "\<Gamma> \<turnstile> Eq \<sigma> a b : Prop" by (rule has_type.Eq[OF a b])
  have matrix_type: "pred_ty \<sigma> # \<Gamma> \<turnstile> H_material_identity_matrix a b : Prop"
    by (rule H_material_identity_matrix_type[OF a b])
  have sa: "pred_ty \<sigma> # \<Gamma> \<turnstile> shift a : \<sigma>" by (rule weakening_front[OF a])
  have sb: "pred_ty \<sigma> # \<Gamma> \<turnstile> shift b : \<sigma>" by (rule weakening_front[OF b])
  have predicate: "pred_ty \<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have premise: "pred_ty \<sigma> # \<Gamma> \<turnstile>\<^sub>H
    Imp (shift (Eq \<sigma> a b)) (H_material_identity_matrix a b)"
    using H_only_equality_predicate_biconditional[OF sa sb predicate]
    by (simp add: H_material_identity_matrix_def shift_def)
  show ?thesis by (rule H_proves.Gen[OF identity_type matrix_type premise])
qed

lemma H_material_identity_backward:
  assumes a: "\<Gamma> \<turnstile> a : \<sigma>" and b: "\<Gamma> \<turnstile> b : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp (Forall (pred_ty \<sigma>) (H_material_identity_matrix a b)) (Eq \<sigma> a b)"
proof -
  let ?U = "Forall (pred_ty \<sigma>) (H_material_identity_matrix a b)"
  let ?R = "Lam \<sigma> (Eq \<sigma> (shift a) (Var 0))"
  have matrix_type: "pred_ty \<sigma> # \<Gamma> \<turnstile> H_material_identity_matrix a b : Prop"
    by (rule H_material_identity_matrix_type[OF a b])
  have U: "\<Gamma> \<turnstile> ?U : Prop" by (rule has_type.Forall[OF matrix_type])
  have variable: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  have shifted: "\<sigma> # \<Gamma> \<turnstile> shift a : \<sigma>" by (rule weakening_front[OF a])
  have body: "\<sigma> # \<Gamma> \<turnstile> Eq \<sigma> (shift a) (Var 0) : Prop"
    by (rule has_type.Eq[OF shifted variable])
  have R: "\<Gamma> \<turnstile> ?R : \<sigma> \<rightarrow>\<^sub>o Prop" by (rule has_type.Lam[OF body])
  have R_pred: "\<Gamma> \<turnstile> ?R : pred_ty \<sigma>" using R by (simp only: pred_ty_def)
  have Ra: "\<Gamma> \<turnstile> App ?R a : Prop" by (rule has_type.App[OF R a])
  have Rb: "\<Gamma> \<turnstile> App ?R b : Prop" by (rule has_type.App[OF R b])
  have aa: "\<Gamma> \<turnstile> Eq \<sigma> a a : Prop" by (rule has_type.Eq[OF a a])
  have ab: "\<Gamma> \<turnstile> Eq \<sigma> a b : Prop" by (rule has_type.Eq[OF a b])
  have UI: "\<Gamma> \<turnstile>\<^sub>H Imp ?U (App ?R a \<longleftrightarrow>\<^sub>o App ?R b)"
    using H_proves.UI[OF matrix_type R_pred]
    by (simp add: H_material_identity_matrix_def subst0_def)
  have universal: "\<Gamma> ; [?U] \<turnstile>\<^sub>H ?U" by (rule H_derivable.Assumption[OF _ U]) simp
  have predicate_agreement: "\<Gamma> ; [?U] \<turnstile>\<^sub>H (App ?R a \<longleftrightarrow>\<^sub>o App ?R b)"
    by (rule H_only_local_theorem_MP[OF UI universal])
  have beta_a: "\<Gamma> \<turnstile>\<^sub>H (App ?R a \<longleftrightarrow>\<^sub>o Eq \<sigma> a a)"
    using H_only_beta_application[OF body a] by (simp add: subst0_def)
  have beta_b: "\<Gamma> \<turnstile>\<^sub>H (App ?R b \<longleftrightarrow>\<^sub>o Eq \<sigma> a b)"
    using H_only_beta_application[OF body b] by (simp add: subst0_def)
  have reflexivity: "\<Gamma> ; [?U] \<turnstile>\<^sub>H Eq \<sigma> a a"
    by (rule H_derivable.Theorem[OF H_proves.Ref[OF a]])
  have Ra_local: "\<Gamma> ; [?U] \<turnstile>\<^sub>H App ?R a"
    by (rule H_only_local_bicond_right[OF Ra aa H_derivable.Theorem[OF beta_a] reflexivity])
  have Rb_local: "\<Gamma> ; [?U] \<turnstile>\<^sub>H App ?R b"
    by (rule H_only_local_bicond_left[OF Ra Rb predicate_agreement Ra_local])
  have identity: "\<Gamma> ; [?U] \<turnstile>\<^sub>H Eq \<sigma> a b"
    by (rule H_only_local_bicond_left[OF Rb ab H_derivable.Theorem[OF beta_b] Rb_local])
  show ?thesis by (rule H_only_deduction[OF U identity])
qed

theorem H_material_IdentityIdentity:
  assumes a: "\<Gamma> \<turnstile> a : \<sigma>" and b: "\<Gamma> \<turnstile> b : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>H (Eq \<sigma> a b \<longleftrightarrow>\<^sub>o
    Forall (pred_ty \<sigma>) (App (Var 0) (shift a) \<longleftrightarrow>\<^sub>o App (Var 0) (shift b)))"
  using H_conj_intro[OF H_material_identity_forward[OF a b] H_material_identity_backward[OF a b]]
  by (simp only: H_material_identity_matrix_def)

end
