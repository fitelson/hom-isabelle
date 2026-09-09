theory Bacon_HLE_Identity_Identity
  imports Bacon_H_Equivalence_Syntax_Bridge Bacon_H_Material_Identity_Identity
begin

section \<open>Deriving the Identity Identity by Logical Equivalence\<close>

text \<open>
  H proves y =σ z ↔ ∀F:σ→t.(Fy ↔ Fz). Logical Equivalence therefore
  gives (λyz.y =σ z) = (λyz.∀F.(Fy ↔ Fz)).
  Source: Bacon Table 6.5 and Theorem 6.1, pp.125–127;
  Bacon–Dorr Figure 4, p.13.

  Isabelle representation: Δ = [σ,σ] puts y at slot 1 and z at slot 0.
  The quantified predicate occupies a further slot, shifting y,z to 2,1.
  The eligibility proof uses H only. The operation identity is a derived
  HLE theorem, not an axiom imported from C.
\<close>

theorem HLE_IdentityIdentity:
  "HLE_proves \<Gamma> (classic_identity_identity \<sigma>)"
proof -
  let ?\<Delta> = "[\<sigma>, \<sigma>]"
  let ?A = "Eq \<sigma> (Var 1) (Var 0)"
  let ?B = "Forall (pred_ty \<sigma>)
    (App (Var 0) (Var 2) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))"
  have y: "?\<Delta> @ \<Gamma> \<turnstile> Var 1 : \<sigma>" by (rule has_type.Var) simp
  have z: "?\<Delta> @ \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  have A: "?\<Delta> @ \<Gamma> \<turnstile> ?A : Prop" by (rule has_type.Eq[OF y z])
  have B: "?\<Delta> @ \<Gamma> \<turnstile> ?B : Prop"
    by (rule infer_type_sound) (simp add: pred_ty_def lookup_def)
  have material: "?\<Delta> @ \<Gamma> \<turnstile>\<^sub>H (?A \<longleftrightarrow>\<^sub>o ?B)"
    using H_material_IdentityIdentity[OF y z] by (simp add: shift_def numeral_2_eq_2)
  show ?thesis using HLE_abstraction[OF A B material]
    by (simp add: classic_identity_identity_def identity_ty_def C_abstract_prefix_def)
qed

end
